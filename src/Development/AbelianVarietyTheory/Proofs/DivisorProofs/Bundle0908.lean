module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeG
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.SchANonzero

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

def intPts (F : Type) [Field F] [NumberField F] (κ : Type) : Set (κ → FiniteAdeleRing (𝓞 F) F) :=
  Set.pi Set.univ fun _ => {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F}

theorem isOpen_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsOpen (intPts F κ) :=
  isOpen_set_pi Set.finite_univ fun _ _ =>
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (fun v => Valued.isOpen_valuationSubring _)

theorem isCompact_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsCompact (intPts F κ) :=
  isCompact_univ_pi fun _ => GlobalTheory.AdeleCocompact.isCompact_integral F

theorem isClosed_intPts (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] : IsClosed (intPts F κ) := by
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite))
  exact (isCompact_intPts F κ).isClosed

theorem indicator_intPts_mem_SB (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (intPts F κ).indicator (1 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_intPts F κ) (isClosed_intPts F κ)
    fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ intPts F κ
  · exact ⟨intPts F κ, isOpen_intPts F κ, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]; rfl⟩
  · exact ⟨(intPts F κ)ᶜ, (isClosed_intPts F κ).isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

theorem exists_mem_schA_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ φ ∈ schA F κ, φ 0 ≠ 0 := by
  intro F _ _ κ _
  classical
  obtain ⟨f, hf⟩ := exists_schwartz_one (κ → mixedEmbedding.mixedSpace F)
  refine ⟨pureA F f ((intPts F κ).indicator 1), Submodule.subset_span ⟨f, _, indicator_intPts_mem_SB F κ, rfl⟩, ?_⟩
  have h0 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ intPts F κ := fun i _ v => by
    show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem (v.adicCompletionIntegers F)
  simp only [pureA]
  rw [Set.indicator_of_mem h0]
  have hz : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _
  rw [hz, hf]
  simp

end GlobalTheory.SchANonzero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineNbhdLieMatrixSmoothCommGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_lie_matrix_smooth_comm_group : ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], Smooth A.hom →
  ∀ (act : ReciprocityTheory.ChartRestriction.G.Geo.Tor.OAct O A) (z : S),
    ∃ (U : S.Opens) (hU : IsAffineOpen U), z ∈ U ∧ ∃ (n : ℕ) (M : O →+* Matrix (Fin n) (Fin n) Γ(S, U)),
      ∀ (R' : Type) [CommRing R'] (f : Γ(S, U) →+* R'),
        ∃ e : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A ≃ₗ[R'] (Fin n → R'),
          ∀ (c : O) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (spMap f ≫ hU.fromSpec) A),
            e (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := spMap f ≫ hU.fromSpec) (S := R') act c v) = matAct M f c (e v) := by
  first | (exact @GlobalTheory.exists_affine_lieMatrix) | (exact GlobalTheory.exists_affine_lieMatrix) | (intros; apply GlobalTheory.exists_affine_lieMatrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAsAlgebraHomEq
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ExtTensorSub

variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (X : Representation ℂ G V) (T : Representation ℂ H W)

def up (U : Subrepresentation X) : Subrepresentation (extTensor X T) where
  toSubmodule := LinearMap.range (U.toSubmodule.subtype.rTensor W)
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u w =>
      refine ⟨⟨X g.1 u, U.apply_mem_toSubmodule g.1 u.2⟩ ⊗ₜ T g.2 w, ?_⟩
      simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hy

def down (S : Subrepresentation (extTensor X T)) : Subrepresentation X where
  toSubmodule :=
    { carrier := {v | ∀ w : W, v ⊗ₜ[ℂ] w ∈ S.toSubmodule}
      add_mem' := fun ha hb w => by rw [TensorProduct.add_tmul]; exact add_mem (ha w) (hb w)
      zero_mem' := fun w => by rw [TensorProduct.zero_tmul]; exact zero_mem _
      smul_mem' := fun c v hv w => by
        rw [← TensorProduct.smul_tmul']; exact S.toSubmodule.smul_mem c (hv w) }
  apply_mem_toSubmodule g v hv w := by
    have := S.apply_mem_toSubmodule (g, 1) (hv w)
    simpa using this

theorem exists_asAlgebraHom_eq {T : Representation ℂ H W} (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (A : Module.End ℂ W) (s : Finset W) :
    ∃ r : MonoidAlgebra ℂ H, ∀ v ∈ s, T.asAlgebraHom r v = A v := by
  classical
  set R := MonoidAlgebra ℂ H
  have hsimple : IsSimpleModule R T.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule T).1 hirr
  set E := T.asModuleEquiv
  have hsc : ∀ φ : Module.End R T.asModule, ∃ c : ℂ, ∀ x, E (φ x) = c • E x := by
    intro φ
    let B : Module.End ℂ W :=
      { toFun := fun v => E (φ (E.symm v))
        map_add' := fun a b => by simp
        map_smul' := fun c v => by
          rw [RingHom.id_apply, Representation.asModuleEquiv_symm_map_smul, map_smul,
            Representation.asModuleEquiv_map_smul, AlgHom.commutes,
            Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply] }
    obtain ⟨c, hc⟩ := hschur B fun m => by
      ext v
      simp only [Module.End.mul_apply, B, LinearMap.coe_mk, AddHom.coe_mk]
      rw [Representation.asModuleEquiv_symm_map_rho, map_smul,
        Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single_one]
    refine ⟨c, fun x => ?_⟩
    have := congrArg (fun F : Module.End ℂ W => F (E x)) hc
    simpa [B] using this
  let f : Module.End (Module.End R T.asModule) T.asModule :=
    { toFun := fun x => E.symm (A (E x))
      map_add' := fun a b => by simp
      map_smul' := fun φ x => by
        obtain ⟨c, hc⟩ := hsc φ
        show E.symm (A (E (φ x))) = φ (E.symm (A (E x)))
        apply E.injective
        rw [hc, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density f (s.image E.symm)
  refine ⟨r, fun v hv => ?_⟩
  have := hr (E.symm v) (Finset.mem_image_of_mem _ hv)
  have h2 := congrArg E this
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply] at h2
  rw [h2, Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]

theorem map_mem (S : Subrepresentation (extTensor X T)) (r : MonoidAlgebra ℂ H) {z : V ⊗[ℂ] W}
    (hz : z ∈ S.toSubmodule) : TensorProduct.map LinearMap.id (T.asAlgebraHom r) z ∈ S.toSubmodule := by
  induction r using MonoidAlgebra.induction_on with
  | of m =>
    have h1 : extTensor X T (1, m) = TensorProduct.map LinearMap.id (T m) :=
      TensorProduct.ext' fun v w => by simp
    rw [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one, ← h1]
    exact S.apply_mem_toSubmodule _ hz
  | add f g hf hg =>
    rw [map_add (f := _), TensorProduct.map_add_right, LinearMap.add_apply]
    exact S.toSubmodule.add_mem hf hg
  | smul c f hf =>
    rw [map_smul, TensorProduct.map_smul_right, LinearMap.smul_apply]
    exact S.toSubmodule.smul_mem c hf

theorem up_down (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1)
    (S : Subrepresentation (extTensor X T)) : up X T (down X T S) = S := by
  classical
  apply Subrepresentation.toSubmodule_injective
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul u w => simpa using u.2 w
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  · intro y hy
    let b := Module.Basis.ofVectorSpace ℂ W
    let F := TensorProduct.equivFinsuppOfBasisRight (M := V) b
    have hy' : y = (F y).sum fun j a => a ⊗ₜ[ℂ] b j := by
      conv_lhs => rw [← F.symm_apply_apply y]
      exact TensorProduct.equivFinsuppOfBasisRight_symm_apply b (F y)
    have hmem : ∀ j₀, F y j₀ ∈ (down X T S).toSubmodule := by
      intro j₀ w
      by_cases hj₀ : F y j₀ = 0
      · rw [hj₀, TensorProduct.zero_tmul]; exact zero_mem _
      let A : Module.End ℂ W := b.constr ℂ fun j => if j = j₀ then w else 0
      obtain ⟨r, hr⟩ := exists_asAlgebraHom_eq hirr hschur A ((F y).support.image b)
      have := map_mem X T S r hy
      rw [hy', map_finsuppSum] at this
      convert this using 1
      rw [Finsupp.sum, Finset.sum_eq_single j₀]
      · rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _
          (Finsupp.mem_support_iff.2 hj₀))]
        simp [A]
      · intro j hj hjj
        rw [TensorProduct.map_tmul, LinearMap.id_apply, hr _ (Finset.mem_image_of_mem _ hj)]
        simp [A, hjj]
      · intro h
        exact absurd (Finsupp.mem_support_iff.2 hj₀) h
    rw [hy', Finsupp.sum]
    exact Submodule.sum_mem _ fun j _ => ⟨⟨F y j, hmem j⟩ ⊗ₜ b j, by simp⟩

theorem down_up [Nontrivial W] (U : Subrepresentation X) : down X T (up X T U) = U := by
  apply Subrepresentation.toSubmodule_injective
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ W, φ w ≠ 0 := by
      by_contra! h
      exact hw ((Module.forall_dual_apply_eq_zero_iff ℂ w).1 h)
    let f : V ⊗[ℂ] W →ₗ[ℂ] V := (TensorProduct.rid ℂ V).toLinearMap ∘ₗ LinearMap.lTensor V φ
    have key : ∀ x, f (U.toSubmodule.subtype.rTensor W x) ∈ U.toSubmodule := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | tmul u w' => simpa [f] using U.toSubmodule.smul_mem (φ w') u.2
      | add x y hx hy =>
        simp only [map_add]
        exact add_mem hx hy
    obtain ⟨x, hx⟩ := hv w
    have h2 := key x
    rw [hx] at h2
    simp only [f, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul] at h2
    exact (U.toSubmodule.smul_mem_iff hφ).1 h2
  · intro hv w
    exact ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩

def orderIso (hirr : T.IsIrreducible)
    (hschur : ∀ A : Module.End ℂ W, (∀ m, A * T m = T m * A) → ∃ c : ℂ, A = c • 1) :
    Subrepresentation X ≃o Subrepresentation (extTensor X T) :=
  haveI := Model.nontrivial_of_isIrreducible hirr
  { toFun := up X T
    invFun := down X T
    left_inv := down_up X T
    right_inv := up_down X T hirr hschur
    map_rel_iff' := by
      intro U U'
      constructor
      · intro h v hv
        have h1 : v ∈ (down X T (up X T U')).toSubmodule := fun w => h ⟨⟨v, hv⟩ ⊗ₜ w, by simp⟩
        rwa [down_up X T U'] at h1
      · intro h
        rintro _ ⟨x, rfl⟩
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero]; exact zero_mem (up X T U').toSubmodule
        | tmul u w => exact ⟨⟨u, h u.2⟩ ⊗ₜ w, by simp⟩
        | add x y hx hy => rw [map_add (f := _)]; exact (up X T U').toSubmodule.add_mem hx hy }

end GlobalTheory.ExtTensorSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharsOfTameLpDim
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TameInertiaChars

theorem exists_basis_eigen {n : ℕ} {Γ : Type} (f : Γ → Module.End ℂ (Fin n → ℂ))
    (hs : ∀ g, (f g).IsSemisimple) (hc : ∀ g k, Commute (f g) (f k)) :
    ∃ B : Module.Basis (Fin n) ℂ (Fin n → ℂ), ∀ j g, ∃ c : ℂ, f g (B j) = c • B j := by
  have h1 := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun g k _ => hc g k) fun g => Module.End.iSup_maxGenEigenspace_eq_top _
  simp only [fun g => (hs g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at h1
  let T : Set (Fin n → ℂ) := {v | ∀ g, ∃ c : ℂ, f g v = c • v}
  have h2 : ⊤ ≤ Submodule.span ℂ T := by
    rw [← h1]
    exact iSup_le fun χ v hv => Submodule.subset_span fun g =>
      ⟨χ g, Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv g)⟩
  let B := Module.Basis.ofSpan h2
  have h3 := Module.Basis.ofSpan_subset h2
  refine ⟨B.reindex (B.indexEquiv (Pi.basisFun ℂ (Fin n))), fun j => ?_⟩
  rw [Module.Basis.reindex_apply]
  exact h3 ⟨_, rfl⟩

theorem charpoly_of_basis {n : ℕ} (f : Module.End ℂ (Fin n → ℂ)) (B : Module.Basis (Fin n) ℂ (Fin n → ℂ))
    (c : Fin n → ℂ) (hB : ∀ j, f (B j) = c j • B j) : f.charpoly = ∏ j, (X - C (c j)) := by
  rw [← LinearMap.charpoly_toMatrix f B, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hB, map_smul, B.repr_self, Matrix.diagonal_apply]
  by_cases e : i = j
  · subst e; simp
  · simp [Finsupp.single_apply, Ne.symm e, e]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

end GlobalTheory.TameInertiaChars

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonDenominatorConjLocalCoordsLattice
section
open NumberField IsDedekindDomain
open scoped Matrix

namespace GlobalTheory.ConjCoordDenom

theorem exists_common_denom_conj_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), (∀ x, w.valuation E (σ x) = w.valuation E x) →
    (∀ a : E, w.valuation E a ≤ 1 → ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * a = r) →
    ∀ (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → ∀ (X : Matrix (Fin n) (Fin n) E),
    (∀ x ∈ L, ∀ i, w.valuation E ((X⁻¹ *ᵥ x) i) ≤ 1) →
    ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∀ x ∈ L, ∀ i, ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ x) i) = r := by
  intro F E _ _ _ _ _ σ w hσ hden n L hL X hX
  obtain ⟨S, hS⟩ := hL
  have key : ∀ g ∈ S, ∀ i, ∃ s : 𝓞 E, s ∉ w.asIdeal ∧ ∃ r : 𝓞 E, (s : E) * σ ((X⁻¹ *ᵥ g) i) = r := by
    intro g hg i
    apply hden
    rw [hσ]
    exact hX g (hS ▸ Submodule.subset_span hg) i
  choose! d hd r hr using key
  haveI := w.isPrime
  refine ⟨∏ g ∈ S, ∏ i, d g i, ?_, ?_⟩
  · intro hmem
    obtain ⟨g, hg, hmem⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    obtain ⟨i, -, hmem⟩ := (Ideal.IsPrime.prod_mem_iff).1 hmem
    exact hd g hg i hmem
  · intro x hx
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      intro i
      obtain ⟨t, ht⟩ : d g i ∣ ∏ g ∈ S, ∏ i, d g i :=
        (Finset.dvd_prod_of_mem (fun i => d g i) (Finset.mem_univ i)).trans
          (Finset.dvd_prod_of_mem (fun g => ∏ i, d g i) hg)
      refine ⟨t * r g i, ?_⟩
      rw [ht]
      push_cast
      rw [mul_comm (d g i : E), mul_assoc, hr g hg i]
    | zero => intro i; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      obtain ⟨b, hb⟩ := hy i
      refine ⟨a + b, ?_⟩
      rw [Matrix.mulVec_add, Pi.add_apply, map_add (f := _), mul_add, ha, hb]
      push_cast
      rfl
    | smul c x _ hx =>
      intro i
      obtain ⟨a, ha⟩ := hx i
      refine ⟨NumberField.RingOfIntegers.mapRingHom σ.toRingHom c * a, ?_⟩
      have hc : c • x = (c : E) • x := (algebraMap_smul E c x).symm
      rw [hc, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm, ha]
      push_cast
      rfl

end GlobalTheory.ConjCoordDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonEigenvectorRhoAdjoinRootEmbedding
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem rho_jM_common_eigvec : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (i : Fin G.m)
    (τ : FM P →+* PadicAlgCl p), τ.comp (algebraMap G.F (FM P)) = G.emb i →
    ∃ v : Fin G.n → PadicAlgCl p, v ≠ 0 ∧
      ∀ a : FM P, (G.rho i (jM P a)).map (fun x => (x : PadicAlgCl p)) *ᵥ v = τ a • v := by
  intro p _ G P i τ hτ
  let f : G.Fw i →+* PadicAlgCl p := algebraMap (G.Fw i) (PadicAlgCl p)
  have hf : (fun x : G.Fw i => (x : PadicAlgCl p)) = ⇑f := rfl
  have hfe : f.comp (G.embW i) = G.emb i := by
    ext x; rfl
  let ψ : G.C →+* Matrix (Fin G.n) (Fin G.n) (PadicAlgCl p) := f.mapMatrix.comp (G.rho i)
  have hψ : ∀ x, ψ x = (G.rho i x).map (fun x => (x : PadicAlgCl p)) := fun x => rfl
  set M := ψ (P.γ : G.C) with hM
  set lam := τ (AdjoinRoot.root P.pol) with hlam
  have hchar : M.charpoly = P.pol.map (G.emb i) := by
    rw [hM, hψ, hf, Matrix.charpoly_map, charpoly_rho_eq_map_pol, Polynomial.map_map, hfe]
  have heval : Polynomial.eval lam M.charpoly = 0 := by
    rw [hchar, Polynomial.eval_map, ← hτ, ← Polynomial.hom_eval₂, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.eval₂_root, map_zero]
  rw [Matrix.eval_charpoly] at heval
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 heval
  have hMv : M *ᵥ v = lam • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext j
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  refine ⟨v, hv0, fun a => ?_⟩
  rw [← hψ]
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [jM_mk]
  have key : ∀ g : Polynomial G.F, ψ (Polynomial.aeval (P.γ : G.C) g) *ᵥ v =
      τ (AdjoinRoot.mk P.pol g) • v := by
    intro g
    induction g using Polynomial.induction_on with
    | C c =>
      rw [Polynomial.aeval_C, AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, ← RingHom.comp_apply τ, hτ]
      show (f.mapMatrix (G.rho i (algebraMap G.F G.C c))) *ᵥ v = _
      rw [G.rho_F]
      ext j
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal, RingHom.mapMatrix_apply, Matrix.diagonal_map]
      exact Or.inl rfl
    | add g h hg hh =>
      rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, hg, hh, map_add (f := _), map_add (f := _), add_smul]
    | monomial k c hk =>
      rw [pow_succ, ← mul_assoc, map_mul, map_mul, ← Matrix.mulVec_mulVec, Polynomial.aeval_X, ← hM, hMv,
        Matrix.mulVec_smul, hk, smul_smul]
      congr 1
      rw [map_mul (AdjoinRoot.mk P.pol) _ Polynomial.X, map_mul τ, AdjoinRoot.mk_X, mul_comm]
  exact key g

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPosDenominatorOfIsCompactFiniteAdeleStatement
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pos_denominator_of_isCompact_finiteAdeleAway : ∀ (p : ℕ) (S : Set (AfP p)), IsCompact S → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ S, (D : AfP p) * a ∈ LevelExists.intAfP p := by
  first | (exact @GlobalTheory.AfPCpctDen.main) | (exact GlobalTheory.AfPCpctDen.main) | (intros; apply GlobalTheory.AfPCpctDen.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjCentralizerLeBlockDiagonalLeviStatement
section
open MeasureTheory Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_centralizer_le_blockDiagonalLevi : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (γ : GL ι K),
  (γ : Matrix ι ι K).charpoly.Separable → ¬ Irreducible (γ : Matrix ι ι K).charpoly →
  ∃ (a b : ℕ) (e : ι ≃ Fin a ⊕ Fin b), 0 < a ∧ 0 < b ∧ ∃ c : GL ι K,
    GlobalTheory.BCT.twCent (MonoidHom.id (GL ι K)) (c⁻¹ * γ * c) ≤ GlobalTheory.OrbDesc.blockLevi e := by
  first | (exact @GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi) | (exact GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi) | (intros; apply GlobalTheory.OrbDesc.exists_conj_cent_le_blockLevi  <;> assumption)
end

