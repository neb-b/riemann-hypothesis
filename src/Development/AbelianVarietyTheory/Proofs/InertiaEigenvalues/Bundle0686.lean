module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.BlockTriangularOfSubOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableSeedOfAcrisPeriods
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0586
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddCharConductorMaxIdeal
section
open ValuativeRel

noncomputable section

namespace GlobalTheory.DZero.PsiM

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valueGroupIso_uniformizer :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k (uniformizer k) = WithZero.exp (-1) := by
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h0 : φ (uniformizer k) ≠ 0 := by simp
  apply le_antisymm
  · have : φ (uniformizer k) < φ 1 := φ.strictMono uniformizer_lt_one
    rw [map_one, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega
  · have : φ.symm (WithZero.exp (-1)) ≤ uniformizer k := by
      rw [le_uniformizer_iff, ← map_one φ.symm]
      exact φ.symm.strictMono (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    simpa using φ.strictMono.monotone this

variable {k}

theorem ord_eq_one {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) : SmGL.ord k ϖ = 1 := by
  rw [SmGL.ord, hϖ, valueGroupIso_uniformizer, WithZero.log_exp]; rfl

end GlobalTheory.DZero.PsiM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistableBoundedJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def incl (d : ℕ) : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] (Fin d → ℚ_[l]) :=
  (Algebra.linearMap ℤ_[l] ℚ_[l]).compLeft (Fin d)

theorem incl_apply (d : ℕ) (v : Fin d → ℤ_[l]) : incl d v = fun i => algebraMap ℤ_[l] ℚ_[l] (v i) := rfl

theorem incl_injective (d : ℕ) : Function.Injective (incl (l := l) d) := by
  intro v w h
  funext i
  have := congrFun h i
  simp only [incl_apply] at this
  exact (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l]) this

theorem qRep_incl {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) (v : Fin d → ℤ_[l]) :
    qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v) := by
  funext i
  change (((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) *ᵥ (fun j => algebraMap ℤ_[l] ℚ_[l] (v j))) i = algebraMap ℤ_[l] ℚ_[l] (((ρ g).val *ᵥ v) i)
  rw [RingHom.map_mulVec]
  rfl

end GlobalTheory.BKLim.StdLat

namespace GlobalTheory.BKLim.StdLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def lat {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Formalism.WeaklyAdmissibleFiltrations.Lattice (LL := ℚ_[l]) (O := ℤ_[l]) (V := Fin d → ℚ_[l]) (qRep ρ) where
  T := LinearMap.range (incl d)
  stable g x hx := by
    obtain ⟨v, rfl⟩ := hx
    exact ⟨_, (qRep_incl ρ g v).symm⟩
  fg := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  free := Module.Free.of_equiv (LinearEquiv.ofInjective (incl d) (incl_injective d))
  span := by
    rw [eq_top_iff, ← (Pi.basisFun ℚ_[l] (Fin d)).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨Pi.single j 1, ?_⟩
    funext i
    simp [incl_apply, Pi.single_apply]

noncomputable def equiv {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    (Fin d → ℤ_[l]) ≃ₗ[ℤ_[l]] ↥(lat ρ).T :=
  LinearEquiv.ofInjective (incl d) (incl_injective d)

theorem equiv_apply {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (v : Fin d → ℤ_[l]) :
    ((equiv ρ v : ↥(lat ρ).T) : Fin d → ℚ_[l]) = incl d v := rfl

noncomputable def basis {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) :
    Module.Basis (Fin d) ℤ_[l] ↥(lat ρ).T :=
  (Pi.basisFun ℤ_[l] (Fin d)).map (equiv ρ)

theorem toMatrix_act {Γ : Type} [Group Γ] {d : ℕ} (ρ : Γ →* GL (Fin d) ℤ_[l]) (g : Γ) :
    LinearMap.toMatrix (basis ρ) (basis ρ) (actT (lat ρ) g) = (ρ g).val := by
  have key : ∀ v, (equiv ρ).symm (actT (lat ρ) g (equiv ρ v)) = (ρ g).val *ᵥ v := by
    intro v
    apply (equiv ρ).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [equiv_apply]
    change qRep ρ g (incl d v) = incl d ((ρ g).val *ᵥ v)
    exact qRep_incl ρ g v
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [basis, Module.Basis.map_apply, Module.Basis.map_repr, LinearEquiv.trans_apply, key,
    Pi.basisFun_apply, Pi.basisFun_repr]
  simp [Matrix.mulVec_single]

theorem cont_act {d : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] (ρ : Γ →* GL (Fin d) ℤ_[l]) (hρ : Continuous ρ)
    (x : Fin d → ℚ_[l]) : Continuous fun g => qRep ρ g x := by
  have h1 : Continuous fun g => ((ρ g).val : Matrix (Fin d) (Fin d) ℤ_[l]) := Units.continuous_val.comp hρ
  have h2 : Continuous fun g => ((ρ g).val.map (algebraMap ℤ_[l] ℚ_[l])) :=
    h1.matrix_map (continuous_subtype_val)
  exact h2.matrix_mulVec continuous_const

end GlobalTheory.BKLim.StdLat

theorem GlobalTheory.BKLim.crys_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsCrys (P.PD K) (qRep ρ) → Nonempty (Seed bk d (fun g => (ρ g).val) τ) := by
  intro l _ K bk τ hτ P AI T d ρ hρc hc
  have h := GlobalTheory.SeedExists.exists_seed l K bk τ hτ P AI ⟨T⟩ (Fin d → ℚ_[l]) (qRep ρ) (GlobalTheory.BKLim.StdLat.lat ρ)
    (GlobalTheory.BKLim.StdLat.cont_act ρ hρc) hc d (GlobalTheory.BKLim.StdLat.basis ρ)
  simp only [GlobalTheory.BKLim.StdLat.toMatrix_act] at h
  exact h

theorem GlobalTheory.BKLim.exists_frame_sst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Continuous ρ → IsSst P (qRep ρ) → (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∃ F : Frame bk N d fun g => (ρ g).val, F.IsDR ∧ (IsCrys (P.PD K) (qRep ρ) → F.IsCr) := by
  intro l _ K bk τ hτ P AI T N d ρ hρc hsst hjump
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have hinv := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  have hdr : IsDR (P.PD K) (qRep ρ) := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  have hHN := hH N hjump
  have hunit : ∀ g, IsUnit ((ρ g).val) := fun g => (ρ g).isUnit
  obtain ⟨s, hs⟩ : ∃ s : WSeed bk d (fun g => (ρ g).val) τ, IsCrys (P.PD K) (qRep ρ) → ∀ g, s.κ g = 1 := by
    by_cases hc : IsCrys (P.PD K) (qRep ρ)
    · obtain ⟨sd⟩ := GlobalTheory.BKLim.crys_seed l K bk τ hτ P AI T d ρ hρc hc
      obtain ⟨s', hs'⟩ := _root_.GlobalTheory.BKLim.wseed_of_seed l K bk τ hτ d _ sd
      exact ⟨s', fun _ => hs'⟩
    · obtain ⟨N', c₁, c₂, c₃, k₀, F, F', X, X', Z, Z', κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        GlobalTheory.T.exists_semistable_lattice_periods_acris l K bk P AI T C hC d ρ hsst
      obtain ⟨s⟩ := _root_.GlobalTheory.BKLim.wseed_of_periods l K bk C τ hτ d (fun g => (ρ g).val) N' c₁ c₂ c₃ k₀ F F' X X' Z Z' κ
        ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨s, fun h => absurd h hc⟩
  obtain ⟨N', F, hFdr, hFcr⟩ := GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods l K bk τ hτ d _ hunit s
  obtain ⟨F₀, -, hε⟩ := GlobalTheory.T.exists_breuilKisin_frame_height_of_jumps_le l K bk τ hτ C hinv.2 N' N d _ F hFdr H hHN
  refine ⟨F₀, ?_, fun hc => ?_⟩
  · unfold Frame.IsDR Frame.IsBeta at hFdr ⊢
    rw [hε]; exact hFdr
  · have := hFcr (hs hc)
    unfold Frame.IsCr at this ⊢
    rw [hε]; exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetDoubleCosetsConjMaxCompact
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ClassFinConj

theorem exists_finset_double_cosets_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (h : GAf L n),
    ∃ T : Finset (GAf L n), ∀ g : GAf L n, ∃ γ ∈ GQ L n, ∃ t ∈ T,
      ∃ κ ∈ (Umax L n ⊓ (Umax L n).map (MulAut.conj h).toMonoidHom), g = γ * t * κ := by
  intro L _ _ _ n h
  classical
  obtain ⟨T, hT⟩ := GlobalTheory.DefiniteClassFinite.exists_finset_double_cosets_Umax L n
  obtain ⟨N', hN', hc⟩ := GlobalTheory.CongConjugate.congConj L n h 1 one_pos
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN'
  refine ⟨(T ×ˢ J).image (fun p => p.1 * p.2), fun g => ?_⟩
  obtain ⟨γ, t, u, ht, hu, e⟩ := hT g
  obtain ⟨j, hj, κ, hκ, eu⟩ := hJ u hu
  refine ⟨(γ : GAf L n), γ.2, t * j, Finset.mem_image.2 ⟨(t, j), Finset.mem_product.2 ⟨ht, hj⟩, rfl⟩, κ,
    Subgroup.mem_inf.2 ⟨hκ.1, Subgroup.mem_map.2 ⟨h⁻¹ * κ * h, (hc κ hκ).1, ?_⟩⟩, ?_⟩
  · simp [MulAut.conj_apply, mul_assoc]
  · rw [e, eu]; simp only [mul_assoc]

end GlobalTheory.ClassFinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantVectorExactFiltrationDegreeBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.exists_letter_vector_exact_degree : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (x : P.R.B), IsUnit x → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ, (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) → ∀ (μ : ↥(GK K) →* (↥LL.1)ˣ) (τ₀' τ' : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) (j : ℕ), (∀ g : ↥(GK K), ((μ g : (↥LL.1)ˣ) : ↥LL.1) * τ₀' ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) = 1) → (∀ a : ↥(K0 K), τ' ((⇑(P.PD K).σ)^[j] a) = τ₀' a) → ∀ d : ℤ, P.ιB ((⇑P.φB)^[j] x) ∈ (P.PD K).Fil d → P.ιB ((⇑P.φB)^[j] x) ∉ (P.PD K).Fil (d + 1) → ∃ w ∈ DcrisL (P.PD K) (charRep μ) τ', ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) d ∧ ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w ∉ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1) := by
  intro l _ P AI hT K LL x hx c hc μ τ₀' τ' j hμ hτ d hd hd1
  have := (P.PD K).finK₀
  obtain ⟨m, cc, kk, h1, hsum⟩ := GlobalTheory.exists_embedding_idempotent_tensor ℚ_[l] ↥(K0 K) ↥LL.1 τ'
  set y := (⇑P.φB)^[j] x with hy
  set z := P.ιB y with hzdef
  clear_value z y
  let f : ↥(K0 K) →ₗ[ℚ_[l]] P.R.B := (LinearMap.mulRight ℚ_[l] y) ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hB : ∀ s : ↥(K0 K), ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) = ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by
    intro s
    have := congrArg (LinearMap.lTensor ↥LL.1 f) (hsum s)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [f, map_sum, LinearMap.lTensor_tmul] using this
  have hφK : ∀ k : ↥(K0 K), P.φB (algebraMap ↥(K0 K) P.R.B k) = algebraMap ↥(K0 K) P.R.B ((P.PD K).σ k) := by
    intro k; rw [← P.PD_φ K]; exact (P.PD K).φ_K₀ k
  have hact : ∀ g : ↥(GK K), ∀ n : ℕ, P.actQ (g : GQ l) ((⇑P.φB)^[n] x) = algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[n] (c g : ↥(K0 K))) * (⇑P.φB)^[n] x := by
    intro g n
    have hcomm : ∀ b, P.actQ (g : GQ l) (P.φB b) = P.φB (P.actQ (g : GQ l) b) := by
      intro b
      have := (P.PD K).φ_comm g b
      rw [P.PD_φ, P.PD_φ, P.PD_actB, P.PD_actB] at this
      exact this.symm
    induction n with
    | zero => simpa using hc g
    | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [hcomm, ih, map_mul, hφK]
  have hterm : ∀ (g : ↥(GK K)) (a : ↥LL.1) (k : ↥(K0 K)),
      actVB (P.PD K) (charRep μ) g (a ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B k * y)) =
        (((μ g : (↥LL.1)ˣ) : ↥LL.1) * a) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B ((⇑(P.PD K).σ)^[j] (c g : ↥(K0 K)) * k) * y) := by
    intro g a k
    simp only [actVB, AlgebraTensorModule.map_tmul]
    congr 1
    change (P.PD K).actB g (algebraMap ↥(K0 K) P.R.B k * y) = _
    rw [map_mul, AlgEquiv.commutes, P.PD_actB, hy, hact g j, map_mul]
    ring
  obtain ⟨w, hw⟩ : ∃ w : ↥LL.1 ⊗[ℚ_[l]] P.R.B, w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := ⟨_, rfl⟩
  have hinv : ∀ g : ↥(GK K), actVB (P.PD K) (charRep μ) g w = w := by
    intro g
    set s := (⇑(P.PD K).σ)^[j] (c g : ↥(K0 K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, hterm]
    calc ∑ i, (((μ g : (↥LL.1)ˣ) : ↥LL.1) * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y)
        = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (s * kk i) * y) := by
          rw [Finset.smul_sum]; simp only [TensorProduct.smul_tmul', smul_eq_mul]
      _ = ((μ g : (↥LL.1)ˣ) : ↥LL.1) • ∑ i, (τ' s * cc i) ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.B (kk i) * y) := by rw [hB]
      _ = _ := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul', smul_eq_mul, ← mul_assoc, hτ, hμ, one_mul]

  have hlet : ∀ a : ↥(K0 K), mulVB (K₀ := ↥(K0 K)) (B := P.R.B) (V := ↥LL.1) (LL := ↥LL.1) a w = τ' a • w := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, mulVB, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    have : ∀ i, algebraMap ↥(K0 K) P.R.B a * (algebraMap ↥(K0 K) P.R.B (kk i) * y) = algebraMap ↥(K0 K) P.R.B (a * kk i) * y := by
      intro i; rw [map_mul, mul_assoc]
    simp only [this]
    rw [hB, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
  have hι : ∀ k : ↥(K0 K), (P.PD K).ι (algebraMap ↥(K0 K) P.R.B k * y) = algebraMap ↥(K0 K) P.R.BdR k * z := by
    intro k; rw [map_mul, AlgHom.commutes, P.PD_ι, ← hzdef]
  have hιw : ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w = ∑ i, cc i ⊗ₜ[ℚ_[l]] (algebraMap ↥(K0 K) P.R.BdR (kk i) * z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hw, map_sum, ιV, AlgebraTensorModule.map_tmul, LinearMap.id_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact hι (kk i)
  have hmem : ∀ k : ↥(K0 K), algebraMap ↥(K0 K) P.R.BdR k * z ∈ (P.PD K).Fil d := by
    intro k
    rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR, ← Algebra.smul_def]
    exact (P.PD K).Fil d |>.smul_mem _ hd
  refine ⟨w, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold Dcris
    refine (Submodule.mem_iInf _).2 fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hinv g, LinearMap.id_apply, sub_self]
  · refine (Submodule.mem_iInf _).2 fun a => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, hlet a, LinearMap.smul_apply, LinearMap.id_apply, sub_self]
  · rw [hιw]
    refine ⟨∑ i, cc i ⊗ₜ[ℚ_[l]] (⟨algebraMap ↥(K0 K) P.R.BdR (kk i) * z, hmem (kk i)⟩ : ↥(((P.PD K).Fil d).restrictScalars ℚ_[l])), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, AlgebraTensorModule.map_tmul]
  · intro hcon
    have hyu : ∀ n : ℕ, IsUnit ((⇑P.φB)^[n] x) := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact ih.map P.φB
    have hz : IsUnit z := by rw [hzdef, hy]; exact (hyu j).map P.ιB
    obtain ⟨v, hzv⟩ := hz.exists_right_inv
    have hvz : v * z = 1 := by rw [mul_comm]; exact hzv
    have hv : v ∈ (P.PD K).Fil (-d) := GlobalTheory.FilInv.inv_mem_Fil_neg l P AI hT K d z v hzv hd hd1
    let Mv : ↥LL.1 ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] ↥LL.1 ⊗[ℚ_[l]] P.R.BdR :=
      AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) (LinearMap.mulLeft ℚ_[l] v)
    have hvmul : ∀ b ∈ ((P.PD K).Fil (d + 1)).restrictScalars ℚ_[l], LinearMap.mulLeft ℚ_[l] v b ∈ ((P.PD K).Fil 1).restrictScalars ℚ_[l] := by
      intro b hb
      have := (P.PD K).Fil_mul (-d) (d + 1) v b hv hb
      rw [show -d + (d + 1) = 1 by ring] at this
      exact this
    have hMv : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) (d + 1), Mv t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1 := by
      rintro t ⟨s, rfl⟩
      refine ⟨AlgebraTensorModule.map (LinearMap.id : ↥LL.1 →ₗ[↥LL.1] ↥LL.1) ((LinearMap.mulLeft ℚ_[l] v).restrict hvmul) s, ?_⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Mv, AlgebraTensorModule.map_tmul]
      | add s t hs ht => simp only [map_add (f := _), hs, ht]
    have hE : Mv (ιV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) w) = ∑ i, cc i ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.BdR (kk i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hιw, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Mv, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
      rw [mul_left_comm, hvz, mul_one]
    have hF1 := hMv _ hcon
    rw [hE] at hF1
    let q := (((P.PD K).Fil 1).restrictScalars ℚ_[l]).mkQ
    let h0 : ↥(K0 K) →ₗ[ℚ_[l]] P.R.BdR ⧸ (((P.PD K).Fil 1).restrictScalars ℚ_[l]) :=
      q ∘ₗ (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.BdR).toLinearMap
    have hinj : Function.Injective h0 := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro k hk
      have hk' : algebraMap ↥(K0 K) P.R.BdR k ∈ (P.PD K).Fil 1 := by
        have := (Submodule.Quotient.mk_eq_zero _).1 hk
        exact this
      rw [IsScalarTower.algebraMap_apply ↥(K0 K) ↥K.1 P.R.BdR] at hk'
      have := JsetEmb.field_inter_filtration_one_eq_zero (P.PD K) _ hk'
      exact (map_eq_zero_iff _ (algebraMap ↥(K0 K) ↥K.1).injective).1 this
    have hq : ∀ t ∈ FilV (P.PD K) (LL := ↥LL.1) (V := ↥LL.1) 1, LinearMap.lTensor ↥LL.1 q t = 0 := by
      rintro t ⟨s, rfl⟩
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul]
        rw [show q ((((P.PD K).Fil 1).restrictScalars ℚ_[l]).subtype b) = 0 from (Submodule.Quotient.mk_eq_zero _).2 b.2, tmul_zero]
      | add s t hs ht => rw [map_add (f := _), map_add (f := _), hs, ht, add_zero]
    have hzero : LinearMap.lTensor ↥LL.1 h0 (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 0 := by
      have := hq _ hF1
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [h0, map_sum, LinearMap.lTensor_tmul] using this
    have he : (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K)) = 0 :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) h0 hinj (hzero.trans (map_zero _).symm)
    let Λ : ↥LL.1 ⊗[ℚ_[l]] ↥(K0 K) →ₗ[ℚ_[l]] ↥LL.1 := TensorProduct.lift ((LinearMap.mul ℚ_[l] ↥LL.1).compl₂ τ'.toLinearMap)
    have hΛ : Λ (∑ i, cc i ⊗ₜ[ℚ_[l]] kk i) = 1 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Λ, map_sum, h1]
    rw [he, map_zero] at hΛ
    exact zero_ne_one hΛ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrRepQuotientOfFiniteGen
section
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.DZero

theorem exists_irrRep_quotient_of_finite_gen : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), GlobalTheory.PRep.IsSmooth π → Nontrivial V → ∀ s : Finset V, Submodule.span ℂ (Set.range fun p : G × s => π p.1 (p.2 : V)) = ⊤ → ∃ (σ : IrrRep G) (p : V →ₗ[ℂ] σ.V), Function.Surjective p ∧ ∀ g v, p (π g v) = σ.ρ g (p v) := by
  intro G V _ _ _ _ _ π hπ hV s hs
  classical

  have htop : ∀ N : Submodule ℂ V, (∀ (g : G), ∀ v ∈ N, π g v ∈ N) →
      Submodule.span ℂ ((s : Set V)) ≤ N → N = ⊤ := by
    intro N hN hsN
    rw [eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact hN g _ (hsN (Submodule.subset_span v.2))
  let S : Set (Submodule ℂ V) := {N | (∀ (g : G), ∀ v ∈ N, π g v ∈ N) ∧ N ≠ ⊤}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], bot_ne_top⟩
  have hcomp := Submodule.finset_span_isCompactElement (R := ℂ) s
  obtain ⟨N, -, hmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hd : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun htop' => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨M, hM, hvM⟩ := (Submodule.mem_sSup_of_directed hne hd).1 hv
      exact le_sSup hM ((hcS hM).1 g v hvM)
    · obtain ⟨M, hM, hsM⟩ := (isCompactElement_iff_le_of_directed_sSup_le _).1 hcomp c hne hd
        (by rw [htop']; exact le_top)
      exact (hcS hM).2 (htop M (hcS hM).1 hsM)) ⊥ hbot
  obtain ⟨hNst, hNtop⟩ := hmax.prop
  let T : Subrepresentation π := ⟨N, fun g v hv => hNst g v hv⟩
  have hT : IsCoatom T := by
    refine ⟨fun h => hNtop (congrArg Subrepresentation.toSubmodule h), fun T' hT' => ?_⟩
    by_contra hne
    have hmem : T'.toSubmodule ∈ S := ⟨fun g v hv => T'.apply_mem_toSubmodule g hv,
      fun h => hne (Subrepresentation.toSubmodule_injective h)⟩
    have heq : T'.toSubmodule = N := le_antisymm (hmax.2 hmem hT'.le) hT'.le
    exact hT'.ne (Subrepresentation.toSubmodule_injective heq.symm)
  have hi := isIrreducible_subQuot hT.covBy_top
  let q : (⊤ : Subrepresentation π).toRepresentation.IntertwiningMap (subQuot ⊤ T) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hsm : IsSmooth (subQuot ⊤ T) :=
    IsSubquotient.isSmooth ⟨⊤, q, Submodule.Quotient.mk_surjective _⟩ hπ
  let σ : IrrRep G := ⟨_, subQuot ⊤ T, hsm, hi⟩
  let p : V →ₗ[ℂ] σ.V := (Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
    LinearMap.id (fun _ => trivial)
  refine ⟨σ, p, fun w => ?_, fun g v => rfl⟩
  obtain ⟨⟨v, -⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨v, rfl⟩

end GlobalTheory.DZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterDefiniteUnitaryInertPlaceStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satakeParameter_definiteUnitary_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ), (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) → Formalism.UG.IsUnramInv ϖ s q → (∀ L : Subgroup (finU (E := E) (n := n)), IsOpen (L : Set (finU (E := E) (n := n))) → ∀ C : Submodule ℂ (infU E n → ℂ), FiniteDimensional ℂ C → FiniteDimensional ℂ (Submodule.span ℂ {ψ : UA E n → ℂ | (∀ γ ∈ ratU E n, ∀ g, ψ (γ * g) = ψ g) ∧ (∀ k ∈ L, ∀ g, ψ (g * (k : UA E n)) = ψ g) ∧ ∀ g, (fun y : infU E n => ψ (g * (y : UA E n))) ∈ C})) → (∃ ι : Formalism.UG.UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) →* UA E n, Continuous ι ∧ (∀ g, ι g ∈ locU n w ∧ cLoc w (ι g) = g.1) ∧ (∀ x ∈ locU n w, cLoc w x = 1 → x = 1) ∧ ∀ x g, cLoc w x = 1 → x * ι g = ι g * x) → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → IsUnramU π w → ∃ α, HasSatAt π w s ϖ q α := by
  first | exact @GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | exact GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt | (intros; apply GlobalTheory.UnitaryBC.SatEx.exists_hasSatAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionUnramifiedAtOnePlaceStatement
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_totallyComplex_ext_with_unity_roots : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (g : ℕ)
    [Fact g.Prime] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n),
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsTotallyComplex E') (_ : Algebra E E')
      (_ : Algebra E' Ω) (_ : IsScalarTower E E' Ω) (_ : IsAlgClosure E' Ω) (w' : HeightOneSpectrum (𝓞 E'))
      (_ : IsPlaceOver A w'), ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal ∧ ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2 ∧
      normV w' = g ^ n ∧ (∃ ζ : E', IsPrimitiveRoot ζ (g ^ n - 1)) ∧
      ∀ t ∈ Ine (F := E) A, ∀ e : E', t (algebraMap E' Ω e) = algebraMap E' Ω e := by
  first | exact @GlobalTheory.UnrCycExt.exists_unramified_ext | exact GlobalTheory.UnrCycExt.exists_unramified_ext | (intros; apply GlobalTheory.UnrCycExt.exists_unramified_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertiaStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inverseLocalArtin_continuousOn_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω) (a : Weil h →* (w.adicCompletion E)ˣ), GlobalTheory.HeckeGal.IsGlobalArtin art → (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) → (∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ) → Continuous fun σ : Ine (F := E) A => a (ineIncl h σ) := by
  first | exact @GlobalTheory.ArtinInvCont.continuous_inv_on_ine | exact GlobalTheory.ArtinInvCont.continuous_inv_on_ine | (intros; apply GlobalTheory.ArtinInvCont.continuous_inv_on_ine <;> assumption)
end

