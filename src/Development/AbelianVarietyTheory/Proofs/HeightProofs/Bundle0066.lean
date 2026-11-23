module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrimesOneModNSplitCompletelyWeberField
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0027

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open GlobalTheory.TypeSum

theorem coef_of_gkMap : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := GlobalTheory.T.discreteSeries_gKMap_values_eq_generalisedCoefficients

theorem coef_transport : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := _root_.GlobalTheory.TypeSum.FrameChange.coef_frame_change

theorem closure_model : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := _root_.GlobalTheory.ClosureSeries.hasTypeAll_of_closure

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε} := rfl
  rw [this]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem continuous_mul_left_GA {D : D7} (V : HSp D) (x : GA D V) : Continuous fun y : GA D V => x * y := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := inferInstance
  refine continuous_induced_rng.2 ?_
  exact (continuous_const_mul _).comp continuous_induced_dom

theorem closure_to_series : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ → IsTypeAt θ V τ S φ := by
  intro D θ V τ S φ hEx hUn hHC hCW hθ hV hS hφ hT
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  obtain ⟨H, i1, i2, σ, hc, hnt, hU, hI, hL2, hK, hmin⟩ := hEx _ ε₀ lam₀ hP₀
  have hσ : IsDS ε₀ lam₀ σ := ⟨hc, hnt, hU, hI, hL2, hK, hmin⟩
  obtain ⟨P, hPu, hPG⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
  refine ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, hPu, hPG, fun x => ?_⟩

  have hfin : ∀ ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType θ V τ S, ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H),
      (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧ (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j)) := by
    intro ψ hψ
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType, sSup_eq_iSup'] at hψ
    refine Submodule.iSup_induction (motive := fun ψ : GA D V → ℂ => ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ))
      (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧
      (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j))) _ hψ ?_ ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
      fun y _ => by simp⟩ ?_
    · rintro ⟨W, H', j1, j2, σ', lam, ε, P', T, hE, hHC', hD', hP', hJ', hGK, rfl⟩ ψ ⟨w, rfl⟩
      obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
      obtain ⟨ℓ, hℓ, hv, he⟩ := coef_of_gkMap θ V τ hθ hHC hCW H' σ' lam ε P' T hHC' hD' hP' hJ' hGK w x
      obtain ⟨ℓ', v', hℓ', hv', he'⟩ := coef_transport hUn _ ε lam hHC' H H' σ σ' hσ hD' P P' _ hPu hP' hPG hJ'
        (fun y => T w (x * atTau θ V τ y)) ℓ w hℓ hv he
      exact ⟨1, fun _ => ℓ', fun _ => v', fun _ => hℓ', fun _ => hv', fun y hy => by simpa using he' y hy⟩
    · rintro a b ⟨m, ℓ, v, h1, h2, h3⟩ ⟨m', ℓ', v', h1', h2', h3'⟩
      refine ⟨m + m', Fin.append ℓ ℓ', Fin.append v v', fun j => ?_, fun j => ?_, fun y hy => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h1 i
        · simpa using h1' i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h2 i
        · simpa using h2' i
      · show a _ + b _ = _
        rw [h3 y hy, h3' y hy, Fin.sum_univ_add]
        simp
  set f : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P)) with hf
  have hcont : ContinuousOn (fun y : Matrix (Fin V.rank) (Fin V.rank) ℂ => x * atTau θ V τ (P⁻¹ * y * P))
      (UJset ε₀) := by
    refine (continuous_mul_left_GA V x).comp_continuousOn ?_
    refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn ?_
    intro y hy
    exact GlobalTheory.LowTypeDetermined.conj_inv_mem hPu hPG hy
  have hfc : ContinuousOn f (UJset ε₀) := hφ.cont.comp_continuousOn hcont
  have hB := closure_model hHC hCW _ ε₀ lam₀ hP₀ H σ hσ f hfc
    (GlobalTheory.TypeSum.GrowthAtPlace.umg_atTau D θ hθ V τ φ hφ ε₀ P hPu hPG x) (by
      intro C hC δ hδ
      have hK : IsCompact ((fun y => x * atTau θ V τ (P⁻¹ * y * P)) '' (C ∩ UJset ε₀)) :=
        (hC.inter_right (isClosed_UJset ε₀)).image_of_continuousOn (hcont.mono Set.inter_subset_right)
      obtain ⟨ψ, hψ, happ⟩ := hT _ hK δ hδ
      obtain ⟨m, ℓ, v, h1, h2, h3⟩ := hfin ψ hψ
      refine ⟨m, ℓ, v, h1, h2, fun y hyC hy => ?_⟩
      rw [← h3 y hy]
      exact happ _ ⟨y, ⟨hyC, hy⟩, rfl⟩)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have a1 := Matrix.mul_nonsing_inv _ hd
  have a2 := Matrix.nonsing_inv_mul _ hd
  have hi : P⁻¹⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _ hd
  have t3 := GlobalTheory.TypeSum.hasTypeAll_transport _ H H σ (fun g => σ (P * g * P⁻¹)) (Formalism.REAL.Jm ε₀)
    (gramAt D V τ) P⁻¹ (GlobalTheory.TypeSum.isUnit_Jm ε₀) (IsUnit.of_mul_eq_one _ a2) (by
      rw [show gramAt D V τ = Pᴴ * Formalism.REAL.Jm ε₀ * P from hPG.symm]
      calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε₀ * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε₀ * (P * P⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1]; simp) (LinearIsometryEquiv.refl ℂ H) (fun g _ v => by
      have e : P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹ = g := by
        rw [hi]
        calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [a1, Matrix.one_mul, Matrix.mul_one]
      show σ g v = σ (P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹) v
      rw [e]) f hB
  have e' : (fun y => f (P⁻¹⁻¹ * y * P⁻¹)) = fun y => φ (x * atTau θ V τ y) := by
    funext y
    show φ (x * atTau θ V τ (P⁻¹ * (P⁻¹⁻¹ * y * P⁻¹) * P)) = φ (x * atTau θ V τ y)
    rw [hi]
    congr 3
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [a2, Matrix.one_mul, Matrix.mul_one]
  rw [e'] at t3
  exact GlobalTheory.TypeSum.hasTypeAll_iff.1 t3

end GlobalTheory.ClosureSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValues
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberSplit
open scoped IntermediateField

namespace GlobalTheory.WeberSplitAny

theorem splits_completely_of_three_le : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n))) (S : Finset ℕ), ∀ (π : 𝓞 K) (p : ℕ), p.Prime → p ∉ S → Ideal.absNorm (Ideal.span {π}) = p → π - 1 ∈ Ideal.span {(n : 𝓞 K)} → {Q : HeightOneSpectrum (𝓞 (IntermediateField.adjoin K (weberSet L n))) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 (IntermediateField.adjoin K (weberSet L n)))) = Ideal.span {π}}.ncard = Module.finrank K (IntermediateField.adjoin K (weberSet L n)) := by
  classical
  intro K _ _ h2 hd L hL n hn
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have g2 := g₂_ne_zero K h2 L hL hd
  have g3 := g₃_ne_zero K h2 L hL hd
  have hD := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨hfin, halg, hperm⟩ := _root_.GlobalTheory.FieldSize.weberSet_finite_algebraic_permuted L n (by omega) g2 g3
  replace halg := halg (invariant_isAlgebraic K h2 L hL)
  have hweb := _root_.GlobalTheory.WeberCongruenceAnyOrder.weber_congruences K h2 L hL
  have hJw : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∈ weberSet L n := Or.inl rfl
  have hJ0 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ≠ 0 := div_ne_zero (pow_ne_zero _ g2) hD
  have hJ1 : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) - 1 ≠ 0 := by
    rw [sub_ne_zero, Ne, div_eq_one_iff_eq hD]
    intro h
    exact g3 (pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination h / 27))
  have hw : ∀ w ∈ weberSet L n, w = L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) ∨ ∃ t, (n : ℂ) * t ∈ L.lattice ∧
      t ∉ L.lattice ∧ w = L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t := by
    rintro w (h | ⟨z, hz, hz', e⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z / n, by rwa [mul_div_cancel₀ _ hn0], hz', e⟩
  generalize L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = J at *
  generalize L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = u at *
  generalize weberSet L n = T at *
  have := hfin.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K T) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral.tower_top
  have hM : NumberField (IntermediateField.adjoin K T) := NumberField.of_module_finite K _
  refine ⟨hM, ?_⟩
  have hTM := IntermediateField.subset_adjoin K T
  set M := IntermediateField.adjoin K T
  have hext : ∀ (N : Type) [Field N] [Algebra K N] (f g : M →ₐ[K] N),
      (∀ x (hx : x ∈ T), f ⟨x, hTM hx⟩ = g ⟨x, hTM hx⟩) → f = g :=
    fun N _ _ f g h => IntermediateField.adjoin_algHom_ext K h
  clear_value M
  obtain ⟨N, _, _, _, _, _, _, ι, hι⟩ := exists_isGalois K M
  replace hι : ∀ x : M, ι (algebraMap M N x) = x := hι
  have hιK : ∀ x : K, ι (algebraMap K N x) = x := fun x => by
    rw [IsScalarTower.algebraMap_apply K M N, hι]; rfl
  let j : N := algebraMap M N ⟨J, hTM hJw⟩
  have hj : ι j = J := hι _
  have hfin' : (ι ⁻¹' T).Finite := hfin.preimage ι.injective.injOn
  obtain ⟨d, hd0, hdi⟩ := exists_integral_multiples ℤ ℚ (hfin'.toFinset ∪ {j⁻¹, (j - 1)⁻¹} ∪
    Finset.univ.image fun σ : N ≃ₐ[K] N => (σ j - j)⁻¹)
  refine ⟨(6 * n * d.natAbs).primeFactors, fun π p hp hpS hN hπ => ?_⟩
  have hnd : ¬ p ∣ 6 * n * d.natAbs := fun h => hpS (Nat.mem_primeFactors.2 ⟨hp, h, by positivity⟩)
  have hpn : ¬ p ∣ n := fun h => hnd ((h.mul_left _).mul_right _)
  have hpd : ¬ (p : ℤ) ∣ d := fun h => hnd ((Int.natCast_dvd.1 h).mul_left _)
  have hp5 : 5 ≤ p := by
    by_contra h
    have h6 : ¬ p ∣ 6 := fun h => hnd ((h.mul_right _).mul_right _)
    have := hp.two_le
    have : p < 5 := by omega
    interval_cases p
    exacts [h6 (by norm_num), h6 (by norm_num), absurd hp (by norm_num)]
  have hprime : (Ideal.span {π}).IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  have hbot : Ideal.span {π} ≠ ⊥ := fun h => hp.ne_zero (by rw [← hN, h]; simp)
  refine ncard_eq_of_tower K M N ⟨Ideal.span {π}, hprime, hbot⟩ ?_
  rintro σ ⟨P, hP, hPo, hσ⟩
  simp only [hN] at hσ hPo
  obtain ⟨W, hW⟩ := exists_valuationSubring ι P hP.ne_top
  have hover : ∀ x ∈ Ideal.span {π}, W.valuation ((x : K) : ℂ) < 1 := fun x hx => by
    have h := hW _ ((Ideal.mem_of_liesOver P (Ideal.span {π}) x).1 hx)
    rw [← hιK]
    exact h
  have hpW : W.valuation p < 1 := by
    simpa [hN] using hover _ (Ideal.absNorm_mem (Ideal.span {π}))
  obtain ⟨-, hJp, hm⟩ := hweb W π p hp hp5 hN (W.mem_nonunits_iff.2 (hover _ (Ideal.mem_span_singleton_self _)))
  obtain ⟨hm1, hm2⟩ := hm n hpn
  simp only [ValuationSubring.mem_nonunits_iff] at hJp hm1 hm2
  have hc : ∀ x : N, ι x ∈ T → W.valuation (ι (σ x) - ι x ^ p) < 1 := fun x hx =>
    frob_congr ι σ W hp hpW (fun y => hW _ (hσ y)) hpd (hdi x (by simp [hx]))
  have hz : ∀ x : N, IsIntegral ℤ (d • x⁻¹) → W.valuation (ι x) < 1 → x = 0 := fun x =>
    eq_zero_of_valuation_lt_one ι W hp hpW hpd
  have hσj : σ j = j := by
    refine sub_eq_zero.1 (hz _ (hdi _ (by simp)) ?_)
    have := Valuation.map_sub_lt _ (hc j (hj ▸ hJw)) hJp
    rw [map_sub ι]
    rw [hj] at this ⊢
    convert this using 2
    ring
  have hm3 := hm2 (fun h => hJ0 (by rw [← hj, hz j (hdi _ (by simp)) (hj ▸ h), map_zero]))
    (fun h => hJ1 (by
      have e : ι (j - 1) = J - 1 := by rw [map_sub, hj, map_one]
      rw [← e, hz (j - 1) (hdi _ (by simp)) (e ▸ h), map_zero]))
  have : Countable N := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq N ι (ι.comp σ.toRingEquiv.toRingHom)
  have hτ' : ∀ x, τ (ι x) = ι (σ x) := hτ
  have key : (σ : N →ₐ[K] N).comp (IsScalarTower.toAlgHom K M N) = IsScalarTower.toAlgHom K M N := by
    refine hext N _ _ fun w hwT => ?_
    change σ (algebraMap M N ⟨w, hTM hwT⟩) = algebraMap M N ⟨w, hTM hwT⟩
    rcases hw w hwT with rfl | ⟨t, ht, ht', rfl⟩
    · exact hσj
    · set x := algebraMap M N ⟨_, hTM hwT⟩
      have hx : ι x = u * L.weierstrassP t := hι _
      obtain ⟨s, hs, hs', e⟩ := hperm τ (by rw [← hj, hτ', hσj]) t ht ht'
      have h1 := hc x (hx ▸ hwT)
      rw [← hτ', hx, e] at h1
      have h3 := (hm1 t ht ht').2
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hπ
      obtain ⟨a, ha⟩ := (hL _).1 ht
      have e1 : ((π : K) : ℂ) * t = t + ((c * a : 𝓞 K) : K) := by
        have : ((c : K) : ℂ) * n = ((π : K) : ℂ) - 1 := by
          simpa using congrArg (fun y : 𝓞 K => ((y : K) : ℂ)) hc
        push_cast
        rw [ha]
        linear_combination -t * this
      rw [e1, L.weierstrassP_add_coe t ⟨_, (hL _).2 ⟨_, rfl⟩⟩] at h3
      have h4 := Valuation.map_sub_lt _ h3 h1
      rw [sub_sub_sub_cancel_right] at h4
      apply ι.injective
      rw [← hτ', hx, e]
      congr 1
      rcases hm3 t s ht ht' hs hs' h4 with h | h
      · rw [← L.weierstrassP_add_coe s ⟨_, h⟩]
        simp
      · rw [← L.weierstrassP_neg s, ← L.weierstrassP_add_coe (-s) ⟨_, h⟩]
        simp
  exact fun x => DFunLike.congr_fun key x

end GlobalTheory.WeberSplitAny
end

