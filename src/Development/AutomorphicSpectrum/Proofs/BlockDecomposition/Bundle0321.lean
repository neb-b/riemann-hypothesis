module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
public import GroundTheory.AutomorphicForms.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0298
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0308
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0254
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MetaplecticLowRank.LowC
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveIdempotentsSeparating
section
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem dvd_of_aeval_eq_zero_of_dvd_charpoly {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) {p g : K[X]} (hp : Irreducible p) (hpc : p ∣ γ.charpoly)
    (hg : aeval γ g = 0) : p ∣ g := by
  classical
  by_contra hn
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd).2 hn
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p (ne_of_gt (degree_pos_of_irreducible hp))
  have hroot : (γ.map (algebraMap K (AlgebraicClosure K))).charpoly.IsRoot α := by
    obtain ⟨c, hc⟩ := hpc
    rw [Matrix.charpoly_map, hc, IsRoot, eval_map_algebraMap, map_mul, hα, zero_mul]
  have hs : α ∈ spectrum (AlgebraicClosure K) (γ.map (algebraMap K (AlgebraicClosure K))) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval (γ.map (algebraMap K (AlgebraicClosure K)))
    (g.map (algebraMap K (AlgebraicClosure K))) ⟨α, hs, rfl⟩
  have h3 : aeval (γ.map (algebraMap K (AlgebraicClosure K))) (g.map (algebraMap K (AlgebraicClosure K))) = 0 := by
    have := aeval_algHom_apply ((Algebra.ofId K (AlgebraicClosure K)).mapMatrix (m := Fin n)) γ g
    rw [hg, map_zero] at this
    rw [aeval_map_algebraMap]
    exact this
  rw [h3] at h2
  have h4 : aeval α g = 0 := by
    by_contra hne
    apply h2
    simp only [eval_map_algebraMap]
    rw [spectrum.mem_resolventSet_iff, sub_zero]
    exact (Ne.isUnit hne).map (algebraMap (AlgebraicClosure K) (Matrix (Fin n) (Fin n) (AlgebraicClosure K)))
  have h5 := congrArg (aeval α) hab
  simp [hα, h4] at h5

theorem exists_prim_of_irreducible {K : Type} [Field K] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) K) (hs : γ.charpoly.Separable) {p : K[X]} (hp : Irreducible p)
    (hpc : p ∣ γ.charpoly) :
    ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := by
  obtain ⟨q, hq⟩ := hpc
  have hχ : aeval γ (p * q) = 0 := by rw [← hq]; exact Matrix.aeval_self_charpoly γ
  obtain ⟨b, u, hbu⟩ : IsCoprime p q := (hq ▸ hs : (p * q).Separable).isCoprime
  have hnd : ∀ c : K[X], aeval γ (c * (p * q)) = 0 := fun c => by rw [map_mul, hχ, mul_zero]
  have hsub : (1 : K[X]) - u * q = b * p := by rw [← hbu]; ring
  have hdvd : p ∣ 1 - u * q := ⟨b, by rw [hsub]; ring⟩
  refine ⟨aeval γ (u * q), ⟨⟨_, rfl⟩, ?_, ?_, ?_⟩, _, rfl, hdvd⟩
  · rw [← map_mul]
    have : u * q * (u * q) = u * q - (u * b) * (p * q) := by linear_combination (-(u * q)) * hsub
    rw [this, map_sub, hnd, sub_zero]
  · intro h0
    have h1 := dvd_of_aeval_eq_zero_of_dvd_charpoly γ hp ⟨q, hq⟩ h0
    exact hp.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hdvd h1))
  · intro h hne
    have hnp : ¬ p ∣ h := by
      rintro ⟨c, rfl⟩
      apply hne
      rw [← map_mul]
      have : p * c * (u * q) = (c * u) * (p * q) := by ring
      rw [this, hnd]
    obtain ⟨a', a, haa⟩ := (hp.coprime_iff_not_dvd).2 hnp
    refine ⟨a, ?_⟩
    rw [← map_mul, ← map_mul]
    have : a * (h * (u * q)) = u * q - (a' * u) * (p * q) := by linear_combination (u * q) * haa
    rw [this, map_sub, hnd, sub_zero]

theorem exists_prim_cover (K : Type) [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K)
    (hs : γ.charpoly.Separable) :
    ∃ S : Finset (Matrix (Fin n) (Fin n) K), (∀ e ∈ S, IsPrim γ e) ∧
      ∀ x : Fin n → K, x ≠ 0 → ∃ e ∈ S, x ᵥ* e ≠ 0 := by
  classical
  have key : ∀ p : K[X], p ∈ UniqueFactorizationMonoid.normalizedFactors γ.charpoly →
      ∃ e, IsPrim γ e ∧ ∃ f : K[X], e = aeval γ f ∧ p ∣ 1 - f := fun p hp =>
    exists_prim_of_irreducible γ hs (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp)
      (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)
  choose! E hE using key
  have hχ0 : γ.charpoly ≠ 0 := (Matrix.charpoly_monic γ).ne_zero
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors γ.charpoly).toFinset.image E, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
    exact (hE p (Multiset.mem_toFinset.1 hp)).1
  · intro x hx
    let I : Ideal K[X] :=
      { carrier := {f | x ᵥ* aeval γ f = 0}
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_add (f := _), Matrix.vecMul_add, ha, hb, add_zero]
        zero_mem' := by simp
        smul_mem' := fun c f hf => by
          simp only [Set.mem_setOf_eq] at hf ⊢
          rw [smul_eq_mul, mul_comm, map_mul, ← Matrix.vecMul_vecMul, hf, Matrix.zero_vecMul] }
    have hmem : ∀ f, f ∈ I ↔ x ᵥ* aeval γ f = 0 := fun f => Iff.rfl
    set a := Submodule.IsPrincipal.generator I with ha
    have hdiv : ∀ f, f ∈ I ↔ a ∣ f := fun f => Submodule.IsPrincipal.mem_iff_generator_dvd I
    have haχ : a ∣ γ.charpoly := (hdiv _).1 (by
      rw [hmem, Matrix.aeval_self_charpoly, Matrix.vecMul_zero])
    have ha0 : a ≠ 0 := fun h => hχ0 (by simpa [h] using haχ)
    have hau : ¬ IsUnit a := fun h => hx (by
      have h1 : (1 : K[X]) ∈ I := (hdiv 1).2 h.dvd
      rw [hmem, map_one, Matrix.vecMul_one] at h1
      exact h1)
    obtain ⟨i, hi, hia⟩ := WfDvdMonoid.exists_irreducible_factor hau ha0
    obtain ⟨p, hp, hip⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hχ0 hi (hia.trans haχ)
    obtain ⟨hprim, f, hf, hpf⟩ := hE p hp
    refine ⟨E p, Finset.mem_image.2 ⟨p, Multiset.mem_toFinset.2 hp, rfl⟩, fun h0 => ?_⟩
    rw [hf] at h0
    have h1 : a ∣ f := (hdiv f).1 h0
    have h2 : p ∣ f := hip.symm.dvd.trans (hia.trans h1)
    have hpi : Irreducible p := UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp
    exact hpi.not_isUnit (isUnit_of_dvd_one (by simpa using dvd_add hpf h2))

end GlobalTheory.CompanionTheory.TorusCh
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratedSubsheafLeIdealPower
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.TwGen

namespace GlobalTheory.CompanionTheory.GE.TwGen

theorem mem_twSecs_of_mem_twPow {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (P : X.Modules)
    (n : ℤ) (m : ℕ) : twPow I H n P m ⊆ twSecs H n (powSub I P m) := by
  letI : Algebra A Γ(X, ⊤) := GroundTheory.Arith.SchemeCoh.overAlgebra (CommRingCat.of A)
  have fac : ∀ a ∈ I ^ m, ∃ ψ : P ⟶ GroundTheory.Arith.SchemeCoh.idealPow I P m,
      ψ ≫ GroundTheory.Arith.SchemeCoh.idealPowι I P m = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
    intro a ha
    rw [← GroundTheory.Arith.SchemeCoh.span_idealGen (I ^ m)] at ha
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ha
    let u : P ⟶ ⨁ fun _ : Fin (GroundTheory.Arith.SchemeCoh.idealGenNum (I ^ m)) => P :=
      biproduct.lift fun k => GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) (c k))
    have hu : u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m) = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      rw [← hc]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [u, GroundTheory.Arith.SchemeCoh.idealSumMap, biproduct.lift_desc, GroundTheory.Arith.SchemeCoh.smulHom_comp_smulHom, map_sum, GroundTheory.Arith.SchemeCoh.smulHom_sum,
        smul_eq_mul, map_mul]
    refine ⟨kernel.lift (cokernel.π (GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))) (u ≫ GroundTheory.Arith.SchemeCoh.idealSumMap P (I ^ m))
      (by rw [Category.assoc, cokernel.condition, comp_zero]), ?_⟩
    rw [← hu]
    exact kernel.lift_ι _ _ _
  have act : ∀ (r : Γ(X, ⊤)) (s : Γ(GlobalTheory.twistZ P H n, ⊤)),
      ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (GroundTheory.Arith.SchemeCoh.smulHom P r)) ⊤) s
        = GroundTheory.Arith.SchemeCoh.restrictTop ⊤ r • s := by
    intro r s
    rw [GlobalTheory.Twist.sec_ext_iff]
    intro i
    rw [GlobalTheory.Twist.coord_map_app, GroundTheory.Arith.SchemeCoh.smulHom_app_apply, GlobalTheory.Twist.coord_smul]
    congr 1
    exact (GroundTheory.Arith.SchemeCoh.restrictTop_restrict _ r).symm
  have base : ∀ a ∈ I ^ m, ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤ a • s ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)) := by
    intro a ha s
    obtain ⟨ψ, hψ⟩ := fac a ha
    have e : (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (powSub I P m).arrow
        = GroundTheory.Arith.SchemeCoh.smulHom P (algebraMap A Γ(X, ⊤) a) := by
      show (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv) ≫ (Subobject.mk (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).arrow = _
      rw [Category.assoc, Subobject.underlyingIso_arrow, hψ]
    refine ⟨ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n)
      (ψ ≫ (Subobject.underlyingIso (GroundTheory.Arith.SchemeCoh.idealPowι I P m)).inv)) ⊤) s, ?_⟩
    have h2 := act (algebraMap A Γ(X, ⊤) a) s
    rw [← e] at h2
    erw [GlobalTheory.Twist.map_comp, Scheme.Modules.Hom.comp_app] at h2
    try erw [ConcreteCategory.comp_apply] at h2
    exact h2
  let K : Ideal Γ(X, ⊤) :=
    { carrier := {r | ∀ s : Γ(GlobalTheory.twistZ P H n, ⊤), r • s ∈ Set.range
        (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤))}
      add_mem' := by
        intro x y hx hy s
        obtain ⟨u, hu⟩ := hx s
        obtain ⟨v, hv⟩ := hy s
        exact ⟨u + v, by rw [map_add (f := _), hu, hv, add_smul]⟩
      zero_mem' := by
        intro s
        exact ⟨0, by rw [map_zero, zero_smul]⟩
      smul_mem' := by
        intro t x hx s
        obtain ⟨u, hu⟩ := hx (t • s)
        exact ⟨u, by rw [hu, smul_eq_mul, mul_comm, mul_smul]⟩ }
  have hJ : Ideal.map (GroundTheory.Arith.SchemeCoh.toFunctions (X := X) ⊤) (I ^ m) ≤ K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact base a ha
  intro c hc
  simp only [twPow, SetLike.mem_coe] at hc
  refine Submodule.smul_induction_on (p := fun x => x ∈ Set.range
      (ConcreteCategory.hom (Scheme.Modules.Hom.app (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (powSub I P m).arrow) ⊤)))
    hc ?_ ?_
  · intro r hr s _
    exact hJ hr s
  · intro x y hx hy
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add (f := _), hu, hv]⟩

theorem genSub_le_powSub : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X} (hH : H.IsLB)
    {P : X.Modules}, P.IsQuasicoherent → ∀ (n : ℤ) (m : ℕ) (c : Γ(GlobalTheory.twistZ P H n, ⊤)),
    c ∈ twPow I H n P m → genSub hH n c ≤ powSub I P m := by
  intro A _ _ I X _ H hH P _ n m c hc
  exact genSub_le hH (powSub I P m) n c (mem_twSecs_of_mem_twPow I H P n m hc)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFibreMeasureLocal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.FibSim

theorem conj_scal {A : Type} [CommRing A] {M n : ℕ} (C : Matrix (Fin n) (Fin M) A)
    (D : Matrix (Fin M) (Fin n) A) (G' G J : Matrix (Fin M) (Fin M) A) (t : A)
    (h : G' * J * G = t • J) : (C * G' * J) * (G * D) = t • (C * J * D) := by
  calc (C * G' * J) * (G * D) = C * (G' * J * G) * D := by simp only [Matrix.mul_assoc]
    _ = t • (C * J * D) := by rw [h, Matrix.mul_smul, Matrix.smul_mul]

theorem fib_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : GL (Fin M) (R ⊗[F] E)) (l : R), IsUnit l → cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (algebraMap R (R ⊗[F] E) l) • JR R J → ∀ a c : ℝ≥0, μ.map (actTup R g) = a • μ → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l) = c • ν → ∀ S, (m S).map (actTup R g) = (a / c) • m (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ l S) := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν m hμ hν hm g l hl hgl a c hmu hnu S
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨hTK, hLK, hSK, hTK2, -, -, -, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  haveI := hBor n M
  obtain ⟨hLH, hSH, hT2H, hBH, hG⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨G, hGc, hGe⟩ := hG M J hJ
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hσ R hR
  have hcont : ∀ h : GL (Fin M) (R ⊗[F] E),
      Continuous (actTup R h : (Fin n → Fin M → R ⊗[F] E) → (Fin n → Fin M → R ⊗[F] E)) := by
    intro h
    refine continuous_pi fun b => ?_
    exact continuous_const.matrix_mulVec (continuous_apply b)
  let e : (Fin n → Fin M → R ⊗[F] E) ≃ₜ (Fin n → Fin M → R ⊗[F] E) :=
    { toFun := actTup R g
      invFun := actTup R g⁻¹
      left_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      right_inv := fun X => by
        funext b
        simp [actTup, Matrix.mulVec_mulVec]
      continuous_toFun := hcont g
      continuous_invFun := hcont g⁻¹ }
  obtain ⟨u, rfl⟩ := hl
  let am := algebraMap R (R ⊗[F] E)
  have hinv : ∀ (v w : Rˣ) (_ : (v : R) * w = 1) (A : HermR R σ n),
      GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (w : R) A) = A := by
    intro v w hvw A
    apply Subtype.ext
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, smul_smul, ← map_mul, hvw,
      map_one, one_smul]
  have hcs : ∀ v : R, Continuous (GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ v : HermR R σ n → HermR R σ n) := by
    intro v
    have hv : Continuous fun A : HermR R σ n => (A : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    exact (hv.const_smul (algebraMap R (R ⊗[F] E) v)).subtype_mk _
  let τh : HermR R σ n ≃ₜ HermR R σ n :=
    { toFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R)
      invFun := GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ ((u⁻¹ : Rˣ) : R)
      left_inv := hinv _ _ (by simp)
      right_inv := hinv _ _ (by simp)
      continuous_toFun := hcs _
      continuous_invFun := hcs _ }
  let B : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}
  have hBo : IsOpen B := by
    have : B = (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hdet : ∀ (v : Rˣ) (A : HermR R σ n), A ∈ B → GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A ∈ B := by
    intro v A hA
    show IsUnit ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (v : R) A : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, Matrix.det_smul]
    exact ((v.isUnit.map (algebraMap R (R ⊗[F] E))).pow _).mul hA
  have hBτ : τh '' B = B := by
    ext S'
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact hdet _ _ hS
    · intro hS'
      exact ⟨τh.symm S', hdet _ _ hS', τh.apply_symm_apply _⟩
  have hU : G ⁻¹' B = {X | IsUnit (gramR R σ J X).det} := by
    ext X
    show IsUnit _ ↔ IsUnit _
    rw [hGe]
  have hfam : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (G ⁻¹' B) ν B m := by
    rw [hU]
    exact hm
  have hgram : ∀ X : Fin n → Fin M → R ⊗[F] E, gramR R σ J (actTup R g X) =
      (algebraMap R (R ⊗[F] E) (u : R)) • gramR R σ J X := by
    intro X
    rw [GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq, GlobalTheory.CompanionTheory.SW.GramAlg.colM_actTup,
      cT_mul]
    exact conj_scal _ _ _ _ _ _ hgl
  have hcomm : ∀ X, G (e X) = τh (G X) := by
    intro X
    apply Subtype.ext
    show ((G (actTup R g X) : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      ((GlobalTheory.CompanionTheory.SW.MassSimil.scalH R σ (u : R) (G X) : HermR R σ n) :
        Matrix (Fin n) (Fin n) (R ⊗[F] E))
    rw [← hGe, GlobalTheory.CompanionTheory.SW.MassSimil.scalH_coe, ← hGe]
    exact hgram X
  have htr := GlobalTheory.CompanionTheory.SW.isFibreFamily_transport _ _ _ μ ν (gramR R σ J) G Subtype.val
    Subtype.val_injective hGc hGe _ (gramR R σ J) G hGc hGe e τh hcomm B hBo m hfam
  rw [hBτ, hU] at htr
  have hmu' : μ.map e = a • μ := hmu
  have hnu' : ν.map τh = c • ν := hnu
  rw [hmu', hnu'] at htr
  have hnew : IsGramFib R σ J n (a • μ) (c • ν) (fun b => (m (τh.symm b)).map e) := htr
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h0 : μ.map e = 0 := by rw [hmu', zero_smul]
    have h1 : (μ.map e) Set.univ = μ Set.univ := by
      rw [e.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos μ Set.univ_nonempty).ne h1
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : ν.map τh = 0 := by rw [hnu', zero_smul]
    have h1 : (ν.map τh) Set.univ = ν Set.univ := by
      rw [τh.measurableEmbedding.map_apply, Set.preimage_univ]
    rw [h0] at h1
    exact (isOpen_univ.measure_pos ν Set.univ_nonempty).ne h1
  haveI hμa : (a • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ ha0
  haveI hνc : (c • ν).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul ν hc0
  have hres := GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale F E σ hσ M J hJ R hR n μ ν m hμ hν hm a c ha0 hc0
  have huq := GlobalTheory.CompanionTheory.SW.GramFib.fibre_unique F E σ hσ M J hJ R hR n (a • μ) (c • ν) _ hμa hνc hres _ hnew (τh S)
  have hs : τh.symm (τh S) = S := τh.symm_apply_apply S
  simp only [hs] at huq
  exact huq.symm

end GlobalTheory.CompanionTheory.SW.FibSim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealElementMapsClosedSystemDownStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_element_maps_closed_system_down : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, P.IsQuasicoherent → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ a ∈ I, MapsDown S (toFunctions (X := X) (A := A) ⊤ a) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | exact GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions | (intros; apply GlobalTheory.CompanionTheory.GE.Step.Maps.mapsDown_toFunctions <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroup
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isCompact_Gx : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), IsCompact (Gx k e : Set (GL (Fin n) k)) := by
  intro k _ _ _ _ n s d e
  have hle : PositivityTheory.LowerBoundConstant.Gx k e ≤ GlobalTheory.SplitWeil.KO k (Fin n) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact sup_le GlobalTheory.StepData.KOne_le_KO inf_le_right
  have hopen : IsOpen (PositivityTheory.LowerBoundConstant.Gx k e : Set (GL (Fin n) k)) := by
    unfold PositivityTheory.LowerBoundConstant.Gx
    exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne
  exact GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) (fun x hx => hle hx)

end GlobalTheory.CompanionTheory.MoyPrasad
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenGx
section
open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

namespace GlobalTheory.CompanionTheory.MoyPrasad

theorem isOpen_Gx (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) :
    IsOpen (Gx k e : Set (GL (Fin n) k)) := by
  unfold PositivityTheory.LowerBoundConstant.Gx
  exact Subgroup.isOpen_mono le_sup_left GlobalTheory.StepData.isOpen_KOne

end GlobalTheory.CompanionTheory.MoyPrasad
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_of_restrict_bijective : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃), (∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) → (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_res | exact GlobalTheory.CompanionTheory.KunGlue.kun_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_res <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModule
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem logAbs_eq_log_ideleModule (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ) :
    logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  have hinf : ∀ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (GroundTheory.Global.IdeleGroup.infinite_ne_zero s w)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), 0 < ‖(s : Ad E).2 v‖ := fun v =>
    norm_pos_iff.2 (GroundTheory.Global.IdeleGroup.finite_ne_zero s v)
  have hA : (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hinf w)
  have hB : (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖) ≠ 0 :=
    (GroundTheory.Global.IdeleGroup.finiteModule_pos s).ne'
  have e : (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) =
      (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq s
  rw [e, Real.log_mul hA hB, Real.log_prod (fun w _ => pow_ne_zero _ (hinf w)), Real.log_finprod hfin]
  unfold logAbs
  simp only [GlobalTheory.CompanionTheory.TorNorm.norm_cV, hm]
  rfl

end GlobalTheory.CompanionTheory.TorusCh

end
end

