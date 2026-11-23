module

public import Mathlib
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0094
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalUnipotentRadicalSumZero
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.CuspSum

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem blk_unip (b : ι → Fin s) (c : Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    Formalism.IrreducibleCountingLemmas.TYPES.blk K b c (g : Matrix ι ι K) = 1 := by
  ext ⟨i, hi⟩ ⟨l, hl⟩
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply, Subtype.mk.injEq]
  exact hg.2 i l (hi.trans hl.symm)


omit [Fintype K] [DecidableEq K] [Fintype ι] in
theorem entry_of_blk (b : ι → Fin s) {M : Matrix ι ι K}
    (h : ∀ c, Formalism.IrreducibleCountingLemmas.TYPES.blk K b c M = 1) (i j : ι) (hij : b i = b j) :
    M i j = if i = j then 1 else 0 := by
  have := congrFun (congrFun (h (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  simpa only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.mk.injEq] using this

theorem unip_mul_mem (b : ι → Fin s) {g h : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) (hh : h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    g * h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨mul_mem hg.1 hh.1, entry_of_blk b fun c => ?_⟩
  rw [Units.val_mul, Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.1 hh.1.1, blk_unip b c hg, blk_unip b c hh,
    one_mul]

theorem unip_inv_mem (b : ι → Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) : g⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨inv_mem hg.1, entry_of_blk b fun c => ?_⟩
  have h := Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.2 hg.1.1
  rw [Units.inv_mul, blk_unip b c hg, mul_one] at h
  rw [← h]
  exact Matrix.submatrix_one _ Subtype.val_injective

open Classical in
theorem sum_rho_unip (τ : FDRep ℂ (GL ι K)) (hc : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ)
    (b : ι → Fin s) (hb : Function.Surjective b) (hs : 2 ≤ s) :
    (∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0) = 0 := by
  set P : Module.End ℂ τ := ∑ v : GL ι K, if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0
    with hP
  have hfix : ∀ a ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b, τ.ρ a * P = P := by
    intro a ha
    rw [hP, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft a)
      (fun v : GL ι K => if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b then τ.ρ v else 0)]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : a * v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b ↔ v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
      refine ⟨fun h => ?_, unip_mul_mem b ha⟩
      simpa using unip_mul_mem b (unip_inv_mem b ha) h
    simp only [Equiv.coe_mulLeft, hiff]
    split_ifs
    · rw [map_mul]
    · rw [mul_zero]
  refine LinearMap.ext fun w => ?_
  exact hc s b hb hs (P w) fun a ha => LinearMap.congr_fun (hfix a ha) w

theorem twoBlock_surjective {d j : ℕ} (hj : 1 ≤ j) (hjd : j < d) :
    Function.Surjective (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) := by
  intro c
  fin_cases c
  · exact ⟨⟨0, by omega⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]; omega⟩
  · exact ⟨⟨j, hjd⟩, by simp [Formalism.IrreducibleCountingLemmas.TYPES.twoBlock]⟩

theorem sum_character_translate :
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (τ : FDRep ℂ (GL (Fin d) K)), 1 ≤ j → j < d → IsCuspidal K τ → ∀ u : GL (Fin d) K,
    (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.character (u * v) else 0) = 0 := by
  intro K _ _ _ d j τ hj hjd hc u
  classical
  have h0 := sum_rho_unip τ hc (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) (twoBlock_surjective hj hjd) le_rfl
  have h1 : LinearMap.trace ℂ τ (τ.ρ u * ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then τ.ρ v else 0) = 0 := by
    rw [h0, mul_zero, map_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum] at h1
  refine Eq.trans (Finset.sum_congr rfl fun v _ => ?_) h1
  split_ifs
  · rw [FDRep.character, map_mul]
  · rw [mul_zero, map_zero]

end GlobalTheory.CompanionTheory.TyFin.CuspSum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.DensInt

theorem exists_cutoff (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by
  have h : ∀ k : ℕ, ∃ f : C(V, ℝ), Set.EqOn f 1 (compactCovering V k) ∧ Set.EqOn f 0 (∅ : Set V) ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    exists_continuous_one_zero_of_isCompact (isCompact_compactCovering V k) isClosed_empty
      (Set.disjoint_empty _)
  choose f h1 _ h3 h4 using h
  refine ⟨fun k => f k, fun k => (f k).continuous, h3, fun k x => h4 k x, fun x => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_mem_compactCovering x
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact h1 k (compactCovering_subset V hk hk₀)

theorem density_limit {V X Y : Type} [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsFiniteMeasureOnCompacts ν] (f : V → Y) (ι : X → Y)
    (B : Set X) (m : X → Measure V)
    (H : ∀ ψ : V → ℂ, Continuous ψ → HasCompactSupport ψ →
      HeckeCharacterZeroLocus.SiegelWeilU.IsContDensityOn μ f ι ν B ψ (fun S => ∫ x, ψ x ∂(m S)) ∧ ∀ S, Integrable ψ (m S))
    (φ : V → ℂ) (hφc : Continuous φ) (hφ : Integrable φ μ) (hφS : ∀ S ∈ B, Integrable φ (m S))
    (hD : ContinuousOn (fun S => ∫ x, ‖φ x‖ ∂(m S)) B) (K : Set X) (hK : IsCompact K) (hKB : K ⊆ B) :
    ∫ v in f ⁻¹' (ι '' K), φ v ∂μ = ∫ b in K, (∫ x, φ x ∂(m b)) ∂ν := by
  obtain ⟨χ, hχc, hχs, hχb, hχ1⟩ := exists_cutoff V
  set ψ : ℕ → V → ℂ := fun k x => φ x * (χ k x : ℂ) with hψ
  have hψc : ∀ k, Continuous (ψ k) := fun k =>
    hφc.mul (Complex.continuous_ofReal.comp (hχc k))
  have hψs : ∀ k, HasCompactSupport (ψ k) := fun k => by
    have : HasCompactSupport (fun x => (χ k x : ℂ)) := (hχs k).comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_left
  have hψn : ∀ k x, ‖ψ k x‖ ≤ ‖φ x‖ := fun k x => by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb k x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hχb k x).2
  have hψl : ∀ x, Filter.Tendsto (fun k => ψ k x) Filter.atTop (𝓝 (φ x)) := fun x => by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 x] with k hk
    simp [hψ, hk]
  have hmeas : ∀ k (ρ : Measure V), AEStronglyMeasurable (ψ k) ρ := fun k ρ =>
    (hψc k).aestronglyMeasurable

  have hL : Filter.Tendsto (fun k => ∫ v in f ⁻¹' (ι '' K), ψ k v ∂μ) Filter.atTop
      (𝓝 (∫ v in f ⁻¹' (ι '' K), φ v ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _) hφ.norm.integrableOn
      (fun k => Filter.Eventually.of_forall (hψn k)) (Filter.Eventually.of_forall hψl)

  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ S ∈ K, ‖∫ x, ‖φ x‖ ∂(m S)‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hD.mono hKB)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hR : Filter.Tendsto (fun k => ∫ b in K, (∫ x, ψ k x ∂(m b)) ∂ν) Filter.atTop
      (𝓝 (∫ b in K, (∫ x, φ x ∂(m b)) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact ((H _ (hψc k) (hψs k)).1.1.mono hKB).aestronglyMeasurable hKm
    · haveI : IsFiniteMeasure (ν.restrict K) := ⟨by simpa using hK.measure_lt_top (μ := ν)⟩
      exact integrable_const _
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      calc ‖∫ x, ψ k x ∂(m S)‖ ≤ ∫ x, ‖ψ k x‖ ∂(m S) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖φ x‖ ∂(m S) := integral_mono ((H _ (hψc k) (hψs k)).2 S).norm (hφS S (hKB hS)).norm (hψn k)
        _ ≤ ‖∫ x, ‖φ x‖ ∂(m S)‖ := Real.le_norm_self _
        _ ≤ C := hC S hS
    · refine (ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun S hS => ?_)
      exact tendsto_integral_of_dominated_convergence (fun x => ‖φ x‖) (fun k => hmeas k _)
        (hφS S (hKB hS)).norm (fun k => Filter.Eventually.of_forall (hψn k))
        (Filter.Eventually.of_forall hψl)
  refine tendsto_nhds_unique hL (hR.congr fun k => ?_)
  exact ((H _ (hψc k) (hψs k)).1.2 K hK hKB).symm


set_option maxHeartbeats 1000000 in
theorem density_identity_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)) (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ → (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) → ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S : HermR (Ainf F) σ n | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} → ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν := by
  intro F E _ _ _ _ _ σ hσ M J hJ n μ ν m hμ hν hfib φ hφc hφ hφS hD K hK hKB
  have hR : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, iLC, iSC, iT2, -, -, -, iB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Ainf F)
  haveI := iB n M
  haveI := iTR
  haveI := iLC
  haveI := iSC
  haveI := iT2
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ (Ainf F) n
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact density_limit μ ν (gramR (Ainf F) σ J) Subtype.val _ m
    (fun ψ h1 h2 => GlobalTheory.CompanionTheory.SW.GramDensity.isContDensityOn_gram F E σ hσ M J hJ (Ainf F) hR n μ ν m hμ hν hfib ψ h1 h2)
    φ hφc hφ hφS hD K hK hKB

end GlobalTheory.CompanionTheory.SW.DensInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOne
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens

theorem exists_congr_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε →
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det →
      ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  intro E _ τ q ε hR n T hT hdet
  have hinv : ∀ a : E, τ (τ a) = a := hR.inv
  have hq : 1 < q := hR.one_lt
  have hcard : Nat.card (Fin n → E) = q ^ (2 * n) := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin, hR.card, ← pow_mul]
  have hcnt := _root_.GlobalTheory.CompanionTheory.UnrDens.card_orthonormal_tuples E τ q ε hR n n le_rfl (Fin n → E) (HermSp.ofMatrix hinv T hT hdet) hcard
  have hε : ε = -1 ∨ ε = 1 := by
    rcases hR.eps with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hne : Nat.card {x : Fin n → Fin n → E // ∀ i j : Fin n,
      (HermSp.ofMatrix hinv T hT hdet).h (x i) (x j) = if i = j then 1 else 0} ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero, eq_comm, Finset.prod_eq_zero_iff] at hcnt
    obtain ⟨i, -, hi⟩ := hcnt
    have hk : n - (i : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt i.isLt
    rcases mul_eq_zero.mp hi with h | h
    · rw [div_eq_zero_iff] at h
      rcases h with h | h
      · have h' := pow_eq_zero_iff (n := 2 * (n - (i : ℕ))) (by omega) |>.mp h
        rw [Nat.cast_eq_zero] at h'
        omega
      · rw [Nat.cast_eq_zero] at h
        omega
    · rw [sub_eq_zero] at h
      have h2 := congrArg abs h
      rw [abs_one, abs_pow, abs_div, Nat.abs_cast] at h2
      have key : ∀ {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (e : ℤ) (k : ℕ),
          (e = -1 ∨ e = 1) → k ≠ 0 → (1 : F) ≠ (|(e : F)| / (q : F)) ^ k := by
        intro F _ _ _ e k he hk' hh
        have hqF : (1 : F) < q := by exact_mod_cast hq
        have habs : |(e : F)| = 1 := by
          rcases he with rfl | rfl <;> simp
        rw [habs] at hh
        have hlt : (1 / (q : F)) ^ k < 1 :=
          pow_lt_one₀ (by positivity) ((div_lt_one (by linarith)).mpr hqF) hk'
        linarith
      exact key ε _ hε hk h2
  obtain ⟨⟨x, hx⟩⟩ := (Nat.card_ne_zero.mp hne).1
  have hg : cT τ (Matrix.of fun a i => x i a) * T * (Matrix.of fun a i => x i a) = 1 := by
    ext i j
    rw [gram_apply hinv T hT hdet]
    show (HermSp.ofMatrix hinv T hT hdet).h (x j) (x i) = (1 : Matrix (Fin n) (Fin n) E) i j
    rw [hx j i, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  exact ⟨_, Matrix.isUnit_det_of_left_inverse hg, hg⟩

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLine
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Polynomial CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B
universe w w' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.LineUniv

theorem exists_line : ∀ {C : Type u} [Category.{v} C] (U : UF C) (P : ∀ ⦃T T' : C⦄, (T ⟶ T') → (T' ⟶ T') → Prop), (∀ T : C, ∃ (T₁ : C) (i : T ⟶ T₁) (η : U.U T₁), (∀ (T' : C) (φ : T ⟶ T') (a : U.U T'), ∃! ψ : T₁ ⟶ T', i ≫ ψ = φ ∧ U.map ψ η = a) ∧ ∀ g : T₁ ⟶ T₁, i ≫ g = i → U.map g η = U.q _ * η → P i g) → ∃ L : Line (𝟭 C) U, ∀ T, P (L.i.app T) (L.γ.app T) := by
  intro C _ U P h
  choose T₁ i η hu hP using h
  have hm : ∀ (T T' : C) (φ : T ⟶ T'), ∃ ψ : T₁ T ⟶ T₁ T', i T ≫ ψ = φ ≫ i T' ∧ U.map ψ (η T) = η T' :=
    fun T T' φ => (hu T _ (φ ≫ i T') (η T')).exists
  choose m hm1 hm2 using hm
  have hg : ∀ T, ∃ g : T₁ T ⟶ T₁ T, i T ≫ g = i T ∧ U.map g (η T) = U.q _ * η T :=
    fun T => (hu T _ (i T) _).exists
  choose g hg1 hg2 using hg
  have uniq : ∀ (T T' : C) (φ : T ⟶ T') (a : U.U T') (ψ ψ' : T₁ T ⟶ T'), i T ≫ ψ = φ → U.map ψ (η T) = a →
      i T ≫ ψ' = φ → U.map ψ' (η T) = a → ψ = ψ' :=
    fun T T' φ a ψ ψ' h1 h2 h3 h4 => (hu T T' φ a).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  let Ξ : C ⥤ C :=
    { obj := T₁
      map := fun {T T'} φ => m T T' φ
      map_id := fun T => uniq T _ (i T) (η T) _ _ (by rw [hm1, Category.id_comp]) (hm2 _ _ _)
        (Category.comp_id _) (U.map_id _ _)
      map_comp := fun {T T' T''} φ ψ => uniq T _ (φ ≫ ψ ≫ i T'') (η T'') _ _
        (by rw [hm1, Category.assoc]) (hm2 _ _ _)
        (by rw [← Category.assoc, hm1, Category.assoc, hm1])
        (by rw [U.map_comp, hm2, hm2]) }
  let iN : 𝟭 C ⟶ Ξ :=
    { app := i
      naturality := fun {T T'} φ => (hm1 T T' φ).symm }
  let γN : Ξ ⟶ Ξ :=
    { app := g
      naturality := fun {T T'} φ => uniq T _ (φ ≫ i T') (U.q _ * η T') _ _
        (by
          change i T ≫ m T T' φ ≫ g T' = _
          rw [← Category.assoc, hm1, Category.assoc, hg1])
        (by
          change U.map (m T T' φ ≫ g T') (η T) = _
          rw [U.map_comp, hm2, hg2])
        (by
          change i T ≫ g T ≫ m T T' φ = _
          rw [← Category.assoc, hg1, hm1])
        (by
          change U.map (g T ≫ m T T' φ) (η T) = _
          rw [U.map_comp, hg2, map_mul, hm2, U.map_q]) }
  refine ⟨{ Ξ := Ξ, i := iN, η := η, map_η := fun {T T'} φ => hm2 T T' φ, γ := γN, iγ := ?_, γη := hg2, univ := ?_ }, ?_⟩
  · ext T
    exact hg1 T
  · intro T t φ a
    exact hu T t φ a
  · intro T
    exact hP T (g T) (hg1 T) (hg2 T)

end GlobalTheory.CompanionTheory.LineUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCochainExtendOfSurjective
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeRepExact

universe v u

section Gen

variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {A : D ⥤ CommAlgCat.{0} R} (a b : IdF A)

def Rp {j : ℕ} (y : CH.Cn (sq a b) j) (z : CH.Cn (CH.modF A) j) : Prop :=
  ∀ s, (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) (show A.obj _ from z s)

variable {a b}

theorem sqMap_val {T T' : D} (φ : T ⟶ T') (w : sqM a b T) (x : A.obj T) (h : w.1 = Ideal.Quotient.mk (b.S T) x) :
    (sqMap a b φ w).1 = Ideal.Quotient.mk (b.S T') ((A.map φ).hom x) := by
  obtain ⟨w, hw⟩ := w
  obtain rfl : w = _ := h
  rfl

theorem Rp.d {j : ℕ} {y : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) :
    Rp a b (CH.d _ j y) (CH.d _ j z) := by
  intro s
  change (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • sqMap a b (toLast i s) (y (face i s)) : sqM a b _).1 =
    Ideal.Quotient.mk _ (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s)))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (y (face i s))).1 = _
  rw [sqMap_val _ _ _ (h (face i s))]

theorem Rp.sub {j : ℕ} {y y' : CH.Cn (sq a b) j} {z z' : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z') :
    Rp a b (y - y') (z - z') := by
  intro s
  change (show sqM a b _ from y s).1 - (show sqM a b _ from y' s).1 =
    Ideal.Quotient.mk _ ((show A.obj _ from z s) - (show A.obj _ from z' s))
  rw [map_sub, h s, h' s]

theorem Rp.unique {j : ℕ} {y y' : CH.Cn (sq a b) j} {z : CH.Cn (CH.modF A) j} (h : Rp a b y z) (h' : Rp a b y' z) :
    y = y' :=
  funext fun s => Subtype.ext ((h s).trans (h' s).symm)

theorem Rp.mem {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : Rp a b 0 z) (s) : z s ∈ b.S _ :=
  (Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).1 (h s).symm

theorem Rp.zero {j : ℕ} {z : CH.Cn (CH.modF A) j} (h : ∀ s, z s ∈ b.S _) : Rp a b 0 z := fun s =>
  ((Ideal.Quotient.eq_zero_iff_mem (a := (show A.obj _ from z s)) (I := b.S _)).2 (h s)).symm

theorem exists_rp {j : ℕ} (z : CH.Cn (CH.modF A) j) (hz : ∀ s, z s ∈ a.S _) : ∃ y, Rp a b y z :=
  ⟨fun s => sqMk a b (show A.obj _ from z s) (hz s), fun _ => rfl⟩

theorem exists_lift {j : ℕ} (y : CH.Cn (sq a b) j) : ∃ z : CH.Cn (CH.modF A) j, (∀ s, z s ∈ a.S _) ∧ Rp a b y z := by
  have key : ∀ s : ComposableArrows D j, ∃ x : A.obj (s.obj (Fin.last j)), x ∈ a.S _ ∧
      (show sqM a b _ from y s).1 = Ideal.Quotient.mk (b.S _) x := fun s => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 (show sqM a b _ from y s).2
    exact ⟨x, hx, e.symm⟩
  choose z hz hr using key
  exact ⟨z, hz, hr⟩

theorem exists_of_mem_B {n : ℕ} {w : CH.Cn (sq a b) n} {z : CH.Cn (CH.modF A) n} (hr : Rp a b w z)
    (hw : w ∈ (CH.cx (sq a b)).B n) : ∃ e : CH.Cn (CH.modF A) n, (∀ s, e s ∈ b.S _) ∧ CH.d _ n z = CH.d _ n e := by
  cases n with
  | zero =>
    have h0 : w = 0 := hw
    subst h0
    exact ⟨z, hr.mem, rfl⟩
  | succ n =>
    obtain ⟨t, rfl⟩ := hw
    obtain ⟨g, -, hg⟩ := exists_lift t
    have h0 : Rp a b 0 (z - CH.d _ n g) := by
      have := hr.sub hg.d
      rwa [sub_self] at this
    refine ⟨_, h0.mem, ?_⟩
    rw [map_sub, CH.d_d, sub_zero]

end Gen

section Cls

variable {R : Type} [CommRing R]

theorem sub_mem_B (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (e : K.cls x hx = K.cls y hy) :
    x - y ∈ K.B n :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).1 e

theorem cls_eq_of_sub_mem (K : Cx.{u} R) {n : ℕ} {x y : K.X n} (hx : K.d n x = 0) (hy : K.d n y = 0) (h : x - y ∈ K.B n) :
    K.cls x hx = K.cls y hy :=
  (Submodule.Quotient.eq ((K.B n).submoduleOf (K.Z n))).2 h

end Cls

section Res

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R}

theorem Rp.res (a b : IdF A) {U V : ObjectProperty C} (h : V ≤ U) {j : ℕ} {y : CH.Cn (sq (a.res U.ι) (b.res U.ι)) j}
    {z : CH.Cn (CH.modF (U.ι ⋙ A)) j} (hr : Rp _ _ y z) :
    Rp (a.res V.ι) (b.res V.ι) ((resU (sq a b) h).pullC j y) ((resU (CH.modF A) h).pullC j z) := fun s =>
  hr (s ⋙ ObjectProperty.ιOfLE h)

end Res

theorem exact_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (Φ : PDF R C) (Fil : ℤ → IdF Φ.A),
    IsFil Φ Fil → ∀ {U V : ObjectProperty C} (h : V ≤ U) (n : ℕ),
    Function.Surjective ((resU (gr Fil n) h).pull n) →
    ∀ (f : CH.Cn (CH.modF (V.ι ⋙ Φ.A)) n), (∀ σ, f σ ∈ (Fil n).S _) → (∀ σ, CH.d _ n f σ ∈ (Fil ((n : ℤ) + 1)).S _) →
    ∃ f' : CH.Cn (CH.modF (U.ι ⋙ Φ.A)) n, (∀ σ, f' σ ∈ (Fil n).S _) ∧ (∀ σ, CH.d _ n f' σ ∈ (Fil ((n : ℤ) + 1)).S _) ∧
      ∀ (x : HU (gr Fil ((n : ℤ) + 1)) V (n + 1)) (x' : HU (gr Fil ((n : ℤ) + 1)) U (n + 1)),
        Rep ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι) (CH.d _ n f) x →
        Rep ((Fil ((n : ℤ) + 1)).res U.ι) ((Fil ((n : ℤ) + 1 + 1)).res U.ι) (CH.d _ n f') x' →
        x = (resU (gr Fil ((n : ℤ) + 1)) h).pull (n + 1) x' := by
  intro R _ C _ Φ Fil hF U V h n hs f hf hdf
  obtain ⟨y, hy⟩ := exists_rp (a := (Fil n).res V.ι) (b := (Fil ((n : ℤ) + 1)).res V.ι) f hf
  have hdy : CH.d _ n y = 0 := hy.d.unique (Rp.zero hdf)
  obtain ⟨c', hc'⟩ := hs ((CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι))).cls y hdy)
  obtain ⟨⟨y', hy'⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c'
  obtain ⟨f', hf'a, hf'⟩ := exists_lift (a := (Fil n).res U.ι) (b := (Fil ((n : ℤ) + 1)).res U.ι)
    (show CH.Cn (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n from y')
  have hdy' : CH.d (sq ((Fil n).res U.ι) ((Fil ((n : ℤ) + 1)).res U.ι)) n y' = 0 := hy'
  have hz : CH.d (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)) n ((resU (gr Fil n) h).pullC n y') = 0 :=
    ((resU (gr Fil n) h).hom.mapZ n ⟨y', hy'⟩).2
  have hB := sub_mem_B (CH.cx (sq ((Fil n).res V.ι) ((Fil ((n : ℤ) + 1)).res V.ι)))
    (x := (resU (gr Fil n) h).pullC n y') (y := y) hz hdy hc'
  refine ⟨f', hf'a, ?_, ?_⟩
  · have := hf'.d
    rw [hdy'] at this
    exact this.mem
  · rintro x x' ⟨u, hu, rfl, hur⟩ ⟨u', hu', rfl, hur'⟩
    have hur1 : Rp _ _ u (CH.d _ n f) := hur
    have hur2 : Rp _ _ u' (CH.d _ n f') := hur'
    have hw := (Rp.res (Fil n) (Fil ((n : ℤ) + 1)) h hf').sub hy
    obtain ⟨e, he, hde⟩ := exists_of_mem_B hw hB
    obtain ⟨t, ht⟩ := exists_rp (a := (Fil ((n : ℤ) + 1)).res V.ι) (b := (Fil ((n : ℤ) + 1 + 1)).res V.ι) e he
    have h1 := (Rp.res (Fil ((n : ℤ) + 1)) (Fil ((n : ℤ) + 1 + 1)) h hur2).sub hur1
    have e1 : (resU (CH.modF Φ.A) h).pullC (n + 1) (CH.d (CH.modF (U.ι ⋙ Φ.A)) n f') =
        CH.d (CH.modF (V.ι ⋙ Φ.A)) n ((resU (CH.modF Φ.A) h).pullC n f') :=
      ((resU (CH.modF Φ.A) h).d_pullC n f').symm
    rw [e1, ← map_sub, hde] at h1
    have h2 := h1.unique ht.d
    have hz' : CH.d (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)) (n + 1)
        ((resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') = 0 :=
      ((resU (gr Fil ((n : ℤ) + 1)) h).hom.mapZ (n + 1) ⟨u', hu'⟩).2
    exact (cls_eq_of_sub_mem (CH.cx (sq ((Fil ((n : ℤ) + 1)).res V.ι) ((Fil ((n : ℤ) + 1 + 1)).res V.ι)))
      (x := (resU (gr Fil ((n : ℤ) + 1)) h).pullC (n + 1) u') (y := u) hz' hu ⟨t, h2.symm⟩).symm

end GlobalTheory.CompanionTheory.ConeRepExact
end

