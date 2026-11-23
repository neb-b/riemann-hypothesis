module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleLocalGlobalProperties
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PrimitiveVectorLatticeRescaleAlmostAll
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalPrimitiveVectorCompactRescale
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanPrimitiveVectorCompactRescale
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.AutomorphicTheory.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicPrimitiveVectorCompactRescale
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PrimA

def phiInf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    AF F ⊗[F] E →+* Ainf F ⊗[F] E :=
  (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

def phiV (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : AF F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom.comp
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

theorem unimodular_compact_mod_units : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ),
    ∃ Ω : Set (Fin 1 → Fin M → AF F ⊗[F] E), IsCompact Ω ∧
      ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ z : Fin M → AF F ⊗[F] E, z ⬝ᵥ y 0 = 1) →
        ∃ (a : (AF F ⊗[F] E)ˣ) (z : Fin 1 → Fin M → AF F ⊗[F] E),
          (a : AF F ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : AF F ⊗[F] E) • y) 0 = 1 := by
  intro F E _ _ _ _ _ σ hCM M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  obtain ⟨-, almM, glueM, cptM⟩ := _root_.GlobalTheory.CompanionTheory.SW.Glue.glue_main F E σ hCM _ b 1 M
  obtain ⟨ext1, alm1, glue1, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Glue.glue_main F E σ hCM _ b 1 1
  obtain ⟨Ωi, hΩi, hi⟩ := _root_.GlobalTheory.CompanionTheory.SW.PrimInf.unimodular_mod_units_inf F E σ hCM M
  choose Ωv hΩv hv using _root_.GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units F E σ hCM M
  obtain ⟨good, hgoodEv, hgood⟩ : ∃ good : HeightOneSpectrum (𝓞 F) → Prop,
      (∀ᶠ v in Filter.cofinite, good v) ∧ ∀ v, good v →
        ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) →
          ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E),
            (a : Fv F v ⊗[F] E) • y ∈ latV b v ∧ z ∈ latV b v ∧
              z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 :=
    ⟨_, _root_.GlobalTheory.CompanionTheory.SW.PrimGood.exists_primitive F E σ hCM _ b M, fun _ h => h⟩
  classical
  obtain ⟨Cv, hCg, hCb⟩ : ∃ Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E),
      (∀ v, good v → Cv v = latV b v) ∧ (∀ v, ¬ good v → Cv v = Ωv v) :=
    ⟨fun v => if good v then latV b v else Ωv v, fun v h => if_pos h, fun v h => if_neg h⟩
  have hCcpt : ∀ v, IsCompact (Cv v) := by
    intro v
    by_cases h : good v
    · rw [hCg v h]; exact (_root_.GlobalTheory.CompanionTheory.SW.LatCpt.latV_compact_open F E σ hCM _ b 1 M v).1
    · rw [hCb v h]; exact hΩv v
  have hClat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v :=
    hgoodEv.mono fun v h => (hCg v h).le
  have extK : ∀ x y : AF F ⊗[F] E, phiInf F E x = phiInf F E y →
      (∀ v, phiV F E v x = phiV F E v y) → x = y := by
    intro x y h1 h2
    have := ext1 (fun _ _ => x) (fun _ _ => y) (by funext a i; exact h1)
      (fun v => by funext a i; exact h2 v)
    exact congrFun (congrFun this 0) 0
  have oneLat : ∀ᶠ v in Filter.cofinite,
      (fun _ _ => 1 : Fin 1 → Fin 1 → Fv F v ⊗[F] E) ∈ latV b v := by
    refine (alm1 (fun _ _ => 1)).mono fun v hv => ?_
    have e : (projV v (projFin (fun _ _ => (1 : AF F ⊗[F] E))) : Fin 1 → Fin 1 → Fv F v ⊗[F] E) =
        fun _ _ => 1 := by
      funext a i; exact map_one (phiV F E v)
    rwa [e] at hv
  have glueK : ∀ (xi : Ainf F ⊗[F] E) (xv : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v ⊗[F] E),
      (∀ᶠ v in Filter.cofinite, xv v = 1) →
      ∃ x : AF F ⊗[F] E, phiInf F E x = xi ∧ ∀ v, phiV F E v x = xv v := by
    intro xi xv h
    obtain ⟨X, h1, h2⟩ := glue1 (fun _ _ => xi) (fun v _ _ => xv v) ((h.and oneLat).mono fun v hv => by
      have e : (fun _ _ => xv v : Fin 1 → Fin 1 → Fv F v ⊗[F] E) = fun _ _ => 1 := by
        funext a i; exact hv.1
      rw [e]; exact hv.2)
    exact ⟨X 0 0, congrFun (congrFun h1 0) 0, fun v => congrFun (congrFun (h2 v) 0) 0⟩
  refine ⟨{X | projInf X ∈ Ωi ∧ ∀ v, projV v (projFin X) ∈ Cv v}, cptM Ωi Cv hΩi hCcpt hClat, ?_⟩
  rintro y ⟨z₀, hz₀⟩
  have hzi : (fun i => phiInf F E (z₀ i)) ⬝ᵥ projInf y 0 = 1 := by
    have := congrArg (phiInf F E) hz₀
    rw [map_one, RingHom.map_dotProduct] at this
    exact this
  obtain ⟨ai, zi, hai, hzi', hidi⟩ := hi (projInf y) ⟨_, hzi⟩
  have hzv : ∀ v, (fun i => phiV F E v (z₀ i)) ⬝ᵥ projV v (projFin y) 0 = 1 := by
    intro v
    have := congrArg (phiV F E v) hz₀
    rw [map_one, RingHom.map_dotProduct] at this
    exact this
  have loc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E),
      (a : Fv F v ⊗[F] E) • projV v (projFin y) ∈ Cv v ∧ z ∈ Cv v ∧
        z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • projV v (projFin y)) 0 = 1 ∧
        (good v → projV v (projFin y) ∈ latV b v →
          (fun _ i => phiV F E v (z₀ i) : Fin 1 → Fin M → Fv F v ⊗[F] E) ∈ latV b v → a = 1) := by
    intro v
    by_cases hg : good v
    · by_cases hy : projV v (projFin y) ∈ latV b v ∧
          (fun _ i => phiV F E v (z₀ i) : Fin 1 → Fin M → Fv F v ⊗[F] E) ∈ latV b v
      · refine ⟨1, fun _ i => phiV F E v (z₀ i), ?_, ?_, ?_, fun _ _ _ => rfl⟩
        · rw [hCg v hg, Units.val_one, one_smul]; exact hy.1
        · rw [hCg v hg]; exact hy.2
        · rw [Units.val_one, one_smul]; exact hzv v
      · obtain ⟨a, z, h1, h2, h3⟩ := hgood v hg _ ⟨_, hzv v⟩
        refine ⟨a, z, ?_, ?_, h3, fun _ h h' => absurd ⟨h, h'⟩ hy⟩
        · rw [hCg v hg]; exact h1
        · rw [hCg v hg]; exact h2
    · obtain ⟨a, z, h1, h2, h3⟩ := hv v _ ⟨_, hzv v⟩
      refine ⟨a, z, ?_, ?_, h3, fun h => absurd h hg⟩
      · rw [hCb v hg]; exact h1
      · rw [hCb v hg]; exact h2
  choose av zv hav hzv' hidv ha1 using loc
  have ae1 : ∀ᶠ v in Filter.cofinite, av v = 1 := by
    filter_upwards [hgoodEv, almM y, almM (fun _ i => z₀ i)] with v h1 h2 h3
    exact ha1 v h1 h2 h3
  obtain ⟨a, ha_i, ha_v⟩ := glueK (ai : Ainf F ⊗[F] E) (fun v => (av v : Fv F v ⊗[F] E))
    (ae1.mono fun v h => by simp [h])
  obtain ⟨a', ha'_i, ha'_v⟩ := glueK ((ai⁻¹ : (Ainf F ⊗[F] E)ˣ) : Ainf F ⊗[F] E)
    (fun v => (((av v)⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E))
    (ae1.mono fun v h => by simp [h])
  have haa : a * a' = 1 := by
    refine extK _ _ ?_ fun v => ?_
    · rw [map_mul, map_one, ha_i, ha'_i, Units.mul_inv]
    · rw [map_mul, map_one, ha_v, ha'_v, Units.mul_inv]
  obtain ⟨Z, hZi, hZv⟩ := glueM zi zv (hgoodEv.mono fun v h => by
    have := hzv' v
    rwa [hCg v h] at this)
  have eI : projInf ((a : AF F ⊗[F] E) • y) = (ai : Ainf F ⊗[F] E) • projInf y := by
    funext p i
    show phiInf F E (a * y p i) = (ai : Ainf F ⊗[F] E) * phiInf F E (y p i)
    rw [map_mul, ha_i]
  have eV : ∀ v, projV v (projFin ((a : AF F ⊗[F] E) • y)) =
      (av v : Fv F v ⊗[F] E) • projV v (projFin y) := by
    intro v
    funext p i
    show phiV F E v (a * y p i) = (av v : Fv F v ⊗[F] E) * phiV F E v (y p i)
    rw [map_mul, ha_v]
  refine ⟨⟨a, a', haa, by rw [mul_comm]; exact haa⟩, Z, ⟨?_, fun v => ?_⟩, ⟨?_, fun v => ?_⟩, ?_⟩
  · show projInf ((a : AF F ⊗[F] E) • y) ∈ Ωi
    rw [eI]; exact hai
  · show projV v (projFin ((a : AF F ⊗[F] E) • y)) ∈ Cv v
    rw [eV]; exact hav v
  · rw [hZi]; exact hzi'
  · rw [hZv]; exact hzv' v
  · show Z 0 ⬝ᵥ ((a : AF F ⊗[F] E) • y) 0 = 1
    refine extK _ _ ?_ fun v => ?_
    · rw [map_one, RingHom.map_dotProduct]
      have e1 : (phiInf F E ∘ Z 0) = zi 0 := by
        funext i; exact congrFun (congrFun hZi 0) i
      have e2 : (phiInf F E ∘ ((a : AF F ⊗[F] E) • y) 0) = ((ai : Ainf F ⊗[F] E) • projInf y) 0 := by
        funext i; exact congrFun (congrFun eI 0) i
      rw [e1, e2]; exact hidi
    · rw [map_one, RingHom.map_dotProduct]
      have e1 : (phiV F E v ∘ Z 0) = zv v 0 := by
        funext i; exact congrFun (congrFun (hZv v) 0) i
      have e2 : (phiV F E v ∘ ((a : AF F ⊗[F] E) • y) 0) =
          ((av v : Fv F v ⊗[F] E) • projV v (projFin y)) 0 := by
        funext i; exact congrFun (congrFun (eV v) 0) i
      rw [e1, e2]; exact hidv v

end GlobalTheory.CompanionTheory.SW.PrimA
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DualLatticeMembershipTrace
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem Bf_mulVec_toA {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι F) (y : ι → F) : Bf B *ᵥ toA y = toA (B *ᵥ y) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) B y i).symm

theorem trace_int_of_basis {F : Type} [Field F] [NumberField F]
    (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ) (c : F)
    (h : ∀ v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * c) = m) (r : 𝓞 F) :
    ∃ n : ℤ, Algebra.trace ℚ F ((N : F) * c * (r : F)) = n := by
  choose m hm using h
  have hr : (r : F) = ∑ v, ((b.repr r v : ℤ) : F) * (b v : F) := by
    conv_lhs => rw [← b.sum_repr r]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  refine ⟨∑ v, b.repr r v * m v, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hr, Finset.mul_sum, map_sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : (N : F) * c * (((b.repr r v : ℤ) : F) * (b v : F)) =
      (((b.repr r v : ℤ) : ℚ) * (N : ℚ)) • ((b v : F) * c) := by
    rw [Algebra.smul_def]
    simp only [eq_ratCast, Rat.cast_mul, Rat.cast_intCast, Rat.cast_natCast]
    ring
  rw [e, map_smul, smul_eq_mul, mul_assoc, hm v]

theorem toA_mem_perp_latN_iff : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), 0 < N → ∀ y : ι → F, toA y ∈ perp (chiB ψ (Bf B)) (latN F ι N : Set (ι → A F)) ↔ ∀ i v, ∃ m : ℤ, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m := by
  intro F _ _ ψ hψ ι _ _ B b N _ y
  obtain ⟨-, hall⟩ := GlobalTheory.T.standard_adelic_character F
  obtain ⟨-, -, hchar⟩ := hall ψ hψ
  have hBy := Bf_mulVec_toA B y
  constructor
  · intro h i v
    have h1 : ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 := by
      intro x hx
      have hmem : (Pi.single i ((N : A F) * x) : ι → A F) ∈ latN F ι N := by
        refine fun j => ?_
        by_cases hj : j = i
        · subst hj
          exact ⟨x, hx, by simp⟩
        · exact ⟨0, oh_zero, by simp [Pi.single_eq_of_ne hj]⟩
      have h2 : ψ ((Pi.single i ((N : A F) * x) : ι → A F) ⬝ᵥ (Bf B *ᵥ toA y)) = 1 := h _ hmem
      rw [hBy, single_dotProduct] at h2
      rw [← h2, map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
      congr 1
      simp only [toA]
      ring
    obtain ⟨n, hn⟩ := (hchar _).mp h1 (b v)
    refine ⟨n, ?_⟩
    rw [← hn]
    have e : (N : F) * (B *ᵥ y) i * (b v : F) = (N : ℚ) • ((b v : F) * (B *ᵥ y) i) := by
      rw [Algebra.smul_def]
      push_cast
      ring
    rw [e, map_smul, smul_eq_mul]
  · intro h x hx
    have h1 : ∀ i, ∀ x ∈ Oh F, ψ (algebraMap F (A F) ((N : F) * (B *ᵥ y) i) * x) = 1 :=
      fun i => (hchar _).mpr (trace_int_of_basis b N _ (h i))
    show ψ (x ⬝ᵥ (Bf B *ᵥ toA y)) = 1
    rw [hBy, dotProduct]
    have h2 : ∀ s : Finset ι, ψ (∑ i ∈ s, x i * toA (B *ᵥ y) i) = 1 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, AddChar.map_add_eq_mul, ih, mul_one]
        obtain ⟨x', hx', e⟩ := hx i
        rw [e, ← h1 i x' hx', map_mul (algebraMap F (A F)), map_natCast (algebraMap F (A F))]
        congr 1
        simp only [toA]
        ring
    exact h2 Finset.univ

end GlobalTheory.CompanionTheory.SW.ThW
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueIntegrable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaMean

theorem mean_thetaS_eq_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Measurable Φ → Integrable Φ (thetaMeas σ J μ 𝓕 S) → meanC μ 𝓕 (thetaS F E σ M J Φ S) = ∫ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.theta_int

end GlobalTheory.CompanionTheory.SW.ThetaMean
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelMeanValueNonnegative
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaLint

theorem theta_lint_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ X, Φ X ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.theta_lint

end GlobalTheory.CompanionTheory.SW.ThetaLint
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureIntegralFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.ThetaCnt

theorem lintegral_thetaMeas : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (n : ℕ) (S : Set (Fin n → Fin M → E)) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → ∫⁻ Y, Φ Y ∂(thetaMeas σ J μ 𝓕 S) = (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 S Φ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.thetacnt

end GlobalTheory.CompanionTheory.SW.ThetaCnt
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOperatorIntegralInvariance
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.FstarPer

theorem oh_mul {F : Type} [Field F] [NumberField F] {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) :
    x * y ∈ Oh F :=
  fun v => mul_mem (hx v) (hy v)

theorem continuous_qf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (h : A F) (B : Matrix ι ι (A F)) : Continuous (qf h B) := by
  unfold qf
  exact continuous_const.mul (continuous_id.dotProduct ((continuous_const (y := B)).matrix_mulVec continuous_id))

theorem fstar_periodic : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ ∧ ∀ y : A F, fstar ψ (hf F) (Bf B) (muF B lf) φ (y + (N : A F) * x) = fstar ψ (hf F) (Bf B) (muF B lf) φ y := by
  intro F _ _ _ _ lf _ _ ψ hψ ι _ _ M B ρ P _ φ hφ
  have hK : IsCompact (qf (hf F) (Bf B) '' tsupport φ) :=
    IsCompact.image hφ.2 (continuous_qf _ _)
  obtain ⟨N, hN, hNK⟩ := (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.2.2.2.2.1 _ hK
  have htriv := ((GlobalTheory.T.standard_adelic_character F).2 ψ hψ).2.1
  have key : ∀ x ∈ Oh F, opU ψ (hf F) (Bf B) ((N : A F) * x) φ = φ := by
    intro x hx
    funext u
    by_cases hu : u ∈ tsupport φ
    · have h1 := hNK _ (Set.mem_image_of_mem _ hu)
      have h2 : (N : A F) * x * qf (hf F) (Bf B) u ∈ Oh F := by
        have h3 := oh_mul hx h1
        have h4 : (N : A F) * x * qf (hf F) (Bf B) u = x * ((N : A F) * qf (hf F) (Bf B) u) := by
          ring
        rwa [h4]
      simp [opU, htriv _ h2]
    · have h0 : φ u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [opU, h0]
  refine ⟨N, hN, fun x hx => ⟨key x hx, fun y => ?_⟩⟩
  unfold fstar
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h5 := congrFun (key x hx) u
  simp only [opU] at h5 ⊢
  rw [add_mul, AddChar.map_add_eq_mul, mul_assoc, h5]

end GlobalTheory.CompanionTheory.SW.FstarPer
end
end

