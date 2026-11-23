module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0512
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0026
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructure
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem cjPre_haar (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R] (n : ℕ) (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure)
    (O : Subring (R ⊗[F] E)) (hOc : IsCompact (O : Set (R ⊗[F] E))) (hOo : IsOpen (O : Set (R ⊗[F] E)))
    (hOs : ∀ x ∈ O, sigR R σ x ∈ O) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (hgg : g * g' = 1)
    (hg : ∀ i j, g i j ∈ O) (hg' : ∀ i j, g' i j ∈ O) (Y : Set (HermR R σ n)) (hY : MeasurableSet Y) :
    MeasurableSet (cjPre R σ g Y) ∧ ν (cjPre R σ g Y) = ν Y := by
  obtain ⟨hTK, hLK, hSK, hTK2, hsc, -, -, -, hcl, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ R
  haveI := hTK
  haveI := hLK
  haveI := hSK
  haveI := hTK2
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hσ R n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  have hinv : ∀ x, sigR R σ (sigR R σ x) = x :=
    GlobalTheory.CompanionTheory.AvgFree.sigR_sigR R σ (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ)
  have hg2 : g' * g = 1 := mul_eq_one_comm.mp hgg
  let t : HermR R σ n ≃+ HermR R σ n :=
    { toFun := fun S => ⟨cjM R σ g S, cjM_mem R σ hinv g S S.2⟩
      invFun := fun S => ⟨cjM R σ g' S, cjM_mem R σ hinv g' S S.2⟩
      left_inv := fun S => Subtype.ext (by
        show cjM R σ g' (cjM R σ g S) = S
        rw [← cjM_mul, hgg, cjM_one])
      right_inv := fun S => Subtype.ext (by
        show cjM R σ g (cjM R σ g' S) = S
        rw [← cjM_mul, hg2, cjM_one])
      map_add' := fun S T => Subtype.ext (by
        simp only [cjM, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]) }
  have hcj : ∀ h : Matrix (Fin n) (Fin n) (R ⊗[F] E),
      Continuous fun S : HermR R σ n => cjM R σ h (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := fun h =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have htc : Continuous t := (hcj g).subtype_mk _
  have hts : Continuous t.symm := (hcj g').subtype_mk _
  have hpre : ∀ Z : Set (HermR R σ n), cjPre R σ g Z = t ⁻¹' Z := by
    intro Z
    ext y
    constructor
    · rintro ⟨z, hz, e⟩
      have : t y = z := Subtype.ext e
      show t y ∈ Z
      rwa [this]
    · intro h
      exact ⟨t y, h, rfl⟩

  have hent : ∀ (h : Matrix (Fin n) (Fin n) (R ⊗[F] E)), (∀ i j, h i j ∈ O) →
      ∀ y : Matrix (Fin n) (Fin n) (R ⊗[F] E), (∀ i j, y i j ∈ O) → ∀ i j, cjM R σ h y i j ∈ O := by
    intro h hh y hy i j
    simp only [cjM, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    exact O.sum_mem fun k _ => O.mul_mem (O.sum_mem fun m _ => O.mul_mem (hOs _ (hh _ _)) (hy _ _)) (hh _ _)
  let C : Set (HermR R σ n) := {y | ∀ i j, (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O}
  have hCv : C = Subtype.val ⁻¹'
      (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => (O : Set (R ⊗[F] E)) :
        Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := by
    ext y
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  have hCc : IsCompact C := by
    rw [hCv]
    exact (hcl n).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc)
  have hCo : IsOpen C := by
    have hval : Continuous fun y : HermR R σ n => (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      continuous_subtype_val
    have e : C = ⋂ i, ⋂ j, {y : HermR R σ n | (y : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j ∈ O} := by
      ext y
      simp only [C, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hOo.preimage ((continuous_apply_apply i j).comp hval)
  have hC0 : (0 : HermR R σ n) ∈ C := fun i j => O.zero_mem
  have htC : t ⁻¹' C = C := by
    ext y
    constructor
    · intro h
      have e : t.symm (t y) = y := t.symm_apply_apply y
      rw [← e]
      exact hent g' hg' _ h
    · intro h
      exact hent g hg _ h
  haveI hνt : (ν.map t).IsAddHaarMeasure := t.isAddHaarMeasure_map ν htc hts
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, ν.map t = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hCpos : ν C ≠ 0 := hCo.measure_ne_zero ν ⟨0, hC0⟩
  have hCfin : ν C ≠ ⊤ := hCc.measure_lt_top.ne
  have hc1 : c = 1 := by
    have h1 : ν.map t C = ν C := by
      rw [Measure.map_apply htc.measurable hCo.measurableSet, htC]
    rw [hc, Measure.coe_nnreal_smul_apply] at h1
    have h2 : (c : ℝ≥0∞) * ν C = 1 * ν C := by
      rw [one_mul]
      exact h1
    have h3 := (ENNReal.mul_left_inj hCpos hCfin).1 h2
    exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact htc.measurable hY
  · rw [hpre, ← Measure.map_apply htc.measurable hY, hc, hc1, one_smul]

end GlobalTheory.CompanionTheory.AvgFree.ElemHerm

theorem GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv O hOc hOo hOs n l a ha hl Y hY
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hlv.1
  obtain ⟨-, -, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  have he : ∀ (w : Fin n → Fv F v ⊗[F] E), (∀ i, w i ∈ O) → ∀ i j, eMat (Fv F v) l w i j ∈ O := by
    intro w hw i j
    simp only [eMat, Matrix.updateCol_apply, Matrix.one_apply]
    split_ifs
    · exact hw i
    · exact O.one_mem
    · exact O.zero_mem
  have hn : ∀ i, negCol (Fv F v) l a i ∈ O := by
    intro i
    simp only [negCol]
    split_ifs
    · exact O.one_mem
    · exact O.neg_mem (ha i)
  exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.cjPre_haar F E σ hσ (Fv F v) n _ (hH n) O hOc hOo hOs _ _
    (eMat_mul_negCol (Fv F v) l a hl) (he a ha) (he _ hn) Y hY
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandard
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero

theorem mass_dilated_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₀ d b v lam hlam m hm a e ha h1 h2
  have hloc := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have hnorm := GlobalTheory.CompanionTheory.SW.Dil.norm_natCast v a e ha h1 h2
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have ht : (a : Fv F v) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact (pow_ne_zero e (inv_ne_zero hq)) hnorm.symm
  have ht2 : (a : Fv F v) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hnorm2 : ‖(a : Fv F v) ^ 2‖ = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ ^ (2 * e) := by
    rw [norm_pow, hnorm, ← pow_mul, mul_comm]
  have hs1 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht e hnorm
  have hs2 := GlobalTheory.CompanionTheory.SW.Dil.scale_fv v lam _ ht2 (2 * e) hnorm2
  set q : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0) with hqdef
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E :=
    fun y => algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) * y with hf
  have hcast : algebraMap (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v) = (a : Fv F v ⊗[F] E) := map_natCast _ _
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk := GlobalTheory.CompanionTheory.SW.Dil.coordK_map (Fv F v) σ hσ b lam _ ht _ hs1
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => (a : Fv F v ⊗[F] E)
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    change IsUnit (a : Fv F v ⊗[F] E)
    rw [← hcast]
    exact ht.isUnit.map _
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf, hcast]
    rw [Subsingleton.elim p 0, mul_comm]
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S => (a ^ 2) • S
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) ((a : Fv F v) ^ 2) *
        (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    change (a ^ 2) • (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j = _
    rw [nsmul_eq_mul, map_pow, hcast]
    push_cast
    rfl
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    exact (continuous_nsmul (a ^ 2)).measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam _ ht2 _ hs2 τ hτm hτe
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g := by
    intro S
    ext i j
    have hsig : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := map_natCast _ _
    rw [hτe, map_pow, hcast, GlobalTheory.CompanionTheory.SW.Dil.cT_scalar _ _ hsig]
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    exact smul_zero _
  rw [hτs] at key
  have hA : MeasurableSet (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.SW.Growth.measurable_latV b v
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' (latV b v)) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : ((q ^ e) ^ 2) ^ M = q ^ (2 * e) * q ^ (e * (2 * M - 2)) := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
    have : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [this]
    ring
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have hq0 : ((q ^ (2 * e) : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    refine pow_ne_zero _ ?_
    rw [hqdef]
    exact_mod_cast hq
  have key3 := (ENNReal.mul_right_inj hq0 ENNReal.coe_ne_top).1 key2
  have hset : {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} =
      (fun X => rmul (Fv F v) X g) ⁻¹' (latV b v) := by
    rw [hrm]
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hf, hcast]
  have hof : ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) =
      ((q ^ (e * (2 * M - 2)) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  rw [hset, ← key3, hof]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowth
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf

theorem exists_mem_boxK_two_pow {K W : Type} [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) {n M : ℕ}
    {R : ℝ} (hR : 0 < R) (X : Fin n → Fin M → K) :
    ∃ j : ℕ, X ∈ boxK κ (fun _ _ => (2 : ℝ) ^ j * R) := by
  set B : ℝ := ∑ a, ∑ i, ∑ w, ‖κ (X a i) w‖ with hB
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (B / R) (one_lt_two : (1 : ℝ) < 2)
  refine ⟨j, fun a i w => ?_⟩
  have h1 : ‖κ (X a i) w‖ ≤ ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun w => ‖κ (X a i) w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have h2 : ∑ w, ‖κ (X a i) w‖ ≤ ∑ i, ∑ w, ‖κ (X a i) w‖ :=
    Finset.single_le_sum (f := fun i => ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  have h3 : ∑ i, ∑ w, ‖κ (X a i) w‖ ≤ B :=
    Finset.single_le_sum (f := fun a => ∑ i, ∑ w, ‖κ (X a i) w‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have h4 : B < (2 : ℝ) ^ j * R := (div_lt_iff₀ hR).1 hj
  linarith

theorem exists_large_ofReal_div_mul_le {A : ℝ} (hA : 0 ≤ A) {D ε : ℝ≥0∞} (hD : D ≠ ⊤) (hε : ε ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ ENNReal.ofReal (A / R) * D ≤ ε := by
  obtain ⟨δ, hδ0, hδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hε)
  have hδ0' : (0 : ℝ) < δ := by exact_mod_cast hδ0
  have hDr : 0 ≤ D.toReal := ENNReal.toReal_nonneg
  have hq : 0 ≤ A * D.toReal / δ := by positivity
  refine ⟨1 + A * D.toReal / δ, by linarith, ?_⟩
  have hRpos : 0 < 1 + A * D.toReal / δ := by linarith
  have hkey : A / (1 + A * D.toReal / δ) * D.toReal ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    have : (δ : ℝ) * (1 + A * D.toReal / δ) = δ + A * D.toReal := by
      field_simp
    rw [this]
    have : (0 : ℝ) ≤ δ := hδ0'.le
    linarith
  calc ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * D
      = ENNReal.ofReal (A / (1 + A * D.toReal / δ)) * ENNReal.ofReal D.toReal := by
        rw [ENNReal.ofReal_toReal hD]
    _ = ENNReal.ofReal (A / (1 + A * D.toReal / δ) * D.toReal) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ : ℝ) := ENNReal.ofReal_le_ofReal hkey
    _ = δ := ENNReal.ofReal_coe_nnreal
    _ ≤ ε := hδ.le

theorem tsum_geometric_half_mul (c d : ℝ≥0∞) :
    ∑' j : ℕ, c * (2⁻¹ : ℝ≥0∞) ^ j * d = c * 2 * d := by
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric,
    ENNReal.one_sub_inv_two, inv_inv]

theorem shell_real_identity {c R : ℝ} (hR : 0 < R) (e j : ℕ) :
    c / ((2 : ℝ) ^ j * R) ^ (e + 1) * ((2 : ℝ) ^ (j + 1) * R) ^ e
      = c * 2 ^ e / R * (1 / 2) ^ j := by
  have h2 : (2 : ℝ) ^ (j + 1) * R = 2 * ((2 : ℝ) ^ j * R) := by ring
  have key : ∀ P : ℝ, P ≠ 0 → c / P ^ (e + 1) * (2 * P) ^ e = c * 2 ^ e / P := by
    intro P hP
    rw [mul_pow, pow_succ]
    field_simp
  rw [h2, key _ (by positivity), one_div, inv_pow]
  field_simp

theorem tail_small_of_density :
    ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  intro K W _ _ κ n M H _ _ μ ν q C₀ hC₀ hden hq hbox φ hφ ε hε
  obtain ⟨e, he⟩ : ∃ e : ℕ, e = 2 * (M - n) * Fintype.card W * n := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := hφ (e + 1)
  have hA : 0 ≤ |C| * (2 : ℝ) ^ e := by positivity
  obtain ⟨R, hR1, hRε⟩ := exists_large_ofReal_div_mul_le hA
    (ENNReal.mul_ne_top (by simp) hC₀ : (2 : ℝ≥0∞) * C₀ ≠ ⊤) hε
  refine ⟨R, hR1, fun Y hY => ?_⟩
  have hR0 : 0 < R := by linarith
  let S : ℕ → Set (Fin n → Fin M → K) := fun j =>
    (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) \ boxK κ (fun _ _ => (2 : ℝ) ^ j * R)) ∩ q ⁻¹' Y
  have hcover : (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y ⊆ ⋃ j, S j := by
    rintro X ⟨hX, hXY⟩
    classical
    have hex := exists_mem_boxK_two_pow κ hR0 X
    have hne : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0] at this
      simp only [pow_zero, one_mul] at this
      exact hX this
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hne
    refine Set.mem_iUnion.2 ⟨j, ⟨?_, ?_⟩, hXY⟩
    · have := Nat.find_spec hex
      rw [hj] at this
      exact this
    · exact Nat.find_min hex (by omega)
  have hshell : ∀ j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
      ≤ ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
    intro j
    have hRj : 1 ≤ (2 : ℝ) ^ j * R := by
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      nlinarith
    have hRj0 : 0 < (2 : ℝ) ^ j * R := by linarith
    have hSm : MeasurableSet (S j) := ((hbox _).diff (hbox _)).inter (hq hY)
    have hpt : ∀ X ∈ S j, ‖φ X‖ₑ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) := by
      rintro X ⟨⟨-, hX⟩, -⟩
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ((hC _ hRj X hX).trans ?_)
      exact div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    have hmu : μ (S j) ≤ C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y := by
      have h1 := hden (fun _ _ => (2 : ℝ) ^ (j + 1) * R) (fun _ _ => by positivity) Y hY
      have h2 : μ (S j) ≤ μ (boxK κ (fun _ _ => (2 : ℝ) ^ (j + 1) * R) ∩ q ⁻¹' Y) :=
        measure_mono fun X hX => ⟨hX.1.1, hX.2⟩
      have h3 : (∏ a : Fin n, ∏ w : W, ENNReal.ofReal ((2 : ℝ) ^ (j + 1) * R) ^ (2 * (M - n)))
          = ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) := by
        rw [ENNReal.ofReal_pow (by positivity), he]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [h3] at h1
      exact h2.trans h1
    calc ∫⁻ X in S j, ‖φ X‖ₑ ∂μ
        ≤ ∫⁻ _ in S j, ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) ∂μ :=
          setLIntegral_mono' hSm hpt
      _ = ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) * μ (S j) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            (C₀ * ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e) * ν Y) := by gcongr
      _ = (ENNReal.ofReal (|C| / ((2 : ℝ) ^ j * R) ^ (e + 1)) *
            ENNReal.ofReal (((2 : ℝ) ^ (j + 1) * R) ^ e)) * (C₀ * ν Y) := by ring
      _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) := by
          rw [← ENNReal.ofReal_mul (by positivity), shell_real_identity hR0,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
          congr 3
          rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
          simp
  calc ∫⁻ X in (boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ
      ≤ ∫⁻ X in ⋃ j, S j, ‖φ X‖ₑ ∂μ := lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ X in S j, ‖φ X‖ₑ ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (|C| * 2 ^ e / R) * (2⁻¹ : ℝ≥0∞) ^ j * (C₀ * ν Y) :=
        ENNReal.tsum_le_tsum hshell
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * 2 * (C₀ * ν Y) := tsum_geometric_half_mul _ _
    _ = ENNReal.ofReal (|C| * 2 ^ e / R) * (2 * C₀) * ν Y := by ring
    _ ≤ ε * ν Y := by gcongr

end GlobalTheory.CompanionTheory.WhitFree.AvgInf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleSectionMemStandardOpenSubgroup
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem moduleSection_mem_standardOpenSubgroup {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (t : {r : ℝ // 0 < r}) :
    moduleSection w t ∈ standardOpenSubgroup F := by
  have h1 : ∀ s : {r : ℝ // 0 < r}, ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ((moduleSection w s : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro s v
    rw [← coe_finiteProj]
    simp [moduleSection, finiteProj_infiniteEmbedding]
  rw [mem_standardOpenSubgroup]
  intro v
  refine ⟨?_, ?_⟩
  · rw [h1]; exact one_mem _
  · rw [← map_inv, h1]; exact one_mem _

theorem differentiableOn_continuedLFunction :
    ∀ (F : Type) [Field F] [NumberField F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker →
        DifferentiableOn ℂ χ.continuedLFunction {1}ᶜ := by
  intro F _ _ χ hU
  by_cases h : ∃ τ : ℝ, ∀ x : IdeleGroup F,
      (χ.toIdele x : ℂ) = ((ideleModule F x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I)
  · obtain ⟨τ, hτ⟩ := h
    let w : InfinitePlace F := Classical.arbitrary _
    have hs : ∀ t : {x : ℝ // 0 < x}, χ.toIdele (moduleSection w t) = 1 := fun t ↦
      MonoidHom.mem_ker.1 (hU (moduleSection_mem_standardOpenSubgroup w t))
    have h0 : archExponent w χ = 0 := archExponent_unique w χ fun t ↦ by simp [hs t]
    have hτ0 : τ = 0 := (archExponent_eq_of_forall hτ w).symm.trans h0
    have hd := HeckeCharacter.differentiableOn_continuedLFunction_of_forall hτ
    simpa [hτ0] using hd
  · exact (χ.differentiable_continuedLFunction h).differentiableOn

end GlobalTheory.CompanionTheory.PartialZeta
end

