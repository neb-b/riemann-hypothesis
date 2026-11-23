module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAuxiliaryStatementB
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0429
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionBoundedLargeNorm
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

open GlobalTheory.CompanionTheory.SW.WBox (cK)

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R] {d : ℕ}
  (b : Module.Basis (Fin d) F E)

theorem cK_tmul_mul (r : R) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((r ⊗ₜ[F] (1 : E)) * y) k = r * cK R b y k := by
  have e : (r ⊗ₜ[F] (1 : E)) * y = r • y := by
    rw [Algebra.smul_def]
    rfl
  simp [cK, e]

theorem cK_nat_mul (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    cK R b ((N : R ⊗[F] E) * y) k = (N : R) * cK R b y k := by
  have e : (N : R ⊗[F] E) = (N : R) ⊗ₜ[F] (1 : E) := by
    exact (map_natCast (algebraMap R (R ⊗[F] E)) N).symm
  rw [e, cK_tmul_mul]

end Coord

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem scale_one (v : HeightOneSpectrum (𝓞 F)) (Q : Set (Fv F v)) (hQ : IsCompact Q) :
    ∃ N : ℕ, 0 < N ∧ ∀ t ∈ Q, (N : Fv F v) * t ∈ v.adicCompletionIntegers F := by
  set p : ℕ := Ideal.absNorm v.asIdeal with hp
  have hp0 : 0 < p := Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hp1 : Valued.v (p : Fv F v) < 1 := by
    have h1 : ((p : 𝓞 F)) ∈ v.asIdeal := by
      simpa [hp] using Ideal.absNorm_mem v.asIdeal
    have h2 := (v.valuation_lt_one_iff_mem (K := F) (p : 𝓞 F)).2 h1
    have h3 : (p : Fv F v) = algebraMap (𝓞 F) (Fv F v) (p : 𝓞 F) := (map_natCast _ p).symm
    rw [h3]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (p : 𝓞 F)).trans_lt h2
  have hO : IsOpen {t : Fv F v | Valued.v t ≤ 1} := Valued.isOpen_integer (Fv F v)
  have hopen : ∀ k : ℕ, IsOpen {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1} := fun k =>
    hO.preimage (continuous_const.mul continuous_id)
  obtain ⟨k, hk⟩ := hQ.elim_directed_cover (fun k : ℕ => {t : Fv F v | Valued.v ((p : Fv F v) ^ k * t) ≤ 1}) hopen
    (fun t _ => by
      by_cases ht : t = 0
      · exact Set.mem_iUnion.2 ⟨0, by simp [ht]⟩
      · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
        obtain ⟨n, hn⟩ := exists_pow_lt₀ hp1 (Units.mk0 _ (inv_ne_zero hvt))
        refine Set.mem_iUnion.2 ⟨n, ?_⟩
        simp only [Set.mem_setOf_eq, map_mul, map_pow]
        exact (mul_le_mul' hn.le le_rfl).trans (inv_mul_cancel₀ hvt).le)
    (directed_of_isDirected_le fun i j hij t ht => by
      simp only [Set.mem_setOf_eq] at ht ⊢
      rw [← Nat.sub_add_cancel hij, pow_add, mul_assoc, map_mul, map_pow]
      exact mul_le_one' (pow_le_one' hp1.le _) ht)
  exact ⟨p ^ k, pow_pos hp0 k, fun t ht => (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 (by
    rw [Nat.cast_pow]
    exact hk ht)⟩

theorem scale_lat [NumberField E] (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (K : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ Y ∈ K, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := by
  obtain ⟨_, _, _, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have hh := (_root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (Fv F v)).2.2.2.2.2.2.1 d b
  have hc : ∀ q : Fin 1 × Fin 1 × Fin d, Continuous fun Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E => cK (Fv F v) b (Y q.1 q.2.1) q.2.2 :=
    fun q => (continuous_apply q.2.2).comp (hh.continuous.comp (continuous_apply_apply q.1 q.2.1))
  choose n hn0 hn using fun q => scale_one v _ (hK.image (hc q))
  refine ⟨∏ q, n q, Finset.prod_pos fun q _ => hn0 q, fun Y hY a i k => ?_⟩
  change cK (Fv F v) b (((∏ q, n q : ℕ) : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  obtain ⟨c, hc'⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ (a, i, k))
  rw [hc']
  have h1 := hn (a, i, k) _ ⟨Y, hY, rfl⟩
  have e : ((n (a, i, k) * c : ℕ) : Fv F v) * cK (Fv F v) b (Y a i) k =
      (c : Fv F v) * ((n (a, i, k) : Fv F v) * cK (Fv F v) b (Y a i) k) := by
    push_cast; ring
  rw [e]
  exact mul_mem (natCast_mem _ c) h1

theorem nat_mul_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    {Y : Fin 1 → Fin 1 → Fv F v ⊗[F] E} (hY : Y ∈ latV b v) :
    (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun a i k => by
  change cK (Fv F v) b ((N : Fv F v ⊗[F] E) * Y a i) k ∈ _
  rw [cK_nat_mul]
  exact mul_mem (natCast_mem _ N) (hY a i k)

end Scale

theorem exists_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (hT : IsTest σ J b S φ A) :
    ∃ K : Set (Fin 1 → Fin 1 → AF F ⊗[F] E), IsCompact K ∧
      ∀ Y : Fin 1 → Fin 1 → AF F ⊗[F] E, (∀ v, projV v (projFin Y) ∈ A v) → projInf Y ∈ tsupport φ → Y ∈ K := by
  obtain ⟨hφc, hφs, hφ0, -, hAS, hAoff⟩ := hT
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 1
  obtain ⟨u1, u2⟩ := _root_.GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples F E σ hcm d b 1 1
  have hSc : ∀ v, ∃ N : ℕ, 0 < N ∧ (v ∈ S → ∀ Y ∈ A v, (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v) := fun v => by
    by_cases hv : v ∈ S
    · obtain ⟨N, h0, h1⟩ := scale_lat σ hcm b v (A v) (hAS v hv).1
      exact ⟨N, h0, fun _ => h1⟩
    · exact ⟨1, one_pos, fun h => absurd h hv⟩
  choose n hn0 hn using hSc
  set N1 : ℕ := ∏ v ∈ S, n v with hN1
  have hN1p : 0 < N1 := Finset.prod_pos fun v _ => hn0 v
  have hsc : ∀ v, ∀ Y ∈ A v, (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) ∈ latV b v := fun v Y hY => by
    by_cases hv : v ∈ S
    · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hv
      have h1 := nat_mul_latV b v c (hn v hv Y hY)
      have e : (fun a i => (N1 : Fv F v ⊗[F] E) * Y a i) = fun a i => (c : Fv F v ⊗[F] E) * ((n v : Fv F v ⊗[F] E) * Y a i) := by
        funext a i
        rw [hN1, hc]
        push_cast
        ring
      rw [e]
      exact h1
    · rw [hAoff v hv] at hY
      exact nat_mul_latV b v N1 hY
  obtain ⟨r1, hr1⟩ := (IsCompact.image hφs t9).bddAbove
  refine ⟨_, u1 N1 r1 hN1p, fun Y hY hs => ⟨fun v => hsc v _ (hY v), hr1 ⟨_, hs, rfl⟩⟩⟩

theorem mem_of_Psi_ne {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E))
    (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (h : Psi φ A Y ≠ 0) :
    (∀ v, projV v (projFin Y) ∈ A v) ∧ projInf Y ∈ tsupport φ := by
  unfold Psi at h
  by_cases h1 : ∀ v, projV v (projFin Y) ∈ A v
  · refine ⟨h1, subset_tsupport φ ?_⟩
    rw [Set.indicator_of_mem (by exact h1)] at h
    intro h2
    exact h (by simp [h2])
  · rw [Set.indicator_of_notMem (by exact h1)] at h
    exact absurd rfl h

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cont_f : Continuous fun Y : Fin 1 → Fin 1 → AF F ⊗[F] E => GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (Y 0 0) :=
    GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv.comp (continuous_apply_apply 0 0)

theorem hdiag (t : Eˣ) : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofE t) = IdeleGroup.diagonal E t := by
    apply Units.ext
    exact GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA (t : E)

theorem mod_mul (y : (AF F ⊗[F] E)ˣ) (t : Eˣ) : (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE t)) : ℝ) = (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E y) : ℝ) := by
  rw [map_mul, map_mul, hdiag, IdeleGroup.ideleModule_diagonal, mul_one]

theorem exists_term (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) (y : (AF F ⊗[F] E)ˣ)
    (h : Th φ A y ≠ 0) : ∃ X : Fin 1 → Fin 1 → E, X ≠ 0 ∧
      Psi φ A (fun a i => (y : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 := by
  unfold Th at h
  obtain ⟨X, hX⟩ := not_forall.1 (fun hall => h (ENNReal.tsum_eq_zero.2 hall))
  exact ⟨X.1, X.2, hX⟩

theorem entry_ne {X : Fin 1 → Fin 1 → E} (h : X ≠ 0) : X 0 0 ≠ 0 := fun h0 => h (by
  funext a i
  rw [Subsingleton.elim a 0, Subsingleton.elim i 0, h0]
  rfl)

theorem coe_eq (y : (AF F ⊗[F] E)ˣ) {X : Fin 1 → Fin 1 → E} (h : X 0 0 ≠ 0) :
    ((GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ h)) : IdeleGroup E) : AdeleRing (𝓞 E) E) =
      GroundTheory.BlockD.ThmBHecke.adeleEquiv F E ((y : AF F ⊗[F] E) * inclR (AF F) (X 0 0)) := rfl
end

theorem th_eq_zero_of_large_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∃ R : ℝ, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → R < md n → Th φ A y = 0 := by
  intro F E _ _ _ _ _ σ hcm J hJ d b S φ A hT
  obtain ⟨K, hK, hmem⟩ := exists_compact σ hcm J b S φ A hT
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.CompanionTheory.IdeleModBdd.ideleModule_bounded_on_compact E _ (hK.image (cont_f (F := F) (E := E)))
  refine ⟨R, fun y n hn hlt => ?_⟩
  by_contra hne
  obtain ⟨X, hX0, hX⟩ := exists_term φ A y hne
  obtain ⟨h1, h2⟩ := mem_of_Psi_ne φ A _ hX
  have hYK := hmem _ h1 h2
  have ht := entry_ne hX0
  have hle := hR (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (y * ofE (Units.mk0 _ ht)))
    (by rw [coe_eq]; exact ⟨_, hYK, rfl⟩)
  rw [mod_mul, _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.ideleModule_eq_md_of_isNm F E σ hcm y n hn] at hle
  exact absurd hle (not_le.2 hlt)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSecondBlockRestriction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.SliceR

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

def levelTwo (K : Subgroup (GL (Fin (r + s)) (Af E))) (t : GL (Fin (r + s)) (Af E)) :
    Subgroup (GL (Fin s) (Af E)) :=
  K.comap ((MulAut.conj t⁻¹).toMonoidHom.comp (Slice2.lev2 (Af E) r s))

theorem mem_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))} {t : GL (Fin (r + s)) (Af E)}
    {u : GL (Fin s) (Af E)} : u ∈ levelTwo K t ↔ t⁻¹ * lev (Af E) r s (1, u) * t ∈ K := by
  simp [levelTwo, MulAut.conj_apply, Slice2.lev2]

theorem isOpen_levelTwo {K : Subgroup (GL (Fin (r + s)) (Af E))}
    (hK : IsOpen (K : Set (GL (Fin (r + s)) (Af E)))) (t : GL (Fin (r + s)) (Af E)) :
    IsOpen (levelTwo K t : Set (GL (Fin s) (Af E))) := by
  have hc : Continuous fun u : GL (Fin s) (Af E) => t⁻¹ * Slice2.lev2 (Af E) r s u * t :=
    (continuous_const.mul Slice2.continuous_lev2).mul continuous_const
  convert hK.preimage hc using 1
  ext u
  exact mem_levelTwo

def sliceMap (k : Kinf E (r + s)) : (Kinf E (r + s) → ℂ) →ₗ[ℂ] (Kinf E s → ℂ) :=
  LinearMap.funLeft ℂ ℂ fun κ => Slice2.levK E r s κ * k

theorem lev_finGL_right (x : GA E r) (g : GA E s) (u : GL (Fin s) (Af E)) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t =
      lev (Ad E) r s (x, g) * cf (r + s) k t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
  have hY : finGL E (r + s) (lev (Af E) r s (1, u)) * finGL E (r + s) t =
      finGL E (r + s) t * finGL E (r + s) (t⁻¹ * lev (Af E) r s (1, u) * t) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  rw [Slice2.lev_mul_right, Slice2.lev_finGL_one, cf, mul_assoc (lev (Ad E) r s (x, g)),
    ← mul_assoc (finGL E (r + s) _), ← infGL_comm, mul_assoc (infGL E (r + s) _), hY]
  simp only [mul_assoc]

theorem lev_infGL_right (x : GA E r) (g : GA E s) (κ : Kinf E s) (k : Kinf E (r + s))
    (t : GL (Fin (r + s)) (Af E)) :
    lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t =
      (lev (Ad E) r s (x, g) * finGL E (r + s) t) *
        infGL E (r + s) (Unitary.toUnits (Slice2.levK E r s κ * k)) := by
  rw [Slice2.lev_mul_right, Slice2.lev_infGL_one, cf, map_mul Unitary.toUnits, Slice2.toUnits_levK,
    map_mul (infGL E (r + s)), mul_assoc (lev (Ad E) r s (x, g)) (finGL E (r + s) t), infGL_comm _ t]
  rw [mul_assoc (lev (Ad E) r s (x, g)) (infGL E (r + s) _), ← mul_assoc (infGL E (r + s) _) (finGL E (r + s) t),
    infGL_comm]
  simp only [mul_assoc]

end GlobalTheory.CompanionTheory.LimV.SliceR

theorem GlobalTheory.CompanionTheory.LimV.SliceR.slice_right : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (k : Kinf E (r + s)) (t : GL (Fin (r + s)) (Af E)) (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → ∃ (K₂ : Subgroup (GL (Fin s) (Af E))) (W₂ : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K₂ : Set (GL (Fin s) (Af E))) ∧ FiniteDimensional ℂ W₂ ∧ ∀ f ∈ typeF K W, ∀ x : GA E r, (fun y : GA E s => f (lev (Ad E) r s (x, y) * cf (r + s) k t)) ∈ typeF K₂ W₂ := by
  intro E _ _ _ r s k t K W hK hW
  refine ⟨SliceR.levelTwo K t, W.map (SliceR.sliceMap k), SliceR.isOpen_levelTwo hK t, inferInstance,
    fun f hf x => ⟨fun u hu g => ?_, fun g => ?_⟩⟩
  · change f (lev (Ad E) r s (x, g * finGL E s u) * cf (r + s) k t) = f (lev (Ad E) r s (x, g) * cf (r + s) k t)
    rw [SliceR.lev_finGL_right]
    exact hf.1 _ (SliceR.mem_levelTwo.1 hu) _
  · refine ⟨_, hf.2 (lev (Ad E) r s (x, g) * finGL E (r + s) t), ?_⟩
    funext κ
    change f _ = f (lev (Ad E) r s (x, g * infGL E s (Unitary.toUnits κ)) * cf (r + s) k t)
    rw [SliceR.lev_infGL_right]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariant
section
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.WeilLaw

theorem weil_parabolic_law : ∀ (D : D7) (n : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (V : HSp D)
    (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)),
    IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n),
    ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
      (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n ψ χ θ V μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ∀ a : Mx D n n, ((0 : Mx D V.rank n) ⬝ a : Mx D V.rank n) = 0 := fun a => Matrix.zero_mul a
  have z2 : StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by rw [StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by
    rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.CompanionTheory.WeilLaw
end

