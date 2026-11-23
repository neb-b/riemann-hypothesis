module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimitiveVectorExtendsHyperbolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderTwoPrimesAlmostAll
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0054
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberRankOneSetFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0521
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalCompactCoverByUnits
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0305
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0695
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatStabOfIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc

theorem JR_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : JR (F := F) R (hypOne J) = hypOne (JR (F := F) R J) := by
  ext i j
  simp only [JR, Matrix.map_apply]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j <;>
    simp [hypOne]

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem e0_mem_latV {d : ℕ} (M : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) :
    (e0 (Fv F v ⊗[F] E) M : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) ∈ latV b v := by
  rw [GoodTrans.mem_latV_iff b v O hO]
  intro a i
  refine Fin.cases ?_ (fun i => ?_) i
  · simpa [e0] using O.one_mem
  · simpa [e0] using O.zero_mem

theorem primV_subset (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F) : primV σ J b v ⊆ latV b v := by
  rintro y ⟨g, hg, rfl⟩
  exact (hg _).2 (e0_mem_latV M b v O hO)

theorem latStab_of_integral (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (g : GL (Fin M) (Fv F v ⊗[F] E)) (hg : g ∈ HR (Fv F v) σ J)
    (hgO : ∀ i j, (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) i j ∈ O)
    (hgiO : ∀ i j, ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) i j ∈ O) :
    latStab σ J b v ((⟨g, hg⟩ : HR (Fv F v) σ J) : HA (Fv F v) σ J) := by
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (a : Fin 1),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  intro X
  rw [GoodTrans.mem_latV_iff b v O hO, GoodTrans.mem_latV_iff b v O hO]
  constructor
  · intro hX a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
        ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact GoodTrans.mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
  · intro hX a i
    show (actW (Fv F v) σ J h' X a) i ∈ O
    rw [hact]
    exact GoodTrans.mulVec_mem O _ hgO _ (hX a) i

theorem cover_pt (σ : E →ₐ[F] E) {M d : ℕ} (J Ji : Matrix (Fin M) (Fin M) E) (hmul : J * Ji = 1)
    (hJs : ∀ i j, σ (J j i) = J i j)
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (O : Subring (Fv F v ⊗[F] E))
    (hO : ∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
      v.adicCompletionIntegers F)
    (hstab : ∀ y ∈ O, sigR (Fv F v) σ y ∈ O)
    (hss : ∀ y, sigR (Fv F v) σ (sigR (Fv F v) σ y) = y)
    (h2 : IsUnit (2 : O)) (hδ : ∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ)
    (π₁ π₂ : O) (hπ : ∀ P : Ideal O, P.IsMaximal → P = Ideal.span {π₁} ∨ P = Ideal.span {π₂})
    (hJO : ∀ i j, inclR (Fv F v) (J i j) ∈ O) (hJiO : ∀ i j, inclR (Fv F v) (Ji i j) ∈ O)
    (X : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) (hX : X ∈ latV b v)
    (hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0) :
    X ∈ primV σ J b v ∨ ∃ c : O, (c = π₁ ∨ c = π₂) ∧ ¬ IsUnit c ∧
      X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
        latV b v := by
  classical
  have hXO := (GoodTrans.mem_latV_iff b v O hO X).1 hX
  let x : Fin (M + 2) → O := fun i => ⟨X 0 i, hXO 0 i⟩
  by_cases hp : ∀ P : Ideal O, P.IsMaximal → ∃ i, x i ∉ P
  · left
    have hJR : JR (F := F) (Fv F v) (hypOne J) = hypOne (JR (F := F) (Fv F v) J) := JR_hypOne _ J
    have hmulT : JR (F := F) (Fv F v) J * JR (F := F) (Fv F v) Ji = 1 := by
      have := congrArg (RingHom.mapMatrix (inclR (Fv F v) (F := F) (E := E))) hmul
      rwa [map_mul, map_one] at this
    obtain ⟨g, hgU, hgx, hgO, hgiO⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimTrans.trans_orbit _ O (sigR (Fv F v) σ) hstab hss h2 hδ π₁ π₂ hπ M
      (JR (Fv F v) J) (JR (Fv F v) Ji) hJO hJiO hmulT
      (fun i j => by
        show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
        rw [← hJs i j]
        rfl)
      x hp (by rw [← hJR]; exact hg)
    have hgH : g ∈ HR (Fv F v) σ (hypOne J) := by
      show g ∈ UJ (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J))
      rw [hJR]; exact hgU
    refine ⟨(⟨g, hgH⟩ : HR (Fv F v) σ (hypOne J)),
      latStab_of_integral σ (hypOne J) b v O hO g hgH hgO hgiO, ?_⟩
    funext a
    rw [Fin.fin_one_eq_zero a]
    exact hgx
  · right
    push_neg at hp
    obtain ⟨P, hPm, hP⟩ := hp
    have aux : ∀ c : O, P = Ideal.span {c} → ¬ IsUnit c ∧
        X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * Y a i) ''
          latV b v := by
      intro c hc
      refine ⟨fun hu => hPm.ne_top (by rw [hc]; exact Ideal.span_singleton_eq_top.2 hu), ?_⟩
      have hdiv : ∀ i, ∃ y : O, y * c = x i := fun i => by
        have := hP i
        rw [hc] at this
        exact Ideal.mem_span_singleton'.1 this
      choose y hy using hdiv
      refine ⟨fun _ i => (y i : Fv F v ⊗[F] E), ?_, ?_⟩
      · rw [GoodTrans.mem_latV_iff b v O hO]
        exact fun _ i => (y i).2
      · funext a i
        rw [Fin.fin_one_eq_zero a]
        have := congrArg Subtype.val (hy i)
        simp only [Subring.coe_mul] at this
        show (c : Fv F v ⊗[F] E) * (y i : Fv F v ⊗[F] E) = X 0 i
        rw [mul_comm]
        exact this
    rcases hπ P hPm with h | h
    · exact ⟨π₁, Or.inl rfl, aux _ h⟩
    · exact ⟨π₂, Or.inr rfl, aux _ h⟩

end Place

theorem prim_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, primV σ J b v ⊆ latV b v ∧ ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ (hypOne J) 1 (coordW (Fv F v) b lam 1 (M + 2)) (coordHerm (Fv F v) σ b lam 1) m → ∀ h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b, m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) ≤ m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) (latV b v) := by
  intro F E _ _ _ _ _ σ h M J hJ hM d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  have hH := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ h M J hJ).1
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, _root_.GlobalTheory.CompanionTheory.SW.QuadMaxIdeal.maximal_ideals F E σ h d b,
    _root_.GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le F E σ h (M + 2) (hypOne J) hH (by omega) d b,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J⁻¹ i j)]
    with v hring h36 h37 hJv hJiv
  obtain ⟨O, hO, hstab, -, h2, hδ, -, -⟩ := hring
  obtain ⟨π₁, π₂, hπ, hu₁, hu₂⟩ := h36 O hO
  refine ⟨primV_subset σ J b v O hO, ?_⟩
  intro lam hlam m hm h₂
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq]
  have hmeas : MeasurableSet (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ h b 1 (M + 2) v
  set H := hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ with hHdef
  have hnull := hm.1 H
  set Z : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
    (gramR (Fv F v) σ (hypOne J) ⁻¹' {(H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E))} ∩
      {X | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ with hZ
  have hnull' : m H Z = 0 := hnull
  let Sc : O → Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) := fun c =>
    {X | ¬ IsUnit c ∧ X ∈ (fun (Y : Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) a i =>
      (c : Fv F v ⊗[F] E) * Y a i) '' latV b v}
  have hbd : ∀ c : O, IsUnit (c : Fv F v ⊗[F] E) → m H (Sc c) ≤
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
    intro c hc
    by_cases hu : IsUnit c
    · have : Sc c = ∅ := by ext X; simp [Sc, hu]
      rw [this, measure_empty]
      simp
    · exact (measure_mono fun X (hX : X ∈ Sc c) => hX.2).trans (h37 O hO lam hlam m hm h₂ c hu hc _ hmeas)
  have hcov : (latV b v : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E)) ⊆
      ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z := by
    intro X hX
    by_cases hXZ : X ∈ Z
    · exact Or.inr hXZ
    · left
      have hgr : gramR (Fv F v) σ (hypOne J) X = (H : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) := by
        simp only [hZ, Set.mem_compl_iff, not_not] at hXZ
        exact hXZ.1
      have hg : hform (sigR (Fv F v) σ) (JR (Fv F v) (hypOne J)) (X 0) (X 0) = 0 := by
        have := congrFun (congrFun hgr 0) 0
        refine this.trans ?_
        simp [hHdef, hermOf]
      rcases cover_pt σ J J⁻¹ (Matrix.mul_nonsing_inv _ hdet) hJ.1 b v O hO hstab hss h2 hδ π₁ π₂ hπ
        (fun i j => (hO _).2 (hJv i j)) (fun i j => (hO _).2 (hJiv i j)) X hX hg with hp | ⟨c, hc, hn, hi⟩
      · exact Or.inl (Or.inl hp)
      · rcases hc with rfl | rfl
        · exact Or.inl (Or.inr ⟨hn, hi⟩)
        · exact Or.inr ⟨hn, hi⟩
  have hN : ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) =
      ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc m H (latV b v) ≤ m H (((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) ∪ Z) := measure_mono hcov
    _ ≤ m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) + m H Z := measure_union_le _ _
    _ = m H ((primV σ J b v ∪ Sc π₁) ∪ Sc π₂) := by rw [hnull', add_zero]
    _ ≤ m H (primV σ J b v ∪ Sc π₁) + m H (Sc π₂) := measure_union_le _ _
    _ ≤ m H (primV σ J b v) + m H (Sc π₁) + m H (Sc π₂) := by gcongr; exact measure_union_le _ _
    _ ≤ m H (primV σ J b v) + ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) +
        ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      gcongr
      · exact hbd _ hu₁
      · exact hbd _ hu₂
    _ = m H (primV σ J b v) + ENNReal.ofReal (2 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m H (latV b v) := by
      rw [hN, add_mul, add_assoc]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneIsotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AvgZero

theorem avg_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 (0 : Fv F v), ∀ V : Set (Fv F v), MeasurableSet V → V ⊆ U → |(coordW (Fv F v) b lam 1 M (A ∩ {X | algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) ∈ V})).toReal - (m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) A).toReal * (lam V).toReal| ≤ ε * (lam V).toReal := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b v lam hlam m hm A hAc hAo
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, htr, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 1 M
  haveI : lam.IsAddHaarMeasure := hlam.1
  have hM1 : 1 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hQ : Continuous fun X : Fin 1 → Fin M → Fv F v ⊗[F] E =>
      algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0) :=
    continuous_const.mul (htr.comp ((a10 1 M J).matrix_elem 0 0))
  have hfam := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length F E σ hCM M J hJ d b v lam hlam m hm
  have hnull := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.NonFree.null_nonfree F E σ hCM M J hJ hM1 d b v lam hlam
  obtain ⟨ι, hι, P, u, hPc, hPo, hPZ, hsum, hcov⟩ :
      ∃ (ι : Type) (_ : Countable ι) (P : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) (u : ι → (Fv F v ⊗[F] E)ˣ),
        IsCompact P ∧ IsOpen P ∧ P ⊆ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ∧
        Summable (fun i => ‖Algebra.norm (Fv F v) (u i : Fv F v ⊗[F] E)‖₊ ^ (M - 1)) ∧
        A ∩ {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} ⊆
          ⋃ i, (fun (X : Fin 1 → Fin M → Fv F v ⊗[F] E) (p : Fin 1) (k : Fin M) =>
            (u i : Fv F v ⊗[F] E) * X p k) '' P := by
    by_cases hs : Nonempty (E →ₐ[F] Fv F v)
    · obtain ⟨τ⟩ := hs
      exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.CoverS.exists_cover F E σ hCM M hM2 v τ A hAc
    · exact _root_.GlobalTheory.CompanionTheory.WeilSiegel.SphereCover.coverF F E σ hCM M hM2 v
        (GlobalTheory.CompanionTheory.DictLoc.isField_tensor_of_no_algHom hCM.2.2.1 (not_nonempty_iff.1 hs)) A hAc
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreBound.compactOpen_mass_le _ _ _ lam _ _ _ hQ hfam P hPc hPo hPZ
  have hset := fun i => _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.Dil.dil_set F E σ hCM M v (u i) P hPc hPo hPZ
  have hb := fun i S hS => _root_.GlobalTheory.CompanionTheory.WeilSiegel.DilPush.push_dil F E σ hCM M J hJ hM1 d b v lam hlam P c hPo.measurableSet hc (u i) S hS
  have hmass := fun i => _root_.GlobalTheory.CompanionTheory.WeilSiegel.FibreMass.fibre_mass_le_of_pushforward _ _ _ lam _ _ _ hQ hfam _ (hset i).1 (hset i).2.1 (hset i).2.2 _ (hb i)
  have key := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity.density_of_summable_cover _ _ ι _ lam _ _ _ hQ hfam hnull A hAc hAo _ _ hset hcov (hsum.mul_left c) hb hmass 0
  have e0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀ = hermScal (Fv F v) σ 0 :=
    Subtype.ext (funext fun _ => funext fun _ => by
      show (1 : Fv F v) ⊗ₜ[F] (0 : E) = (0 : Fv F v) ⊗ₜ[F] (1 : E)
      simp)
  rw [e0]
  exact key

end GlobalTheory.CompanionTheory.SW.AvgZero
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurablePureAdelicFunction
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem measurable_pure_rv_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G)
    (hg : ∀ v ∈ S, Continuous (g v)) :
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hval : Measurable (Units.val : (AF F)ˣ → AF F) := comap_measurable _
  have hfst : Continuous (fun x : AF F => x.1) := continuous_fst
  have hev : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (fun x : AF F => x.2 v) := fun v =>
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have hc : Continuous (fun x : AF F => G x.1 * ∏ v ∈ S, g v (x.2 v)) :=
    (hG.comp hfst).mul (continuous_finsetProd _ fun v hv => (hg v hv).comp (hev v))
  have hopen : IsOpen {x : AF F | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F} :=
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S)).preimage continuous_snd
  have hh : Measurable (fun x : AF F => if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
      ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) :=
    Measurable.ite hopen.measurableSet (ENNReal.measurable_ofReal.comp hc.measurable)
      measurable_const
  have he : (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) = (fun x : AF F =>
      if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) ∘ Units.val :=
    funext fun a => GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply S G g a
  rw [he]
  exact hh.comp hval

end GlobalTheory.CompanionTheory.BasePsi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_adelic_function_formula : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | exact GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | (intros; apply GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateIsometry
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem rt_mem_l2Sub_and_inner_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N) (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  have key : ∀ z : Sm E N, ∀ hz : z ∈ squareIntegrableSmoothSubmoduleGL μ, ∃ h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ,
      l2Map μ (rt E N g z) = R (latticeGL E N) μ g (l2Map μ z) := by
    intro z hz
    have h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ := ((mem_l2Sub μ).1 hz).mul_right g
    refine ⟨h', ?_⟩
    rw [l2Map_apply μ h', l2Map_apply μ hz, right_translate_toL2]
    rfl
  obtain ⟨hx', ex⟩ := key x hx
  obtain ⟨hy', ey⟩ := key y hy
  refine ⟨hx', ?_⟩
  let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  rw [ex, ey]
  exact U.inner_map_map _ _

end GlobalTheory.CompanionTheory.FinDiscOrth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetLIntegralLeMulFd
section
noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace GlobalTheory.CompanionTheory.Growth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem size_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ C : Set (GA E n), IsCompact C → ∃ r, ∀ g ∈ C, logSize g ≤ r) ∧ (∀ g : GA E n, 0 ≤ logSize g) ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∀ g h : GA E n, logSize (g * h) ≤ logSize g + logSize h + c := by
  obtain ⟨h1, h2, -, c, hc⟩ := GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
    GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  exact ⟨h1, h2, max c 0, le_max_right _ _, fun g h =>
    (hc g h).trans (add_le_add le_rfl (le_max_left _ _))⟩

end GlobalTheory.CompanionTheory.Growth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SurjectiveReductionMaximalCompactStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_reduction_maximal_compact : ∀ (D : D7) (n : ℕ) (v : Pl D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ ρ : KAt D n v →* GL (Ix n) (Ov D v), (∀ k : KAt D n v, thU D n v τ (proj D.sp.cm.sig (Jst D n) v k) = inL (L := Lv D v) (ρ k)) ∧ Function.Surjective ρ ∧ ∀ ϖ : Ov D v, Irreducible ϖ → MeasurableSet (ρ ⁻¹' (Gam2 (n := n) ϖ : Set (GL (Ix n) (Ov D v)))) := by
  first | exact @GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho | exact GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho | (intros; apply GlobalTheory.CompanionTheory.Jp.RhoSplit.exists_rho <;> assumption)
end

