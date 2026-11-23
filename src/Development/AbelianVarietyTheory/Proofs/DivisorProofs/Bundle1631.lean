module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnramifiedSkewSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1118
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1605
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
section
open NumberField

open scoped Pointwise

namespace GlobalTheory.VacRead

theorem mul_smul_eq_span_absNorm {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (h2 : Module.finrank ℚ K = 2) (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ 1) (I : Ideal (𝓞 K)) :
    I * (τ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} := by
  classical
  by_cases hI : I = ⊥
  · subst hI; simp
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hτx : τ • (I ^ h) = Ideal.span {τ • x} := by
    rw [hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = x * (τ • x) := by
    have hp : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = ∏ σ : K ≃ₐ[ℚ] K, σ • x := by
      apply RingOfIntegers.ext
      have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : K)
      rw [← Algebra.coe_norm_int] at h1
      change algebraMap (𝓞 K) K _ = algebraMap (𝓞 K) K _
      rw [map_prod, map_intCast]
      rw [map_intCast] at h1
      exact h1
    rw [hp, huniv, Finset.prod_pair (Ne.symm hτ), one_smul]
  have key : (I * (τ • I)) ^ h = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} ^ h := by
    rw [mul_pow, ← smul_pow', hx', ← hx', hτx, hx', Ideal.span_singleton_mul_span_singleton, ← hnorm,
      Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
    · conv_lhs => rw [h4]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h4]
      rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
  exact pow_left_injective hpos key

theorem hostConj_quadraticGenerator_eq_neg (D : Formalism.BasicNotions.D7) :
    D.host.conj (D.host.sqd) = -D.host.sqd :=
  D.host.conj_sqd

theorem conj_mul_cE_absNorm (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) :
    (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E,
      D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧
    (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E)
      {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨GlobalTheory.CurveLattice.finrank_hostK D⟩
  let τ : D.host.K ≃ₐ[ℚ] D.host.K := D.host.conj.restrictNormal D.host.K
  have hτ : ∀ k : D.host.K, ((τ k : D.host.K) : D.host.E) = D.host.conj (k : D.host.E) :=
    fun k => AlgEquiv.restrictNormal_commutes D.host.conj D.host.K k
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hs : D.host.sqd ∈ D.host.K :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have h2 := hτ ⟨_, hs⟩
    rw [h1, AlgEquiv.one_apply, hostConj_quadraticGenerator_eq_neg] at h2
    have h3 : D.host.sqd = 0 := by
      have : (2 : D.host.E) * D.host.sqd = 0 := by
        simp only at h2; linear_combination h2
      simpa using this
    have h4 := D.host.sqd_sq
    rw [h3] at h4
    have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
    exact hd (by simpa using h4.symm)
  have hI := mul_smul_eq_span_absNorm (GlobalTheory.CurveLattice.finrank_hostK D) τ hτ1 cc

  let iK : 𝓞 D.host.K →+* 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E)
  have hiK : ∀ k : 𝓞 D.host.K, ((iK k : 𝓞 D.host.E) : D.host.E) = ((k : D.host.K) : D.host.E) := fun k => rfl
  have hsm : ∀ k : 𝓞 D.host.K, (((τ • k : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((k : D.host.K) : D.host.E) :=
    fun k => hτ k
  set N : D.host.E := (Ideal.absNorm cc : D.host.E) with hN
  let M : Submodule (𝓞 D.host.E) D.host.E := Submodule.span (𝓞 D.host.E) {N}
  have hgen : ∀ c₁ ∈ cc, ∀ c₂ ∈ cc, D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) ∈ M := by
    intro c₁ h₁ c₂ h₂
    have hm : c₂ * (τ • c₁) ∈ cc * (τ • cc) := Ideal.mul_mem_mul h₂ (Ideal.smul_mem_pointwise_smul _ _ _ h₁)
    rw [hI, Ideal.mem_span_singleton'] at hm
    obtain ⟨k, hk⟩ := hm
    have hE : D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) = (iK k : D.host.E) * N := by
      rw [hiK, ← hsm, mul_comm, hN]
      have := congrArg (fun y : 𝓞 D.host.K => ((y : D.host.K) : D.host.E)) hk
      simp only [map_mul, map_natCast] at this
      push_cast at this ⊢
      rw [← this]
    rw [hE]
    exact Submodule.mem_span_singleton.mpr ⟨iK k, rfl⟩
  have hpart : ∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, D.host.conj α * β ∈ M := by
    intro α hα β hβ
    induction hα using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c₁, h₁, rfl⟩ := hx
      have hle : GlobalTheory.VacRead.cE D cc ≤ M.comap (LinearMap.mulLeft (𝓞 D.host.E) (D.host.conj ((c₁ : D.host.K) : D.host.E))) := by
        refine Submodule.span_le.mpr ?_
        rintro y ⟨c₂, h₂, rfl⟩
        exact hgen c₁ h₁ c₂ h₂
      exact hle hβ
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), add_mul]; exact M.add_mem hx hy
    | smul o x _ hx =>
      have : D.host.conj (o • x) * β = (RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) o) • (D.host.conj x * β) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
        rfl
      rw [this]
      exact M.smul_mem _ hx
  refine ⟨fun α hα β hβ => ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (hpart α hα β hβ)
    exact ⟨o, by rw [← ho, Algebra.smul_def, mul_comm]⟩
  · have hNK : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc * (τ • cc) := by
      rw [hI]; exact Ideal.mem_span_singleton_self _
    have hcoe : N = ((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      rw [hN]; push_cast; rfl
    rw [hcoe]
    refine Submodule.mul_induction_on hNK ?_ ?_
    · intro a ha b hb
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
      have hb' : b = τ • (τ⁻¹ • b) := by rw [smul_inv_smul]
      refine Submodule.subset_span ⟨((τ⁻¹ • b : 𝓞 D.host.K) : D.host.K), Submodule.subset_span ⟨_, hb, rfl⟩,
        ((a : D.host.K) : D.host.E), Submodule.subset_span ⟨a, ha, rfl⟩, ?_⟩
      conv_lhs => rw [hb']
      rw [← hsm]
      push_cast
      ring
    · intro x y hx hy
      push_cast
      exact Submodule.add_mem _ hx hy

end GlobalTheory.VacRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionConjugationPropertiesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertCompletionConjugation_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
  B.IsGood σ → ∀ {v : Pl (F := F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  (∀ x, GlobalTheory.InertBigCell.conjW σ hw (GlobalTheory.InertBigCell.conjW σ hw x) = x) ∧
  (∀ x ∈ w.adicCompletionIntegers E, GlobalTheory.InertBigCell.conjW σ hw x ∈ w.adicCompletionIntegers E) ∧
  (2 : w.adicCompletion E)⁻¹ ∈ w.adicCompletionIntegers E ∧
  (∀ e : E, GlobalTheory.InertBigCell.conjW σ hw (algebraMap E (w.adicCompletion E) e) = algebraMap E (w.adicCompletion E) (σ e)) := by
  first | exact @GlobalTheory.InertBigCell.conjW_props | exact GlobalTheory.InertBigCell.conjW_props | (intros; apply GlobalTheory.InertBigCell.conjW_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertCompletionToAdelesProperties
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBigCell

theorem iotaW_adelic_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w),
  Function.Injective (GlobalTheory.InertBigCell.iotaW hw) ∧
  (∀ x y, GlobalTheory.InertBigCell.iotaW hw (x * y) = GlobalTheory.InertBigCell.iotaW hw x * GlobalTheory.InertBigCell.iotaW hw y) ∧
  GlobalTheory.InertBigCell.iotaW hw 1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
  (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, GlobalTheory.InertBigCell.iotaW hw x = z) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (GlobalTheory.InertBigCell.conjW σ hw x) = cA σ (GlobalTheory.InertBigCell.iotaW hw x)) ∧
  (∀ x, GlobalTheory.InertBigCell.iotaW hw (2⁻¹ * x) = ⅟(2 : AF F) • GlobalTheory.InertBigCell.iotaW hw x) ∧
  (∀ e : E, GlobalTheory.InertBigCell.iotaW hw (algebraMap E (w.adicCompletion E) e) =
    algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) * inclR (F := F) (AF F) e) := by
  intro F E _ _ _ _ _ σ v w hw
  refine ⟨iotaW_injective hw, iotaW_mul hw, iotaW_one hw, fun z => ?_, iotaW_conjW σ hw, fun x => ?_,
    iotaW_algebraMap hw⟩
  · rw [GlobalTheory.InertLocField.at_iff v z]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨InertChart.complEquiv hw (under_eq_of_isInertAt hw) y, by
        rw [iotaW_apply, RingEquiv.symm_apply_apply]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (iotaW_apply hw x).symm⟩
  · have h := invOf_two_smul_add_iotaW hw 0 x
    rw [add_zero, zero_add, zero_add] at h
    exact h.symm

end GlobalTheory.InertBigCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnramifiedSkewSpaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_place_unramified_skew_space : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (n r s : ℕ) (X : Spc F E n), X.IsSkew σ B r s →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ P : GL (Fin n) L, (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((P : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) →
      ∃ JT : GL (Fin n) L, JT ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) ∧
        (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ ∧
        ∀ i j, σL ((JT : Matrix (Fin n) (Fin n) L) i j) = (JT : Matrix (Fin n) (Fin n) L) j i := by
  first | exact @GlobalTheory.InertGramSkew.gram_skew_unimodular | exact GlobalTheory.InertGramSkew.gram_skew_unimodular | (intros; apply GlobalTheory.InertGramSkew.gram_skew_unimodular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrrepAveragesFinDimSmoothOfKTypesAndPolyAverages
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

variable {n : ℕ}

def typesIn (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Submodule ℂ H :=
  ⨆ μ : A, (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H)

theorem typesIn_kStable (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (A : Set (Fin n → ℝ)) : Formalism.MainNotions.S.IsKStableOn ε σ (typesIn ε σ A) := by
  intro g hg v hv
  unfold typesIn at hv ⊢
  refine Submodule.iSup_induction _ (motive := fun v => σ g v ∈ _) hv (fun μ y hy => ?_) (by simp) ?_
  · rw [sSup_eq_iSup] at hy
    refine Submodule.iSup_induction _ (motive := fun z => σ g z ∈ _) hy (fun S w hw => ?_) (by simp) ?_
    · refine Submodule.iSup_induction _ (motive := fun w => σ g w ∈ _) hw (fun hS u hu => ?_) (by simp) ?_
      · exact Submodule.mem_iSup_of_mem μ (Submodule.mem_sSup_of_mem hS (hS.2.2.1 g hg u hu))
      · intro a b ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b ha hb; rw [map_add]; exact add_mem ha hb
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

theorem typesIn_fd (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : GlobalTheory.PsCo.Pc1.Mat n → (H →L[ℂ] H)) (hσ : IsURepOn (UJset ε) σ)
    (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) {A : Set (Fin n → ℝ)} (hA : A.Finite) :
    FiniteDimensional ℂ (typesIn ε σ A) := by
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hadm := GlobalTheory.PsCo.TrAdm.isAdmissibleSub_top n ε H σ hσ' hirr
  haveI : Finite A := hA.to_subtype
  have : ∀ μ : A,
      FiniteDimensional ℂ (sSup {S : Submodule ℂ H | S ≤ ⊤ ∧ Formalism.MainNotions.S.IsKTypeOf ε σ μ S} : Submodule ℂ H) :=
    fun μ => hadm μ
  exact Submodule.finiteDimensional_iSup _

theorem irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages : SumTypes → PolyAvg → RangeFD := by
  intro hST hPA n ε H _ _ _ σ hσ hirr d
  obtain ⟨A, hAf, hA⟩ := hPA n ε d
  set M := typesIn ε σ A with hMdef
  have hMf : FiniteDimensional ℂ M := typesIn_fd ε σ hσ hirr hAf
  have hMK : Formalism.MainNotions.S.IsKStableOn ε σ M := typesIn_kStable ε σ A
  have hσ' : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ := by
    rw [mir_isURepOn_iff, mir_UJset_eq]; exact hσ
  have hMD : M ≤ smD ε σ := fun v hv => CompanionTheory.D.gk.HC.mem_smD_of_isKFin hσ' hirr ⟨M, hMf, hv, hMK⟩
  refine ⟨M.comap (smD ε σ).subtype, ?_, ?_, ?_⟩
  · exact (Submodule.comapSubtypeEquivOfLe hMD).symm.finiteDimensional
  · intro k hk x hx
    show σ k (x : H) ∈ M
    exact hMK k (by rw [mir_Kset_eq]; exact hk) x hx
  · intro P hP u
    rw [Submodule.map_comap_subtype, inf_eq_right.2 hMD]
    obtain ⟨S, hSf, hSK, hSP, hSA⟩ := hA H σ hσ u
    refine (hST n ε H σ hσ S hSf hSK).trans (sSup_le fun S' hS' => ?_) (hSP P hP)
    obtain ⟨hS'S, μ, hμ⟩ := hS'
    obtain ⟨v, hv, hv0, hvw⟩ := hμ.2.2.2.1
    have hμA : μ ∈ A := hSA μ v (hS'S hv) hv0 hvw
    exact le_iSup_of_le (⟨μ, hμA⟩ : A) (le_sSup ⟨le_top, hμ⟩)

end GlobalTheory.PsCo.PcEF

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem rangeFD_closed : RangeFD := irrepAveragesFinDimSmooth_of_kTypes_and_polyAverages @GlobalTheory.PsCo.PcEF.finDimStable_isSumOfKTypes @GlobalTheory.PsCo.PcEF.polyAverages_finiteWeightStableSubspace

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory GlobalTheory.TriMove GlobalTheory.Mem.Isom

namespace GlobalTheory.TriMoveConst

variable {D : D7}

def kapME {V V' : HSp D} (I : IsoMat V V') : GA D V ≃ᵐ GA D V' :=
  (Homeomorph.mk I.kap.toEquiv I.continuous_kap I.continuous_kap_symm).toMeasurableEquiv

theorem kapME_apply {V V' : HSp D} (I : IsoMat V V') (g : GA D V) : kapME I g = I.kap g := rfl

theorem preimage_kapME {V V' : HSp D} (I : IsoMat V V') (s : Set (GA D V)) : kapME I ⁻¹' (I.kap.symm ⁻¹' s) = s := by
  ext g
  simp only [Set.mem_preimage, kapME_apply, MulEquiv.symm_apply_apply]

theorem trH_symm_trH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (F : WO S T → ℂ) :
    trH IS.symm IT.symm (trH IS IT F) = F := by
  funext w
  show F ((homMap IS IT).symm (homMap IS IT w)) = F w
  rw [AddEquiv.symm_apply_apply]

theorem thetaKO_omH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) (F : WO S T → ℂ) :
    thetaKO (omH IS IT om) (IS.kap g) (IT.kap h) (trH IS IT F) = thetaKO om g h F := by
  unfold thetaKO
  rw [omH_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, trH_symm_trH]
  show (om (g, h) F) ((homMap IS IT).symm 0) = _
  rw [map_zero]

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

theorem ker_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) (g : GA D B) :
    (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) (IA.kap g) = Y.ker ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ true IA IW Y.rA.s Y.rA.B Y.rW.s Y.rW.B (Y.f t) P
  have hs : ∀ {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ), GlobalTheory.Grid.sgnM true s = -s := fun _ => rfl
  simp only [hs] at hF
  exact (congrArg (thetaKO (omH IA IW (Y.ω t)) (IA.kap g) (IW.kap h)) hF).trans (thetaKO_omH IA IW (Y.ω t) g h _)

theorem ker'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) (g : GA D B') :
    (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) (IA'.kap g) = Y.ker' ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ false IA' IW Y.rA'.s Y.rA'.B Y.rW.s Y.rW.B (Y.f' t) P
  show thetaKO (omH IA' IW (Y.ω' t)) (IA'.kap g) (IW.kap h) (pureTensorO ψ θ (GlobalTheory.Grid.sgn false A') WW
      (fun τ => GlobalTheory.Grid.sgnM false (cartMove IA' τ (Y.rA'.s τ))) (fun τ => cartMove IW τ (Y.rW.s τ))
      (fun τ => basMove IA' τ (Y.rA'.B τ)) (fun τ => basMove IW τ (Y.rW.B τ)) (trH IA' IW (Y.f' t))
      (polMove IW.rank_eq IA'.rank_eq P)) =
    thetaKO (Y.ω' t) g h (pureTensorO ψ θ (GlobalTheory.Grid.sgn false B') WW₁ (fun τ => GlobalTheory.Grid.sgnM false (Y.rA'.s τ)) Y.rW.s Y.rA'.B
      Y.rW.B (Y.f' t) P)
  rw [hF, thetaKO_omH]

theorem I_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) = Y.I ψ θ t P h := by
  show ∫ g in IA.kap.symm ⁻¹' Y.fd, (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) g
      ∂(Y.m.map (kapME IA)) = _
  rw [setIntegral_map_equiv (kapME IA), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd, F g ∂Y.m) (funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g)

theorem I'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) = Y.I' ψ θ t P h := by
  show ∫ g in IA'.kap.symm ⁻¹' Y.fd', (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) g
      ∂(Y.m'.map (kapME IA')) = _
  rw [setIntegral_map_equiv (kapME IA'), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd', F g ∂Y.m') (funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g)

theorem integrableOn_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd
      (triMove IA IA' IW Y).m ↔ IntegrableOn (Y.ker ψ θ t P h) Y.fd Y.m := by
  show IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (IA.kap.symm ⁻¹' Y.fd)
      (Y.m.map (kapME IA)) ↔ _
  rw [IntegrableOn, (kapME IA).restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) ∘ kapME IA = Y.ker ψ θ t P h :=
    funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem integrableOn'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd'
      (triMove IA IA' IW Y).m' ↔ IntegrableOn (Y.ker' ψ θ t P h) Y.fd' Y.m' := by
  show IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (IA'.kap.symm ⁻¹' Y.fd')
      (Y.m'.map (kapME IA')) ↔ _
  rw [IntegrableOn, (kapME IA').restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) ∘ kapME IA' = Y.ker' ψ θ t P h :=
    funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem isConst_triMove : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  intro D T₀ A A' WW B B' WW₁ IA IA' IW Y ψ θ hθ c hY
  obtain ⟨hc, P, P', H⟩ := hY
  refine ⟨hc, polMove IW.rank_eq IA.rank_eq P, polMove IW.rank_eq IA'.rank_eq P', fun t => ?_⟩
  obtain ⟨hint, ⟨h0, hne⟩, heq⟩ := H t
  refine ⟨fun h' => ?_, ⟨IW.kap h0, ?_⟩, fun h' => ?_⟩
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    exact ⟨(integrableOn_move IA IA' IW Y ψ θ hθ t P h).2 (hint h).1,
      (integrableOn'_move IA IA' IW Y ψ θ hθ t P' h).2 (hint h).2⟩
  · rw [I'_move IA IA' IW Y ψ θ hθ t P' h0]
    exact hne
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    rw [I_move IA IA' IW Y ψ θ hθ t P h, I'_move IA IA' IW Y ψ θ hθ t P' h]
    exact heq h

end GlobalTheory.TriMoveConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDiagonalIntegralExtendsLinearFormStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangian_diagonal_integral_extends_linearForm : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), Function.Injective j →
    (∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v))) →
    ∃ Λ : ((κ ⊕ κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), Λ Φ = lagInt ψ μ ν j Φ := by
  first | exact @GlobalTheory.InertLagChar.lagInt_linForm | exact GlobalTheory.InertLagChar.lagInt_linForm | (intros; apply GlobalTheory.InertLagChar.lagInt_linForm <;> assumption)
end

