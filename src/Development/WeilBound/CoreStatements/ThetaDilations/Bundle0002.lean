module

public import Development.WeilBound.CoreStatements.ThetaDilations.SqPosOfNe
public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScaling
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilRepresentationQuadraticDatum
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0005
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.ThetaDilations.OrbitAdelic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]

theorem oh_mul {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x * y ∈ Oh F := fun v => mul_mem (hx v) (hy v)

theorem oh_nat (N : ℕ) : (N : A F) ∈ Oh F := by
  induction N with
  | zero => exact fun v => by rw [Nat.cast_zero]; exact zero_mem _
  | succ n ih => exact fun v => by rw [Nat.cast_succ]; exact add_mem (ih v) (one_mem _)

def LN (F ι : Type) [Field F] [NumberField F] (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  zero_mem' := fun _ => ⟨0, fun _ => zero_mem _, (mul_zero _).symm⟩
  add_mem' := fun ha hb i => by
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨y', hy', e'⟩ := hb i
    exact ⟨y + y', fun v => add_mem (hy v) (hy' v), by rw [Pi.add_apply, e, e', mul_add]⟩
  neg_mem' := fun ha i => by
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, fun v => neg_mem (hy v), by rw [Pi.neg_apply, e, mul_neg]⟩

theorem co_LN {N : ℕ} (hN : 0 < N) : CO (LN F ι N) := by
  obtain ⟨-, -, -, h1, -, -, -, -, -, h2⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  have e : (LN F ι N : Set (ι → A F)) = Set.univ.pi fun _ => (fun y => (N : A F) * y) '' Oh F := by
    ext x
    exact ⟨fun h i _ => (h i).imp fun y hy => ⟨hy.1, hy.2.symm⟩, fun h i => (h i trivial).imp fun y hy => ⟨hy.1, hy.2.symm⟩⟩
  refine ⟨e ▸ isCompact_univ_pi fun _ => h1.image (continuous_const.mul continuous_id), ?_⟩
  have e' : (LN F ι N : Set (ι → A F)) = ⋂ i, (fun x => x i) ⁻¹' {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
    ext x; rw [Set.mem_iInter]; rfl
  exact e' ▸ isOpen_iInter_of_finite fun i => (h2 N hN).preimage (continuous_apply i)

theorem LN_small {U : Set (ι → A F)} (hU : U ∈ 𝓝 (0 : ι → A F)) : ∃ N : ℕ, 0 < N ∧ (LN F ι N : Set (ι → A F)) ⊆ U := by
  obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, hsub⟩ := hU
  obtain ⟨N, hN, h⟩ := h1 (⋂ i, t i) (Filter.iInter_mem.2 ht)
  refine ⟨N, hN, fun x hx => hsub fun i _ => ?_⟩
  obtain ⟨y, hy, e⟩ := hx i
  exact e ▸ Set.mem_iInter.1 (h y hy) i

theorem orbit_adelic [MeasurableSpace (A F)] {ψ : AddChar (A F) ℂ} {h : A F} {B : Matrix ι ι (A F)}
    {μ : Measure (ι → A F)} (H : NAQuad ψ h B μ) {φ : (ι → A F) → ℂ} (hφ : SB φ) :
    ∃ (L' : AddSubgroup (ι → A F)) (s : Finset (ι → A F)) (C : ℝ), CO L' ∧ ∀ k : SL(2, A F), (∀ i j, k i j ∈ Oh F) →
      ∀ T, Impl ψ h B μ k T → (∀ u, ‖T φ u‖ ≤ C) ∧
        ∃ c : (ι → A F) → ℂ, (∀ a, ‖c a‖ ≤ C) ∧ T φ = ∑ a ∈ s, c a • ind a L' := by
  have hD := H.2.2.2.2.2
  obtain ⟨L, L', hL, hL', -, h0, hinv⟩ := sb_level hD hφ
  obtain ⟨L₂, hL₂, hK⟩ := co_cpt hD ((co_LN (F := F) (ι := ι) one_pos).1.image (continuous_const_smul h))
  obtain ⟨N, hN, hsub⟩ := LN_small (((hL'.2.inter (co_perp hD hL).2).inter (co_perp hD hL₂).2).mem_nhds
    ⟨⟨L'.zero_mem, (perpG hD L).zero_mem⟩, (perpG hD L₂).zero_mem⟩)
  refine orbit_bd H (Oh F) (co_LN hN) (fun a ha x hx i => ?_) hφ fun x hx y hy => funext fun u => ?_
  · obtain ⟨y, hy, e⟩ := hx i
    exact ⟨a * y, oh_mul ha hy, by rw [Pi.smul_apply, e, smul_eq_mul, mul_left_comm]⟩
  · have h1 : chiB ψ B (h • x) y = 1 := (hsub hy).2 _ (hK ⟨x, fun i => by
      obtain ⟨z, hz, e⟩ := hx i
      exact ⟨N * z, oh_mul (oh_nat N) hz, by rw [e, Nat.cast_one, one_mul]⟩, rfl⟩)
    rw [chiB, smul_dotProduct, smul_eq_mul] at h1
    rw [Heisenberg₂, hinv u x (hsub hx).1.1, AddChar.map_add_eq_mul, h1, mul_one]
    by_cases hu : u ∈ L
    · rw [show ψ (u ⬝ᵥ (B *ᵥ y)) = 1 from (hsub hy).1.2 u hu, one_mul]
    · rw [h0 u hu, mul_zero]

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

-- bundled from Development.WeilBound.CoreStatements.ThetaDilations.ProdRho
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

variable {F : Type} [Field F] [NumberField F]

theorem prod_rho {ρ : InfinitePlace F → (F →+* ℝ)} (hF : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : F) : ∏ w, |ρ w a| = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := InfinitePlace.prod_eq_abs_norm a
  rw [← Rat.cast_abs, ← h]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [IsTotallyReal.mult_eq, pow_one, ← w.norm_embedding_eq, ← hρ, Complex.norm_real, Real.norm_eq_abs]

theorem map_nMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (b : R) :
    Matrix.SpecialLinearGroup.map f (nMat b) = nMat (f b) :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f (nMat b i j) = _
    fin_cases i <;> fin_cases j <;> simp [nMat]

theorem map_wMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) : Matrix.SpecialLinearGroup.map f wMat = wMat :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f ((wMat : SL(2, R)) i j) = _
    fin_cases i <;> fin_cases j <;> simp [wMat]

theorem map_mMat {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.SpecialLinearGroup.map f (mMat a) = mMat (Units.map (f : R →* S) a) :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    show f (mMat a i j) = _
    fin_cases i <;> fin_cases j <;> simp [mMat]

def uA (a : Fˣ) : (A F)ˣ := Units.map (algebraMap F (A F) : F →* A F) a

theorem mod_rat [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)} (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} (hc : Fintype.card ι = 2 * M)
    (B : Matrix ι ι F) (a : Fˣ) (s : Set (ι → A F)) (hs : MeasurableSet s) :
    muF B lf ((fun u => (uA a : A F) • u) '' s) =
      ENNReal.ofReal ((|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M) ^ 2) * muF B lf s := by
  have h2 := (_root_.GlobalTheory.CompanionTheory.SW.Core.PiScale.pi_scale F lf hlf h1 ι).2 (uA a) s hs
  have h3 := (_root_.GlobalTheory.CompanionTheory.SW.Core.Scale.lf_scale F lf hlf h1).1 a a.ne_zero _ (_root_.GlobalTheory.CompanionTheory.SW.Core.AfTop.finiteAdele_topology F).2.2.2.2.1.measurableSet
  rw [h1, mul_one] at h3
  rw [muF, Measure.smul_apply, Measure.smul_apply, h2, smul_eq_mul, smul_eq_mul, mul_left_comm, ← pow_mul,
    ENNReal.ofReal_pow (by positivity), hc, mul_comm M 2]
  exact congrArg (fun t => t ^ (2 * M) * _) h3

theorem good_ex [MeasurableSpace (A F)] [BorelSpace (A F)] {lf : Measure (A F)} (hlf : lf.IsAddHaarMeasure)
    (h1 : lf (Oh F) = 1) {ψ : AddChar (A F) ℂ} (hψ : IsStdChar F ψ) {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ}
    {B : Matrix ι ι F} {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P)
    {𝒟 : ((ι → A F) → ℂ) → (InfinitePlace F → ℂ) → ℂ}
    (hD : ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) →
      (∀ b : F, 𝒟 (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = 𝒟 φ τ) ∧
      (∀ a : F, a ≠ 0 → 𝒟 (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = 𝒟 φ τ) ∧
      (cG B ρ P τ * 𝒟 (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = 𝒟 φ τ) ∧
      ∀ c : ℂ, 𝒟 (c • φ) τ = c * 𝒟 φ τ) (γ : SL(2, F)) :
    ∃ T, Impl ψ (hf F) (Bf B) (muF B lf) (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) γ) T ∧
      ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → wt M (mob ρ γ τ) * ‖𝒟 (T φ) (mob ρ γ τ)‖ = wt M τ * ‖𝒟 φ τ‖ := by
  have H := _root_.GlobalTheory.CompanionTheory.SW.Core.SelfDual.naQuad F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hmob := _root_.GlobalTheory.CompanionTheory.SW.Core.Mobius.main F ρ
  set G : SL(2, F) → Prop := fun γ => ∃ T,
    Impl ψ (hf F) (Bf B) (muF B lf) (Matrix.SpecialLinearGroup.map (algebraMap F (A F)) γ) T ∧
      ∀ φ τ, SB φ → (∀ w, 0 < (τ w).im) → wt M (mob ρ γ τ) * ‖𝒟 (T φ) (mob ρ γ τ)‖ = wt M τ * ‖𝒟 φ τ‖ with hG
  have gmul : ∀ g g', G g → G g' → G (g * g') := by
    rintro g g' ⟨T, a1, a2⟩ ⟨T', b1, b2⟩
    refine ⟨T ∘ T', by rw [map_mul]; exact impl_mul a1 b1, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.1, ← b2 φ τ hφ hτ]
    exact a2 _ _ (b1.1 φ hφ) fun w => ((hmob τ hτ).1 g' w).2
  have gU : ∀ b, G (nMat b) := fun b => by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) (nMat b) = nMat (algebraMap F (A F) b) := map_nMat _ _
    refine ⟨_, e ▸ impl_U H _, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.2.1, (hD φ τ hφ hτ).1]
    simp [wt]
  have gW : G wMat := by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) wMat = wMat := map_wMat _
    refine ⟨_, e ▸ impl_fou_chiB H, fun φ τ hφ hτ => ?_⟩
    rw [(hmob τ hτ).2.2.2.2, ← (hD φ τ hφ hτ).2.2.1, norm_mul, (_root_.GlobalTheory.CompanionTheory.SW.GaussFou.gauss_fourier F ι M B ρ P hQ τ hτ).2.1,
      ← mul_assoc, wt, wt, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg, Real.sqrt_div (hτ w).le, ← Complex.norm_def, div_pow,
      div_eq_mul_inv]
  have gD : ∀ a : Fˣ, G (mMat a) := fun a => by
    have e : Matrix.SpecialLinearGroup.map (algebraMap F (A F)) (mMat a) = mMat (uA a) := map_mMat _ _
    have hn : (0 : ℝ) < |((Algebra.norm ℚ (a : F) : ℚ) : ℝ)| :=
      abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 a.ne_zero)
    refine ⟨_, e ▸ impl_D H (uA a) (by positivity) (mod_rat hlf h1 hQ.2.1 B a), fun φ τ hφ hτ => ?_⟩
    have e2 : opD (|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M) (uA a : A F) φ =
        ((|((Algebra.norm ℚ (a : F) : ℚ) : ℝ)|⁻¹ ^ M : ℝ) : ℂ) • opD 1 (algebraMap F (A F) a) φ := by
      funext u; simp [opD, uA]
    have hτ' := fun w => ((hmob τ hτ).1 (mMat a) w).2
    have hs : SB (opD 1 (algebraMap F (A F) a) φ) := sb_opD H 1 (uA a) hφ
    rw [e2, (hD _ _ hs hτ').2.2.2, (hmob τ hτ).2.2.2.1, (hD φ τ hφ hτ).2.1 a a.ne_zero, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), ← mul_assoc]
    congr 1
    rw [inv_pow, ← div_eq_mul_inv, div_eq_iff (by positivity), ← prod_rho hQ.1 hQ.2.2.2.2.1, wt, wt,
      ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Complex.ofReal_pow, Complex.im_ofReal_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, mul_pow, mul_comm]
  show G γ
  obtain ⟨d1, -, d3, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.Core.SL2BruhatDecomposition.decompositions F γ
  by_cases hc : γ 1 0 = 0
  · have ha : γ 0 0 ≠ 0 := fun h0 => by
      have := γ.det_coe
      rw [Matrix.det_fin_two, h0, hc] at this
      simp at this
    rw [d3 (Units.mk0 _ ha) rfl hc]
    exact gmul _ _ (gU _) (gD _)
  · rw [d1 (Units.mk0 _ hc) rfl]
    exact gmul _ _ (gmul _ _ (gmul _ _ (gU _) (gD _)) gW) (gU _)

end PositivityTheory.PlacePermOperatorBicommutantSpan
end
end

