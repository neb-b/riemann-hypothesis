module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormalDeformationPowerSeriesSolution
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLinearSystemMaximalDegreeFactorization
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeight
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma wt_countable : Countable SL(2, ℤ) := by
  have : Function.Injective (fun g : SL(2, ℤ) => fun i j => (g : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro g h e; ext i j; exact congrFun (congrFun e i) j
  exact this.countable

lemma wt_cont (g : SL(2, ℤ)) : Continuous (fun τ : ℍ => g • τ) :=
  continuous_const_smul (g : GL (Fin 2) ℝ)

lemma wt_fd_closed : IsClosed ModularGroup.fd := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const
  exact h1.inter h2

theorem wt_exists : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  haveI := wt_countable
  haveI hfin : Finite (SL(2, ℤ) ⧸ Gamma0 L) := Subgroup.finite_quotient_of_finiteIndex
  set S : Finset SL(2, ℤ) := (Set.finite_range (fun q : SL(2, ℤ) ⧸ Gamma0 L => q.out)).toFinset with hS
  have hcov : ∀ g : SL(2, ℤ), ∃ s ∈ S, ∃ γ ∈ Gamma0 L, g = s * γ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 L) g
    refine ⟨(QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma0 L).out, by simp [hS], ((h⁻¹ : Gamma0 L) : SL(2, ℤ)), (h⁻¹).2, ?_⟩
    rw [hh]; simp
  set K : Set ℍ := {τ | ∃ s ∈ S, s • τ ∈ ModularGroup.fd} with hK
  have hKm : MeasurableSet K := by
    have : K = ⋃ s ∈ S, (fun τ : ℍ => s • τ) ⁻¹' ModularGroup.fd := by
      ext τ; simp [hK]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => (wt_fd_closed.preimage (wt_cont s)).measurableSet
  have hKfin : ∀ τ : ℍ, {γ : Gamma0 L | (γ : SL(2, ℤ)) • τ ∈ K}.Finite := by
    intro τ
    have h1 : {g : SL(2, ℤ) | g • τ ∈ K}.Finite := by
      have : {g : SL(2, ℤ) | g • τ ∈ K} = ⋃ s ∈ S, (fun g => s * g) ⁻¹' {g | g • τ ∈ ModularGroup.fd} := by
        ext g; simp [hK, mul_smul]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet fun s _ =>
        (_root_.GlobalTheory.EisM.finite_smul_mem_fd τ).preimage (mul_right_injective s).injOn
    exact Set.Finite.preimage (f := (Subtype.val : Gamma0 L → SL(2, ℤ))) Subtype.val_injective.injOn h1
  have hKne : ∀ τ : ℍ, ∃ γ : Gamma0 L, (γ : SL(2, ℤ)) • τ ∈ K := by
    intro τ
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hcov g
    exact ⟨⟨γ, hγ⟩, s, hs, by rwa [mul_smul] at hg⟩
  let N : ℍ → ENNReal := fun τ => ∑' γ : Gamma0 L, K.indicator (1 : ℍ → ENNReal) ((γ : SL(2, ℤ)) • τ)
  have hNm : Measurable N := by
    refine Measurable.tsum fun γ => ?_
    exact (measurable_one.indicator hKm).comp (wt_cont (γ : SL(2, ℤ))).measurable
  have hNcard : ∀ τ, N τ = ((hKfin τ).toFinset.card : ENNReal) := by
    intro τ
    simp only [N]
    rw [tsum_eq_sum (s := (hKfin τ).toFinset)]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_mem hγ]; simp
    · intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_notMem hγ]
  have hNinv : ∀ (γ : Gamma0 L) τ, N ((γ : SL(2, ℤ)) • τ) = N τ := by
    intro γ τ
    simp only [N]
    rw [← (Equiv.mulRight γ).tsum_eq (fun δ : Gamma0 L => K.indicator (1 : ℍ → ENNReal) ((δ : SL(2, ℤ)) • τ))]
    simp [mul_smul]
  let ρ : ℍ → ℝ := fun τ => K.indicator (fun τ => ((N τ).toReal)⁻¹) τ
  refine ⟨ρ, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (ENNReal.measurable_toReal.comp hNm).inv.indicator hKm
  · intro τ; simp only [ρ]; apply Set.indicator_nonneg; intro τ _; positivity
  · intro τ
    have hz : ∀ γ ∉ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      simp only [ρ]; rw [Set.indicator_of_notMem hγ]
    have hpos : 0 < (hKfin τ).toFinset.card := by
      obtain ⟨γ, hγ⟩ := hKne τ
      exact Finset.card_pos.mpr ⟨γ, by simpa using hγ⟩
    have heq : ∑ γ ∈ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 1 := by
      rw [Finset.sum_congr rfl (g := fun _ => (((hKfin τ).toFinset.card : ℝ))⁻¹)]
      · rw [Finset.sum_const, nsmul_eq_mul]
        have : ((hKfin τ).toFinset.card : ℝ) ≠ 0 := by positivity
        field_simp
      · intro γ hγ
        have hγ' : (γ : SL(2, ℤ)) • τ ∈ K := by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ; exact hγ
        simp only [ρ]
        rw [Set.indicator_of_mem hγ', hNinv, hNcard]
        simp
    exact heq ▸ hasSum_sum_of_ne_finset_zero hz
  · refine ⟨S, fun τ hτ => ?_⟩
    have : τ ∈ K := by
      by_contra h; exact hτ (by simp only [ρ]; rw [Set.indicator_of_notMem h])
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralNormNatDegreeModEqOne
section
open Polynomial

namespace GlobalTheory


open Polynomial in
theorem _root_.GlobalTheory.exists_integral_norm_natDegree_mod_eq_one :
    ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
      [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] (N : ℕ), 1 ≤ N →
      ∃ f : FunctionField.ringOfIntegers k K, f ≠ 0 ∧ (Algebra.norm k[X] f).natDegree % N = 1 % N := by
  intro k K _ _ _ _ _ _ _ _ N hN
  set O := FunctionField.ringOfIntegers k K
  have hC1 : _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) := by
    unfold _root_.GlobalTheory.NeedB.IsFirstChernClassOfLineBundle
    intro n d f hf hd hdn
    obtain ⟨x, hx, h⟩ := _root_.GlobalTheory.tsenLang_ratFunc k n 1 d (fun _ => f) (fun _ => hf) hd (by simpa using hdn)
    exact ⟨x, hx, h 0⟩
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) K hC1
    RatFunc.X RatFunc.X_ne_zero
  haveI : Module.IsTorsionFree k[X] K := .trans_faithfulSMul k[X] (RatFunc k) K
  haveI : Module.Free k[X] O := Module.free_of_finite_type_torsion_free'
  haveI := IsIntegralClosure.isLocalization k[X] (RatFunc k) K O
  have hnorm : ∀ a : O, algebraMap k[X] (RatFunc k) (Algebra.norm k[X] a) =
      Algebra.norm (RatFunc k) (algebraMap O K a) := fun a =>
    (Algebra.norm_localization k[X] (nonZeroDivisors k[X]) (Rₘ := RatFunc k) (Sₘ := K) a).symm
  obtain ⟨⟨a, s⟩, hxa⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid O (nonZeroDivisors k[X])) x
  obtain ⟨b, hb, hbs⟩ := s.2
  simp only at hxa
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set r := Module.finrank k[X] O
  have hs : Algebra.norm k[X] (s : O) = b ^ r := by rw [← hbs]; exact Algebra.norm_algebraMap b
  have ha : Algebra.norm k[X] a = X * b ^ r := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [hnorm, ← hxa, map_mul, hx, ← hnorm, hs, map_mul, RatFunc.algebraMap_X]
  have hexp : r + r * (N - 1) = r * N := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hf : Algebra.norm k[X] (a * (s : O) ^ (N - 1)) = X * b ^ (r * N) := by
    rw [map_mul, map_pow, ha, hs, mul_assoc, ← pow_mul, ← pow_add, hexp]
  refine ⟨a * (s : O) ^ (N - 1), ?_, ?_⟩
  · intro h
    have h0 := hf
    rw [h, Algebra.norm_zero] at h0
    exact mul_ne_zero X_ne_zero (pow_ne_zero _ hb0) h0.symm
  · rw [hf, natDegree_mul X_ne_zero (pow_ne_zero _ hb0), natDegree_X, natDegree_pow,
      show r * N * b.natDegree = r * b.natDegree * N by ring, Nat.add_mul_mod_self_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralTraceEqZetaSubOneTop
section
open GlobalTheory.K5

theorem GlobalTheory.exists_integral_trace_eq_zeta_sub_one_top : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (S : Finset Ω), (∀ s ∈ S, IsInt (p := p) s) → ∀ j : ℕ, 1 ≤ j →
  ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt (p := p) y ∧ (∀ g ∈ E, g ∈ ⨅ n, Gn T n) ∧
    (∀ h ∈ ⨅ n, Gn T n, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧
    ∑ g ∈ E, g y = T.ζ j - 1 :=
  fun p _ hp Ω _ _ hc T S _ j hj => GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp hc T _ le_rfl S j hj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowers
section
open Polynomial

namespace GlobalTheory

theorem classGroup_mk0_mul_mul_pow_eq_one_of_span_eq {A : Type} [CommRing A] [IsDedekindDomain A]
    (N : ℕ) (P D C : Ideal A) (f : A) (hP : P ∈ nonZeroDivisors (Ideal A))
    (hD : D ∈ nonZeroDivisors (Ideal A)) (hC : C ∈ nonZeroDivisors (Ideal A))
    (h : Ideal.span {f} = P * D * C ^ N) :
    ClassGroup.mk0 ⟨P, hP⟩ * ClassGroup.mk0 ⟨D, hD⟩ * ClassGroup.mk0 ⟨C, hC⟩ ^ N = 1 := by
  rw [← map_pow, ← map_mul, ← map_mul]
  have hm : P * D * C ^ N ∈ nonZeroDivisors (Ideal A) :=
    mul_mem (mul_mem hP hD) (pow_mem hC N)
  have e : (⟨P, hP⟩ * ⟨D, hD⟩ * ⟨C, hC⟩ ^ N : nonZeroDivisors (Ideal A)) = ⟨P * D * C ^ N, hm⟩ :=
    Subtype.ext (by simp)
  rw [e, ClassGroup.mk0_eq_one_iff, ← h]
  exact ⟨⟨f, rfl⟩⟩

theorem prod_maximal_mem_nonZeroDivisors {A : Type} [CommRing A] [IsDedekindDomain A]
    {I : Type} [Fintype I] (Q : I → Ideal A) (hQ : ∀ i, (Q i).IsMaximal)
    (P₀ : Ideal A) (hP₀ : P₀.IsMaximal) (h₀ : P₀ ≠ ⊥) :
    (∏ i, Q i) ∈ nonZeroDivisors (Ideal A) := by
  refine prod_mem fun i _ => mem_nonZeroDivisors_of_ne_zero ?_
  intro hi
  have hb : (⊥ : Ideal A).IsMaximal := by
    have := hQ i
    rwa [hi] at this
  exact h₀ (hb.eq_of_le hP₀.ne_top bot_le).symm

theorem exists_class_group_mk0_eq_mul_pow :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A]
      [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A]
      [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal →
      ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal →
        a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A,
          ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  intro k A _ _ _ _ _ _ _ _ _ _ N hN P₀ hP₀ h₀
  haveI : Algebra.FiniteType k A :=
    Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  obtain ⟨r, V, D, Q, f₀, hset, hdeg⟩ := _root_.GlobalTheory.linear_system_setup k A N P₀ (by omega) hP₀
  have hform := _root_.GlobalTheory.FormalDeform.formal_deformation k A N (Fin r) V D P₀ Q f₀ hN hP₀ hset
  obtain ⟨a, ha, hall⟩ := _root_.GlobalTheory.specialise_generic_solution k A (PowerSeries k) N (Fin r) V D hN hform
  obtain ⟨-, hVD, hQ, -, -, -, -, -, hf₀, hspan₀, -⟩ := hset
  refine ⟨a, ha, fun P hP haP h => ?_⟩
  obtain ⟨Q', f, hQ', hinj, hne, hDQ', hDP, hfV, hf, hfP, hfQ'⟩ := hall P hP haP
  have hspan := _root_.GlobalTheory.degree_count_generates k A N (Fin r) D P₀ P Q Q' f₀ f hP₀ hP hQ hQ' hinj hne hDQ' hDP
    hf₀ hf hspan₀ (hVD f hfV) hfP hfQ' (hdeg f hfV hf)
  have hP₀ne : P₀ ≠ ⊥ := nonZeroDivisors.ne_zero h₀
  have hD : D ∈ nonZeroDivisors (Ideal A) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro hD0
    apply hDP
    rw [hD0]
    exact bot_le
  have hC := prod_maximal_mem_nonZeroDivisors Q hQ P₀ hP₀ hP₀ne
  have hC' := prod_maximal_mem_nonZeroDivisors Q' hQ' P₀ hP₀ hP₀ne
  rw [Finset.prod_pow] at hspan hspan₀
  have e := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P D _ f h hD hC' hspan
  have e₀ := classGroup_mk0_mul_mul_pow_eq_one_of_span_eq N P₀ D _ f₀ h₀ hD hC hspan₀
  refine ⟨ClassGroup.mk0 ⟨_, hC⟩ / ClassGroup.mk0 ⟨_, hC'⟩, ?_⟩
  generalize ClassGroup.mk0 ⟨P, h⟩ = p at e ⊢
  generalize ClassGroup.mk0 ⟨P₀, h₀⟩ = p₀ at e₀ ⊢
  generalize ClassGroup.mk0 ⟨D, hD⟩ = d at e e₀
  generalize ClassGroup.mk0 ⟨_, hC⟩ = c at e₀ ⊢
  generalize ClassGroup.mk0 ⟨_, hC'⟩ = c' at e ⊢
  have e' : p * c' ^ N = p₀ * c ^ N := by
    apply mul_right_cancel (b := d)
    rw [mul_right_comm p, mul_right_comm p₀, e, e₀]
  rw [div_pow, ← mul_div_assoc, ← e', mul_div_cancel_right]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricH1ZetaSubOneKills
section
open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.TateGeo

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem cong_refl' (k : ℕ) (x : Ω) : Cong (p := p) k x x :=
  ⟨0, isIntegral_zero, by simp⟩

theorem cong_symm' {k : ℕ} {x y : Ω} (h : Cong (p := p) k x y) : Cong (p := p) k y x := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩

theorem cong_trans' {k : ℕ} {x y w : Ω} (h1 : Cong (p := p) k x y) (h2 : Cong (p := p) k y w) : Cong (p := p) k x w := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_add' {k : ℕ} {x y x' y' : Ω} (h1 : Cong (p := p) k x y) (h2 : Cong (p := p) k x' y') :
    Cong (p := p) k (x + x') (y + y') := by
  obtain ⟨z, hz, e⟩ := h1
  obtain ⟨z', hz', e'⟩ := h2
  exact ⟨z + z', hz.add hz', by rw [mul_add, ← e, ← e']; ring⟩

theorem cong_mul_left' {k : ℕ} {x y : Ω} (a : Ω) (ha : IsInt (p := p) a) (h : Cong (p := p) k x y) :
    Cong (p := p) k (a * x) (a * y) := by
  obtain ⟨z, hz, e⟩ := h
  exact ⟨a * z, ha.mul hz, by rw [← mul_sub, e]; ring⟩

theorem cong_sum' {k : ℕ} {ι : Type*} (s : Finset ι) (f f' : ι → Ω)
    (h : ∀ i ∈ s, Cong (p := p) k (f i) (f' i)) : Cong (p := p) k (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cong_refl' (p := p) k (0 : Ω)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cong_add' (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem cong_of_eq' {k : ℕ} {x y : Ω} (h : x = y) : Cong (p := p) k x y := h ▸ cong_refl' k x

theorem mem_geoTop_iff (T : Tower p Ω) (g : Gal p Ω) :
    g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n ↔
      (∀ x : Ω, IsAlgZp p x → g x = x) ∧ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  rw [Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr Iff.rfl (forall_congr' fun n => ?_)
  rw [Gn, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  rfl

theorem exists_moved (T : Tower p Ω) {g : Gal p Ω} (hg : g ∉ Ggeo p Ω ⊓ ⨅ n, Gn T n) :
    ∃ a : Ω, g a ≠ a ∧ ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, h a = a := by
  rw [mem_geoTop_iff] at hg
  by_contra hno
  push_neg at hno
  apply hg
  refine ⟨fun x hx => ?_, fun n => ⟨?_, ?_⟩⟩
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno x hne
    exact hx' (((mem_geoTop_iff T h).mp hh).1 x hx)
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).1
  · by_contra hne
    obtain ⟨h, hh, hx'⟩ := hno _ hne
    exact hx' (((mem_geoTop_iff T h).mp hh).2 n).2

theorem uniform_lc_on (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₀ : Finset Ω, ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      (∀ x ∈ S₀, h x = g x) → Cong (p := p) k (c h) (c g) := by
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hH
  have hS : ∀ g : Gal p Ω, ∃ S : Finset Ω,
      (g ∈ H → ∀ h ∈ H, (∀ x ∈ S, h x = g x) → Cong (p := p) k (c h) (c g)) ∧
      (g ∉ H → ∀ h ∈ H, ¬ ∀ x ∈ S, h x = g x) := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨S, hS⟩ := hc.2 g hg
      exact ⟨S, fun _ => hS, fun h => (h hg).elim⟩
    · obtain ⟨a, hga, ha⟩ := exists_moved T hg
      refine ⟨{a}, fun h => (hg h).elim, fun _ h hh hagree => ?_⟩
      have := hagree a (Finset.mem_singleton_self a)
      rw [ha h hh] at this
      exact hga this.symm
  choose S hS1 hS2 using hS
  obtain ⟨F, hF⟩ := _root_.GlobalTheory.K5.gal_finite_subcover p Ω hΩ S
  refine ⟨F.biUnion S, fun g hg h hh hgh => ?_⟩
  obtain ⟨g0, hg0F, hg0⟩ := hF g
  have hg0H : g0 ∈ H := by
    by_contra hn
    exact hS2 g0 hn g hg hg0
  have h1 : Cong (p := p) k (c g) (c g0) := hS1 g0 hg0H g hg hg0
  have h2 : Cong (p := p) k (c h) (c g0) := hS1 g0 hg0H h hh (fun x hx => by
    rw [hgh x (Finset.mem_biUnion.mpr ⟨g0, hg0F, hx⟩), hg0 x hx])
  exact cong_trans' h2 (cong_symm' h1)

theorem uniform_lc_on_int (hΩ : IsClo p Ω) (T : Tower p Ω) {k : ℕ} {c : Gal p Ω → Ω}
    (hc : IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c) :
    ∃ S₁ : Finset Ω, (∀ s ∈ S₁, IsInt (p := p) s) ∧ ∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n,
      ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, (∀ x ∈ S₁, h x = g x) → Cong (p := p) k (c h) (c g) := by
  classical
  obtain ⟨S₀, hS₀⟩ := uniform_lc_on hΩ T hc
  have hm : ∀ x : Ω, ∃ a : O0 p, a ≠ 0 ∧ IsInt (p := p) (a • x) := fun x => by
    obtain ⟨a, ha, hi⟩ := (hΩ.alg.isAlgebraic x).exists_integral_multiple
    exact ⟨a, ha, hi⟩
  choose a ha hai using hm
  refine ⟨S₀.image (fun x => a x • x), ?_, fun g hg h hh hgh => hS₀ g hg h hh fun x hx => ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hs
    exact hai x
  · have e := hgh (a x • x) (Finset.mem_image_of_mem _ hx)
    rw [Algebra.smul_def, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes] at e
    have hne : algebraMap (O0 p) Ω (a x) ≠ 0 := by
      intro h0
      exact ha x (hΩ.inj (by rw [h0, map_zero]))
    exact mul_left_cancel₀ hne e

theorem h1_killed_by_zeta_sub_one_geo : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k j : ℕ), 1 ≤ j → ∀ c : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω ⊓ ⨅ n, Gn T n) c →
  (∀ g ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, Cong (p := p) k (c (g * h)) (c g + g (c h))) →
  Cob1 k (Ggeo p Ω ⊓ ⨅ n, Gn T n) (fun g => (T.ζ j - 1) * c g) := by
  intro p _ hp2 Ω _ _ hΩ T k j hj c hc hcoc
  classical
  set H := Ggeo p Ω ⊓ ⨅ n, Gn T n with hHdef
  obtain ⟨S₁, hS₁int, hS₁⟩ := uniform_lc_on_int hΩ T hc
  obtain ⟨y, E, hy, hEH, hu, hsum⟩ :=
    GlobalTheory.T.smallTraces_subgroup_galois_towerTop p Ω hp2 hΩ T H inf_le_right S₁ j hj
  set x : Ω := ∑ g ∈ E, g y * c g with hx
  have hxint : IsInt (p := p) x := by
    refine IsIntegral.sum _ fun g hg => ?_
    exact (IsIntegral.map g.toAlgHom hy).mul (hc.1 g (hEH g hg))
  refine ⟨-x, hxint.neg, fun h hh => ?_⟩
  have hσex : ∀ g ∈ E, ∃ g' ∈ E, (h * g) y = g' y ∧ ∀ s ∈ S₁, (h * g) s = g' s := fun g hg => by
    obtain ⟨g', ⟨hg'E, h1, h2⟩, -⟩ := hu (h * g) (H.mul_mem hh (hEH g hg))
    exact ⟨g', hg'E, h1, h2⟩
  choose! σ hσE hσy hσS using hσex
  have hσinj : Set.InjOn σ E := by
    intro g1 hg1 g2 hg2 he
    have ey : g1 y = g2 y := by
      have := (hσy g1 hg1).trans ((congrArg (fun f : Gal p Ω => f y) he).trans (hσy g2 hg2).symm)
      simpa using this
    have es : ∀ s ∈ S₁, g1 s = g2 s := fun s hs => by
      have := (hσS g1 hg1 s hs).trans ((congrArg (fun f : Gal p Ω => f s) he).trans (hσS g2 hg2 s hs).symm)
      simpa using this
    exact (hu g1 (hEH g1 hg1)).unique ⟨hg1, rfl, fun _ _ => rfl⟩ ⟨hg2, ey, es⟩
  have himg : E.image σ = E :=
    Finset.eq_of_subset_of_card_le (fun g' hg' => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hg'
      exact hσE g hg) (by rw [Finset.card_image_of_injOn hσinj])
  have hperm : ∑ g ∈ E, σ g y * c (σ g) = x := by
    rw [hx, ← Finset.sum_image (f := fun g' => g' y * c g') hσinj, himg]
  have hhx : h x = ∑ g ∈ E, h (g y) * h (c g) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]; simp only [map_mul]
  have hζ : h (T.ζ j) = T.ζ j := (((mem_geoTop_iff T h).mp hh).2 j).1
  have hsumh : ∑ g ∈ E, h (g y) = T.ζ j - 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hsum, map_sub, map_one, hζ]
  have step : ∀ g ∈ E, Cong (p := p) k (h (g y) * h (c g)) (σ g y * c (σ g) - h (g y) * c h) := by
    intro g hg
    have hgH := hEH g hg
    have c1 : Cong (p := p) k (h (c g)) (c (h * g) - c h) := by
      obtain ⟨z, hz, e⟩ := hcoc h hh g hgH
      exact ⟨-z, hz.neg, by rw [mul_neg, ← e]; ring⟩
    have c2 : Cong (p := p) k (c (h * g)) (c (σ g)) :=
      hS₁ (σ g) (hEH _ (hσE g hg)) (h * g) (H.mul_mem hh hgH) (hσS g hg)
    have c3 : Cong (p := p) k (c (h * g) - c h) (c (σ g) - c h) := by
      obtain ⟨z, hz, e⟩ := c2
      exact ⟨z, hz, by rw [← e]; ring⟩
    have := cong_mul_left' (h (g y)) (IsIntegral.map h.toAlgHom (IsIntegral.map g.toAlgHom hy))
      (cong_trans' c1 c3)
    refine cong_trans' this (cong_of_eq' ?_)
    have ey : h (g y) = σ g y := by rw [← hσy g hg]; rfl
    rw [ey]; ring
  have total := cong_sum' E _ _ step
  rw [← hhx, Finset.sum_sub_distrib, hperm, ← Finset.sum_mul, hsumh] at total
  obtain ⟨z, hz, e⟩ := total
  refine ⟨z, hz, ?_⟩
  show (T.ζ j - 1) * c h - (h (-x) - -x) = _
  rw [map_neg, ← e]; ring

end GlobalTheory.K5.TateGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Hilbert90LocallyConstantCocycle
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem hilbert90_locallyConstant_cocycle :
    ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : (Ω ≃ₐ[K] Ω) → Ωˣ),
      IsLocallyConstant w → (∀ g h, ((w (g * h) : Ωˣ) : Ω) = w g * g (w h)) →
        ∃ t : Ωˣ, ∀ g, ((w g : Ωˣ) : Ω) = g t / t := by
  intro K Ω _ _ _ _ _ w hw hc
  have h1 : w 1 = 1 := by
    apply Units.ext
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    have h' : ((w 1 : Ωˣ) : Ω) * 1 = (w 1 : Ω) * (w 1 : Ω) := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ (w 1).ne_zero h').symm
  have hopen : IsOpen (w ⁻¹' {1}) := hw _
  obtain ⟨E, hfin, hE⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 (hopen.mem_nhds (by simp [h1]))
  haveI := hfin
  obtain ⟨β, hβ⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_units_of_cocycle (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) (fun h => w h.1) E
    (fun h hh => hE hh) (fun g h => Units.ext (by simp [hc]))
  refine ⟨β, fun g => ?_⟩
  have := congrArg Units.val (hβ ⟨g, Subgroup.mem_top g⟩)
  simpa [div_eq_mul_inv] using this

end GlobalTheory
end

