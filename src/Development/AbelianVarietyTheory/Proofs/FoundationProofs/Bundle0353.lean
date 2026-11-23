module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0348
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCoboundaryWildInertiaAwayFromL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.WildCob

theorem eq_one_of_pow_near {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h1 : ∀ i j, ‖(A - 1) i j‖ < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ‖(m : K)‖ = 1 ∧ ∀ i j, ‖(A ^ m - 1) i j‖ < ε) : A = 1 := by
  obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
  simp only [add_sub_cancel_left] at h1
  by_contra hne
  have hX : ∃ i j, X i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (by rw [show X = 0 from Matrix.ext hc, add_zero])
  obtain ⟨i₀, j₀, h0⟩ := hX
  obtain ⟨⟨a, b⟩, -, hab⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n)) (fun p => ‖X p.1 p.2‖)
    ⟨(i₀, j₀), Finset.mem_univ _⟩
  set r := ‖X a b‖ with hr
  have hle : ∀ i j, ‖X i j‖ ≤ r := fun i j => hab (i, j) (Finset.mem_univ _)
  have hr0 : 0 < r := (norm_pos_iff.2 h0).trans_le (hle _ _)
  have hr1 : r < 1 := h1 a b
  have hmul : ∀ (Y Z : Matrix n n K) (s t : ℝ), 0 ≤ s → 0 ≤ t → (∀ i j, ‖Y i j‖ ≤ s) → (∀ i j, ‖Z i j‖ ≤ t) →
      ∀ i j, ‖(Y * Z) i j‖ ≤ s * t := by
    intro Y Z s t hs ht hY hZ i j
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hs ht) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hY _ _) (hZ _ _) (norm_nonneg _) hs
  have hrr : 0 ≤ r * r := mul_nonneg hr0.le hr0.le
  have key : ∀ m : ℕ, ∀ i j, ‖((1 + X) ^ m - 1 - (m : K) • X) i j‖ ≤ r * r := by
    intro m
    induction m with
    | zero => intro i j; simpa using hrr
    | succ m ih =>
      intro i j
      have e : (1 + X) ^ (m + 1) - 1 - ((m + 1 : ℕ) : K) • X =
          ((1 + X) ^ m - 1 - (m : K) • X) + (((1 + X) ^ m - 1 - (m : K) • X) * X + (m : K) • (X * X)) := by
        simp only [pow_succ, mul_add, sub_mul, mul_one, one_mul, Nat.cast_succ, add_smul, one_smul, Matrix.smul_mul]
        abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih i j)
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · exact (hmul _ _ _ _ hrr hr0.le ih hle i j).trans (mul_le_of_le_one_right hrr hr1.le)
      · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)).trans
          (hmul _ _ _ _ hr0.le hr0.le hle hle i j)
  obtain ⟨m, hm, hm'⟩ := h r hr0
  have e : (m : K) * X a b = ((1 + X) ^ m - 1) a b + -(((1 + X) ^ m - 1 - (m : K) • X) a b) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h2 : ‖(m : K) * X a b‖ < r := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hm' a b) ?_)
    rw [norm_neg]
    exact (key m a b).trans_lt (mul_lt_of_lt_one_right hr0 hr1)
  rw [norm_mul, hm, one_mul] at h2
  exact lt_irrefl _ h2

theorem exists_open_subgroup {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Set (G ℚ Ω)) (hV : V ∈ nhds (1 : G ℚ Ω)) :
    ∃ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) ∧ H.index ≠ 0 ∧ (H : Set (G ℚ Ω)) ⊆ V := by
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).mp hV
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, ?_, hsub⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Module.finrank_pos.ne'

theorem exists_pow_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (B : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (hvl : ¬ B.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ GlobalTheory.WeilDeligne.Wild ℚ B) (V : Set (G ℚ Ω))
    (hV : V ∈ nhds (1 : G ℚ Ω)) : ∃ m : ℕ, ¬ l ∣ m ∧ σ ^ m ∈ V := by
  obtain ⟨H, ho, hidx, hsub⟩ := exists_open_subgroup V hV
  have hvl1 : B.valuation (l : Ω) = 1 :=
    le_antisymm ((B.valuation_le_one_iff _).mpr (natCast_mem B l)) (not_lt.mp hvl)
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  refine ⟨m, hm, hsub (GlobalTheory.WildKill.mem_of_wild B H ho (σ ^ m) (l ^ a) ?_
    ((GlobalTheory.WeilDeligne.Wild ℚ B).pow_mem hσ m) ?_)⟩
  · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
  · rw [← pow_mul, mul_comm]; exact hmem

theorem isUnit_natCast {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : IsUnit (m : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

noncomputable def aff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l)
    (s : G ℚ Ω) : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
  Matrix.fromBlocks (mat W s) (Matrix.of fun i _ => z s i) 0 1

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (q : Pl), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ z ∈ coc W c (Ine (F := ℚ) B), ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = mat W σ *ᵥ v - v := by
  intro l hl Ω _ _ _ W c B q hW _ hB hq z hz
  obtain ⟨hzc, hzO, hzm⟩ := mem_coc.1 hz
  have hvl : ¬ B.valuation (l : Ω) < 1 := by
    intro h
    apply hq
    rw [← hB]
    simpa using h
  set P := GlobalTheory.WeilDeligne.Wild ℚ B with hP
  have hPI : P ≤ Ine (F := ℚ) B := GlobalTheory.WeilDeligne.Wild_le_Ine
  have hz1 : z 1 = 0 := by
    have := hzm 1 (one_mem _) 1 (one_mem _)
    rw [mul_one, mat, map_one, Units.val_one, Matrix.one_mulVec] at this
    exact left_eq_add.1 this
  have ha1 : aff W z 1 = 1 := by
    rw [aff, ← Matrix.fromBlocks_one]
    congr 1
    · simp
    · ext i j; simp [hz1]
  let M : P →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
    { toFun := fun s => aff W z s
      map_one' := ha1
      map_mul' := fun s t => by
        simp only [aff, Matrix.fromBlocks_multiply, Subgroup.coe_mul]
        congr 1
        · simp [mat]
        · ext i j
          rw [hzm s (hPI s.2) t (hPI t.2), Matrix.mul_one]
          exact add_comm _ _
        · simp
        · simp }
  have hM : ∀ s : P, M s = aff W z s := fun _ => rfl
  have hcont : ∀ i j, Continuous fun s => aff W z s i j := by
    have hWc : Continuous fun s => mat W s := Units.continuous_val.comp hW
    rintro (i | i) (j | j)
    · exact hWc.matrix_elem i j
    · exact hzc i
    · exact continuous_const
    · exact continuous_const
  have hV : ∀ ε : ℝ, 0 < ε → {s : G ℚ Ω | ∀ i j, ‖(aff W z s - 1) i j‖ < ε} ∈ nhds (1 : G ℚ Ω) := by
    intro ε hε
    refine IsOpen.mem_nhds ?_ (by simp [ha1, hε])
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt ((hcont i j).sub continuous_const).norm continuous_const
  have hker : ∀ s : P, (∀ i j, ‖(aff W z s - 1) i j‖ < 1) → s ∈ M.ker := by
    intro s hs
    refine eq_one_of_pow_near (M s) hs fun ε hε => ?_
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV ε hε)
    exact ⟨m, norm_natCast_eq_one hm, by rw [← map_pow]; exact hm'⟩
  have hfi : M.ker.FiniteIndex := by
    obtain ⟨H, -, hidx, hsub⟩ := exists_open_subgroup _ (hV 1 one_pos)
    have : H.FiniteIndex := ⟨hidx⟩
    exact Subgroup.finiteIndex_of_le (H := H.subgroupOf P) fun s hs => hker s (hsub hs)
  classical
  let Q := P ⧸ M.ker
  letI : Fintype Q := Fintype.ofFinite _
  have hcard : ¬ l ∣ Fintype.card Q := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV 1 one_pos)
    apply hm
    rw [← hx, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hker _ hm'
  let Mq : Q →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) := QuotientGroup.lift M.ker M fun _ h => h
  have hMq : ∀ x : Q, Mq x = aff W z (x.out : P) := fun x => by
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hS : ∀ s : P, aff W z s * ∑ x : Q, Mq x = ∑ x : Q, Mq x := fun s => by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (s : Q)) _ _ fun x => by
      rw [Equiv.coe_mulLeft, map_mul]; rfl
  obtain ⟨u, hu⟩ := isUnit_natCast hcard
  have hinv : (Fintype.card Q : Qbar l) * algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← map_mul, Units.mul_inv, map_one]
  refine ⟨fun i => -(algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) * ∑ x : Q, z (x.out : P) i), fun i =>
    c.O.neg_mem (c.O.mul_mem (c.O.algebraMap_mem _) (c.O.sum_mem fun x _ => hzO _ _)), fun σ hσ => ?_⟩
  funext i
  have h1 := congrFun (congrFun (hS ⟨σ, hσ⟩) (Sum.inl i)) (Sum.inr ())
  simp only [hMq, Matrix.mul_apply, Matrix.sum_apply, aff, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply_eq, Fin.sum_univ_two,
    Finset.univ_unique, Finset.sum_singleton, Finset.sum_const, Finset.card_univ, Finset.card_singleton, one_smul, nsmul_eq_mul, Nat.cast_one,
    one_mul, mul_one] at h1
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (algebraMap ℤ_[l] (Qbar l) (↑u⁻¹)) * h1 - z σ i * hinv

end GlobalTheory.WildCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

variable {l : ℕ} [Fact l.Prime]

theorem norm_l_pow_anti {m n : ℕ} (h : n ≤ m) :
    ‖((l : ℕ) : Qbar l) ^ m‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_natCast_l_lt_one.le h

theorem isCompact_coef (c : Coef l) : IsCompact (c.O : Set (Qbar l)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let f : (Fin k → ℤ_[l]) → Qbar l :=
    fun v => ∑ i, algebraMap ℤ_[l] (Qbar l) (v i) * (s i : Qbar l)
  have hcont : Continuous f := by
    have ha : Continuous (algebraMap ℤ_[l] (Qbar l)) := by
      have : ⇑(algebraMap ℤ_[l] (Qbar l)) = fun a : ℤ_[l] => algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) := by
        funext a; exact IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) a
      rw [this]
      exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val
    exact continuous_finsetSum _ fun i _ => (ha.comp (continuous_apply i)).mul continuous_const
  have heq : (c.O : Set (Qbar l)) = Set.range f := by
    ext x
    constructor
    · intro hx
      have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (Set.range s) := by rw [hs]; trivial
      obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hmem
      refine ⟨v, ?_⟩
      have := congrArg (fun y : c.O => (y : Qbar l)) hv
      simp only [AddSubmonoidClass.coe_finsetSum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Algebra.smul_def]
      rfl
    · rintro ⟨v, rfl⟩
      exact c.O.sum_mem fun i _ => c.O.mul_mem (c.O.algebraMap_mem _) (s i).2
  rw [heq]
  exact isCompact_range hcont

theorem cg_of_le {a : ℕ → Qbar l} (h : ∀ n, Cg n (a (n + 1)) (a n)) {n m : ℕ} (hnm : n ≤ m) :
    Cg n (a m) (a n) := by
  induction m, hnm using Nat.le_induction with
  | base => unfold Cg; simp
  | succ m hm ih =>
    have h1 : Cg n (a (m + 1)) (a m) := by
      unfold Cg at *; exact (h m).trans (norm_l_pow_anti hm)
    exact cg_trans h1 ih

theorem exists_limit_coef : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (X : Type) (a : ℕ → X → Qbar l),
    (∀ n x, a n x ∈ c.O) → (∀ n x, Cg n (a (n + 1) x) (a n x)) →
    ∃ z : X → Qbar l, (∀ x, z x ∈ c.O) ∧ ∀ n x, Cg n (z x) (a n x) := by
  intro l _ c X a hO hC
  have key : ∀ x, ∃ y ∈ (c.O : Set (Qbar l)), ∀ n, Cg n y (a n x) := by
    intro x
    have hle : ∀ n m, n ≤ m → ‖a m x - a n x‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
      fun n m h => cg_of_le (a := fun k => a k x) (fun k => hC k x) h
    have hcs : CauchySeq (fun m => a m x) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (tendsto_norm_l_pow (l := l)).eventually (gt_mem_nhds hε) |>.exists_forall_of_atTop
      refine ⟨N, fun m hm => ?_⟩
      rw [dist_eq_norm]
      exact (hle N m hm).trans_lt (hN N le_rfl)
    obtain ⟨y, hy, hlim⟩ := cauchySeq_tendsto_of_isComplete (isCompact_coef c).isComplete
      (fun m => hO m x) hcs
    refine ⟨y, hy, fun n => ?_⟩
    unfold Cg
    have ht : Filter.Tendsto (fun m => ‖a m x - a n x‖) Filter.atTop (nhds ‖y - a n x‖) :=
      (hlim.sub_const _).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => hle n m hm⟩)
  choose z hz using key
  exact ⟨z, fun x => (hz x).1, fun n x => (hz x).2 n⟩

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulScalarClassEqSmulAddCoboundaryModPrimeP
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.LocCharSpan

open UpperTheory.V.X

variable {O Γ : Type} [CommRing O] [TopologicalSpace O] [Group Γ] [TopologicalSpace Γ]

theorem red_mem (p : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (a : Γ → O) (ha : Continuous a)
    (hc : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t)) :
    (fun s => Lev.mk p (a s)) ∈ Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := by
  refine ⟨hp.comp ha, fun s t => ?_⟩
  have h := (Lev.mk_eq_zero p _).2 (hc s t)
  rw [map_sub, sub_eq_zero, map_add (f := _), ← smul_eq_mul ((θ s : Oˣ) : O), map_smul] at h
  exact h


omit [TopologicalSpace O] in
theorem lift_cob (p : O) (θ : Γ →* Oˣ) (z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) (f : Γ → O)
    (hf : ∀ s, z.1 s = Lev.mk p (f s))
    (hz : (Submodule.Quotient.mk z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) = 0) :
    ∃ y : O, ∀ s, p ∣ f s - (((θ s : Oˣ) : O) * y - y) := by
  obtain ⟨y', hy'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hz)
  obtain ⟨y, rfl⟩ := Lev.mk_surjective p y'
  refine ⟨y, fun s => (Lev.mk_eq_zero p _).1 ?_⟩
  have h : z.1 s = ((θ s : Oˣ) : O) • Lev.mk p y - Lev.mk p y := hy' s
  rw [map_sub, map_sub, ← hf, h, ← smul_eq_mul, map_smul, sub_self]


omit [TopologicalSpace O] in
theorem kill (p : O) (θ : Γ →* Oˣ) (h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ)) : p • h = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  have h0 : p • z = 0 := Subtype.ext (funext fun s => by
    obtain ⟨y, hy⟩ := Lev.mk_surjective p (z.1 s)
    change p • z.1 s = 0
    rw [← hy, ← map_smul, Lev.mk_eq_zero]
    exact Dvd.intro _ rfl)
  rw [← Submodule.Quotient.mk_smul, h0, Submodule.Quotient.mk_zero]

theorem span_of_classes (p q : O) (hp : Continuous (Lev.mk p)) (θ : Γ →* Oˣ) (m : ℕ)
    (hcount : ∀ z : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), (∀ x : O, x • z = 0 → q ∣ x) →
      ∀ h : H1 (Formalism.GaloisCohomology.scalRep (Lev p) θ), ∃ x : O, m • h = x • z)
    (a : Γ → O) (ha : Continuous a) (hca : ∀ s t, p ∣ a (s * t) - (a s + ((θ s : Oˣ) : O) * a t))
    (hann : ∀ x y : O, (∀ s, p ∣ x * a s - (((θ s : Oˣ) : O) * y - y)) → q ∣ x)
    (a' : Γ → O) (ha' : Continuous a') (hca' : ∀ s t, p ∣ a' (s * t) - (a' s + ((θ s : Oˣ) : O) * a' t)) :
    ∃ x y : O, ∀ s, p ∣ (m : O) * a' s - (x * a s + (((θ s : Oˣ) : O) * y - y)) := by
  let z : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a ha hca⟩
  let z' : Z1 (Formalism.GaloisCohomology.scalRep (Lev p) θ) := ⟨_, red_mem _ hp θ a' ha' hca'⟩
  obtain ⟨x, hx⟩ := hcount (Submodule.Quotient.mk z) (fun x hx => by
      rw [← Submodule.Quotient.mk_smul] at hx
      obtain ⟨y, hy⟩ := lift_cob _ θ (x • z) (fun s => x * a s)
        (fun s => ((Lev.mk p).map_smul x (a s)).symm) hx
      exact hann x y hy) (Submodule.Quotient.mk z')
  rw [← Nat.cast_smul_eq_nsmul O, ← sub_eq_zero, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    ← Submodule.Quotient.mk_sub] at hx
  obtain ⟨y, hy⟩ := lift_cob _ θ ((m : O) • z' - x • z) (fun s => (m : O) * a' s - x * a s)
    (fun s => by
      rw [map_sub, ← smul_eq_mul, ← smul_eq_mul, map_smul, map_smul]
      rfl) hx
  refine ⟨x, y, fun s => ?_⟩
  rw [← sub_sub]
  exact hy s

end GlobalTheory.LocCharSpan

theorem GlobalTheory.LocCharSpan.span : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (A : ValuationSubring Ω), OverL l A → ∀ θ' : ↥(Dec (F := ℚ) A) →* c.Oˣ, Continuous (fun g => ((θ' g : c.Oˣ) : c.O)) → (∃ g, θ' g ≠ 1) → (∃ g, θ' g ≠ (UpperTheory.V.Base.chiO ℚ Ω l c.O).comp (Dec (F := ℚ) A).subtype g) → ∀ r : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ↥(Dec (F := ℚ) A) → c.O, Continuous a → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a (s * t) - (a s + ((θ' s : c.Oˣ) : c.O) * a t)) → (∀ x y : c.O, (∀ s, ((l : ℕ) : c.O) ^ n ∣ x * a s - (((θ' s : c.Oˣ) : c.O) * y - y)) → ((l : ℕ) : c.O) ^ (n - r) ∣ x) → ∀ a' : ↥(Dec (F := ℚ) A) → c.O, Continuous a' → (∀ s t, ((l : ℕ) : c.O) ^ n ∣ a' (s * t) - (a' s + ((θ' s : c.Oˣ) : c.O) * a' t)) → ∃ x y : c.O, ∀ s, ((l : ℕ) : c.O) ^ n ∣ (m : c.O) * a' s - (x * a s + (((θ' s : c.Oˣ) : c.O) * y - y)) := by
  intro h1 h2 h3 l _ Ω _ _ _ c A hA θ hθ hn1 hn2 r
  obtain ⟨C, hC⟩ := GlobalTheory.T.local_character_h1_finite_levels h1 h2 h3 l Ω c A hA θ hθ hn1 hn2
  obtain ⟨m, hm, hcount⟩ := GlobalTheory.CycIndex.nsmul_mem_span_of_card_le l c C r
  refine ⟨m, hm, fun n hn a ha hca hann a' ha' hca' => ?_⟩
  obtain ⟨hfin, hcard⟩ := hC n hn
  have hl : ((l : ℕ) : c.O) ≠ 0 := fun h => by
    have h' := congrArg Subtype.val h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hp := (UpperTheory.V.X.So.adicCont l c).1 _ (pow_ne_zero n hl)
  exact GlobalTheory.LocCharSpan.span_of_classes _ _ hp θ m
    (hcount n _ (GlobalTheory.LocCharSpan.kill _ θ) hcard) a ha hca hann a' ha' hca'
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FgInertiaCocyclesModCoboundariesCoefRing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.InertCoh

theorem fg_map_mkQ_of_ev {R M N : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (Z B Y : Submodule R M) (ev : M →ₗ[R] N) (L : Submodule R N) (hL : L.FG)
    (h1 : ∀ z ∈ Z, ∃ y ∈ Y, z - y ∈ B) (h2 : ∀ y ∈ Y, ev y ∈ L) (h3 : ∀ y ∈ Y, ev y = 0 → y ∈ B) :
    (Z.map B.mkQ).FG := by
  let f : Y →ₗ[R] N := ev ∘ₗ Y.subtype
  let g : Y →ₗ[R] (M ⧸ B) := B.mkQ ∘ₗ Y.subtype
  have hf : (LinearMap.range f).FG := by
    refine hL.of_le ?_
    rintro _ ⟨y, rfl⟩
    exact h2 y y.2
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro y hy
    exact (Submodule.Quotient.mk_eq_zero B).2 (h3 y y.2 hy)
  haveI : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.2 hf
  haveI : Module.Finite R (Y ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  have hg : (LinearMap.range g).FG := by
    rw [← Submodule.range_liftQ (LinearMap.ker f) g hker, LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine hg.of_le ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨y, hy, hzy⟩ := h1 z hz
  exact ⟨⟨y, hy⟩, ((Submodule.Quotient.eq B).2 hzy).symm⟩

theorem cobound_mem_coc {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {W : R2 Ω l} {c : Coef l}
    (I : Subgroup (G ℚ Ω)) (hW : Continuous W) (hO : ∀ s i j, mat W s i j ∈ c.O) {v : Fin 2 → Qbar l}
    (hv : ∀ i, v i ∈ c.O) : (fun s => mat W s *ᵥ v - v) ∈ coc W c I := by
  have hm : Continuous fun s => mat W s := Units.continuous_val.comp hW
  refine mem_coc.2 ⟨fun i => ?_, fun s i => ?_, fun s _ t _ => ?_⟩
  · exact (continuous_apply i).comp ((hm.matrix_mulVec continuous_const).sub continuous_const)
  · simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
    exact c.O.sub_mem (c.O.sum_mem fun j _ => c.O.mul_mem (hO s i j) (hv j)) (hv i)
  · simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
    abel

theorem fg_coc_mod_cob : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (I : Subgroup (G ℚ Ω)) (P : Set (G ℚ Ω)) (γ : G ℚ Ω), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ z ∈ coc W c I, ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ ∈ P, z σ = mat W σ *ᵥ v - v) → (∀ z ∈ coc W c I, (∀ σ ∈ P, z σ = 0) → z γ = 0 → ∀ s ∈ I, z s = 0) → ((coc W c I).map (cob W c I).mkQ).FG := by
  intro l _ Ω _ _ W c I P γ hW hO hP hγ
  haveI := c.dvr
  haveI : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  let Y : Submodule c.O (G ℚ Ω → Fin 2 → Qbar l) :=
    coc W c I ⊓ ⨅ σ ∈ P, LinearMap.ker (LinearMap.proj σ : (G ℚ Ω → Fin 2 → Qbar l) →ₗ[c.O] (Fin 2 → Qbar l))
  have hY : ∀ z, z ∈ Y ↔ z ∈ coc W c I ∧ ∀ σ ∈ P, z σ = 0 := by
    intro z
    simp [Y, Submodule.mem_iInf]
  let ι : (Fin 2 → c.O) →ₗ[c.O] (Fin 2 → Qbar l) := (Algebra.linearMap c.O (Qbar l)).compLeft (Fin 2)
  have hL : (LinearMap.range ι).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map _
  refine fg_map_mkQ_of_ev _ _ Y (LinearMap.proj γ) _ hL ?_ ?_ ?_
  · intro z hz
    obtain ⟨v, hv, hzv⟩ := hP z hz
    refine ⟨z - fun s => mat W s *ᵥ v - v, (hY _).2 ⟨Submodule.sub_mem _ hz (cobound_mem_coc I hW hO hv), ?_⟩, ?_⟩
    · intro σ hσ
      simp only [Pi.sub_apply, hzv σ hσ, sub_self]
    · exact mem_cob.2 ⟨v, fun s _ => by simp only [sub_sub_cancel]⟩
  · intro y hy
    exact ⟨fun i => ⟨y γ i, (mem_coc.1 ((hY y).1 hy).1).2.1 γ i⟩, rfl⟩
  · intro y hy h0
    refine mem_cob.2 ⟨0, fun s hs => ?_⟩
    rw [hγ y ((hY y).1 hy).1 ((hY y).1 hy).2 h0 s hs]
    simp

end GlobalTheory.InertCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScalingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_cocycle_integral_after_scaling : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (z : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → z ∈ Z1 (Loc.colRep W) → Unr W z → ∀ A : ValuationSubring Ω, ∃ (c' : Coef l) (k : ℕ), c.O ≤ c'.O ∧ (∀ s i, ((l : ℕ) : Qbar l) ^ k * z s i ∈ c'.O) ∧ (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Triv W A z → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Gr W A z → ∃ x ∈ c'.O, ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k * z s 1 = mat W s 1 1 * x - x) := by
  first | exact @GlobalTheory.CocInt.integral_after_scaling | exact GlobalTheory.CocInt.integral_after_scaling | (intros; apply GlobalTheory.CocInt.integral_after_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := _root_.GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
end

