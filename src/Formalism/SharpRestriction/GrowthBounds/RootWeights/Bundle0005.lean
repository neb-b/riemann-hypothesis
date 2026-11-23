module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001
public import Lemmata.GeneralBFactLeftVersion.Imports
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0040

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ExistsNonzeroMultipleMemLattice
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem finite_full_submodule_isLattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hfg : M.FG) (hM : MQ (K := KK O) M = ⊤) : Submodule.IsLattice (KK O) M :=
  Submodule.IsLattice.of_fg (KK O) hfg

theorem exists_nonzero_multiple_mem_lattice {O : Type} [CommRing O] [IsDomain O]
    {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    (M : Submodule O V) (hM : MQ (K := KK O) M = ⊤) (x : V) : ∃ a : O, a ≠ 0 ∧ a • x ∈ M := by
  first | exact Bl.general_b_fact_left_version.goal1 .. | (apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_version.goal1 <;> first | assumption | infer_instance)

theorem dual_lattice_values_mem_scaled : DualLatticeDivisibility := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM t z hz
  have : Submodule.IsFullLattice (KK O) M :=
    { toIsLattice := finite_full_submodule_isLattice M hfg hM
      span_eq_top := hM }
  have : Module.Free O M := Submodule.IsLattice.free (KK O) M
  have : Module.Finite O M := Submodule.IsLattice.finite (KK O) M
  let b := Module.finBasis O M
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : M) : V) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  have hcoord : ∀ i, ∀ x ∈ M, ∃ o : O, B.coord i x = algebraMap O (KK O) o := by
    intro i x hx
    refine ⟨b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 : x = ∑ j, (algebraMap O (KK O) (b.repr ⟨x, hx⟩ j)) • B j := by
      have h2 := congrArg (fun y : M => (y : V)) (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      refine h2.symm.trans ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hB, algebraMap_smul]
    conv_lhs => rw [h1]
    simp [Module.Basis.coord_apply, Finsupp.single_apply, Algebra.algebraMap_eq_smul_one]
  choose o ho using fun i => hz (B.coord i) (hcoord i)
  refine ⟨∑ i, o i • ((b i : M) : V), M.sum_mem fun i _ => M.smul_mem _ (b i).2, ?_⟩
  rw [← B.sum_repr z, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := ho i
  rw [Module.Basis.coord_apply] at this
  rw [this, hB, mul_smul, algebraMap_smul]

theorem lattice_inter_subspace_basis : LatticeSubspaceBasis := by
  intro O _ _ _ V _ _ _ _ _ M hfg hM H
  let N : Submodule O H := M.comap (H.subtype.restrictScalars O)
  have hmemN : ∀ x : H, x ∈ N ↔ (x : V) ∈ M := fun x => Iff.rfl
  have hNoeM : IsNoetherian O M := isNoetherian_of_fg_of_noetherian M hfg
  let φ : N →ₗ[O] M :=
    { toFun := fun x => ⟨((x : H) : V), (hmemN x.1).1 x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    have : ((x : H) : V) = ((y : H) : V) := congrArg (fun w : M => (w : V)) hxy
    exact Subtype.ext (Subtype.ext this)
  have hNoeN : IsNoetherian O N := isNoetherian_of_injective φ hφ
  have hNfg : N.FG := (Module.Finite.iff_fg).1 inferInstance
  have hNspan : Submodule.span (KK O) (N : Set H) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_nonzero_multiple_mem_lattice M hM (x : V)
    have ha1 : algebraMap O (KK O) a ≠ 0 :=
      (map_ne_zero_iff (algebraMap O (KK O)) (IsFractionRing.injective O (KK O))).2 ha
    have hmem : a • x ∈ N := (hmemN _).2 (by simpa using hax)
    have hx : x = (algebraMap O (KK O) a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul (KK O) a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsFullLattice (KK O) N :=
    { toIsLattice := Submodule.IsLattice.of_fg (KK O) hNfg
      span_eq_top := hNspan }
  have : Module.Free O N := Submodule.IsLattice.free (KK O) N
  let b := Module.finBasis O N
  let B := b.extendOfIsFullLattice (KK O)
  have hB : ∀ i, B i = ((b i : N) : H) := fun i =>
    Module.Basis.extendOfIsFullLattice_apply (KK O) b i
  refine ⟨Module.finrank O N, fun j => (((b j : N) : H) : V), fun j => ⟨(hmemN _).1 (b j).2, (b j : H).2⟩, ?_, ?_, ?_⟩
  · have h1 := B.linearIndependent.map' H.subtype (Submodule.ker_subtype H)
    have h2 : (fun j => (((b j : N) : H) : V)) = (H.subtype ∘ B) := by
      funext j
      simp [hB]
    rw [h2]
    exact h1
  · intro x hx
    have h1 := congrArg (fun y : H => (y : V)) (B.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
    simp [hB]
  · intro x hxM hxH
    refine ⟨fun j => b.repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩ j, ?_⟩
    have h1 := congrArg (fun y : N => ((y : H) : V)) (b.sum_repr ⟨⟨x, hxH⟩, (hmemN _).2 hxM⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.FockLatticeFiniteSpanning
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def ValuationProperties (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  vK p (0 : KK O) = ⊤ ∧
  (∀ x y : KK O, vK p (x * y) = vK p x + vK p y) ∧
  (∀ x y : KK O, min (vK p x) (vK p y) ≤ vK p (x + y)) ∧
  (∀ m : ℕ, m ≠ 0 → vK p (m : KK O) = ((padicValNat p m : ℚ) : WithTop ℚ)) ∧
  (∀ x : KK O, vK p (-x) = vK p x) ∧
  (∀ x : KK O, 0 ≤ vK p x ↔ ∃ o : O, x = algebraMap O (KK O) o)

def FockLatticeClosure (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ σ : Type,
    InBB (O := O) p (0 : MvPolynomial σ (KK O)) ∧
    (∀ F G : MvPolynomial σ (KK O), InBB (O := O) p F → InBB (O := O) p G → InBB (O := O) p (F + G)) ∧
    (∀ (o : O) (F : MvPolynomial σ (KK O)), InBB (O := O) p F → InBB (O := O) p (o • F)) ∧
    (∀ (m : σ →₀ ℕ) (c : KK O), InBB (O := O) p (monomial m c) ↔
      0 ≤ vK p c + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ)) ∧
    (∀ F : MvPolynomial σ (KK O), InBB (O := O) p F ↔ ∀ m, InBB (O := O) p (monomial m (F.coeff m))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m c, InBB (O := O) p (monomial m c) → InBB (O := O) p (u (monomial m c))) →
      ∀ F, InBB (O := O) p F → InBB (O := O) p (u F)) ∧
    (∀ (m m' : σ →₀ ℕ) (c : KK O) (z : ℤ), InBB (O := O) p (monomial m c) →
      (z = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p z + padicValNat p (expFact m')) →
      InBB (O := O) p (monomial m' (c * (z : KK O)))) ∧
    (∀ u : MvPolynomial σ (KK O) →ₗ[KK O] MvPolynomial σ (KK O),
      (∀ m, u (monomial m 1) ∈ IntPol O σ) → ∀ F ∈ IntPol O σ, u F ∈ IntPol O σ) ∧
    (∀ (m : σ →₀ ℕ) (z : ℤ), monomial m (z : KK O) ∈ IntPol O σ) ∧
    (∀ F : MvPolynomial σ (KK O), F ∈ IntPol O σ ↔ ∀ m, ∃ o : O, F.coeff m = algebraMap O (KK O) o)

def PolynomialIntegralFormPreservesLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι),
    PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)

def IntegralFormGeneratorsPreserveLattices (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι), ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)

def FockLatticeFiniteSpanning (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι],
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.HighestWeightModuleBounds
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem v2rep_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem v2rep_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun f : Module.End K V => f x) (hR a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [sub_eq_iff_eq_add'] at h
  rw [h]
  congr 1
  split_ifs <;> simp

theorem v2rep_shift (E : GLOps n K V) (hR : SatisfiesGLRelations E) (a b : Fin n) (ν : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E ν) : E a b x ∈ weightSp E (ν + rootW a b) := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro c
  rw [v2rep_comm E hR c c a b x, hx c, map_smul]
  by_cases hca : c = a <;> by_cases hcb : c = b
  · subst hca; subst hcb
    simp [rootW]
  · subst hca
    simp [rootW, hcb, Ne.symm hcb]
    module
  · subst hcb
    simp [rootW, hca]
    module
  · simp [rootW, hca, hcb, Ne.symm hcb]

def cyclicLevelSubmodule (E : GLOps n K V) (v : V) : ℕ → Submodule K V
  | 0 => Submodule.span K {v}
  | k + 1 => cyclicLevelSubmodule E v k ⊔ ⨆ ab : Fin n × Fin n, ⨆ (_ : ab.2 < ab.1), (cyclicLevelSubmodule E v k).map (E ab.1 ab.2)

theorem v2rep_Y_le (E : GLOps n K V) (v : V) (k : ℕ) : cyclicLevelSubmodule E v k ≤ cyclicLevelSubmodule E v (k + 1) := by
  exact le_sup_left

theorem v2rep_Y_low (E : GLOps n K V) (v : V) (k : ℕ) (a b : Fin n) (h : b < a) (x : V) (hx : x ∈ cyclicLevelSubmodule E v k) :
    E a b x ∈ cyclicLevelSubmodule E v (k + 1) := by
  show E a b x ∈ cyclicLevelSubmodule E v k ⊔ _
  refine Submodule.mem_sup_right ?_
  refine Submodule.mem_iSup_of_mem (a, b) ?_
  refine Submodule.mem_iSup_of_mem h ?_
  exact Submodule.mem_map_of_mem hx

theorem v2rep_Y_up (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ) :
    ∀ c d : Fin n, c ≤ d → ∀ x ∈ cyclicLevelSubmodule E v k, E c d x ∈ cyclicLevelSubmodule E v k := by
  induction k with
  | zero =>
    intro c d hcd x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · rw [hv.2.2 c d hlt]
      exact Submodule.zero_mem _
    · subst heq
      rw [(v2rep_mem_weightSp E mu v).1 hv.2.1 c]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  | succ k ih =>
    have hany : ∀ p q : Fin n, ∀ y ∈ cyclicLevelSubmodule E v k, E p q y ∈ cyclicLevelSubmodule E v (k + 1) := by
      intro p q y hy
      rcases lt_or_ge q p with hqp | hpq
      · exact v2rep_Y_low E v k p q hqp y hy
      · exact v2rep_Y_le E v k (ih p q hpq y hy)
    intro c d hcd
    suffices hs : cyclicLevelSubmodule E v (k + 1) ≤ (cyclicLevelSubmodule E v (k + 1)).comap (E c d) from fun x hx => hs hx
    refine sup_le (fun y hy => v2rep_Y_le E v k (ih c d hcd y hy)) ?_
    refine iSup_le fun ab => iSup_le fun hab => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    rw [Submodule.mem_comap, Submodule.mem_comap, v2rep_comm E hR c d ab.1 ab.2 y]
    refine Submodule.add_mem _ (v2rep_Y_low E v k ab.1 ab.2 hab _ (ih c d hcd y hy)) ?_
    refine Submodule.sub_mem _ ?_ ?_
    · split_ifs
      · exact hany c ab.2 y hy
      · exact Submodule.zero_mem _
    · split_ifs
      · exact hany ab.1 d y hy
      · exact Submodule.zero_mem _

theorem v2rep_Y_all (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) (k : ℕ)
    (a b : Fin n) (y : V) (hy : y ∈ cyclicLevelSubmodule E v k) : E a b y ∈ cyclicLevelSubmodule E v (k + 1) := by
  rcases lt_or_ge b a with hba | hab
  · exact v2rep_Y_low E v k a b hba y hy
  · exact v2rep_Y_le E v k (v2rep_Y_up E hR mu v hv k a b hab y hy)

theorem v2rep_Umon_Y (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (u : Module.End K V) (hu : u ∈ Umon E) : ∀ k, ∀ x ∈ cyclicLevelSubmodule E v k, ∃ k', u x ∈ cyclicLevelSubmodule E v k' := by
  induction hu using Submonoid.closure_induction with
  | mem u hu =>
    obtain ⟨ab, rfl⟩ := hu
    intro k x hx
    exact ⟨k + 1, v2rep_Y_all E hR mu v hv k ab.1 ab.2 x hx⟩
  | one =>
    intro k x hx
    exact ⟨k, hx⟩
  | mul u₁ u₂ _ _ h₁ h₂ =>
    intro k x hx
    obtain ⟨k₂, hk₂⟩ := h₂ k x hx
    obtain ⟨k₁, hk₁⟩ := h₁ k₂ _ hk₂
    exact ⟨k₁, hk₁⟩

def dominantWeightSubmodule [NeZero n] (E : GLOps n K V) (mu : Fin n → ℤ) : Submodule K V :=
  ⨆ ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}, weightSp E ν

theorem v2rep_Good_low [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (a b : Fin n) (h : b < a) :
    dominantWeightSubmodule E mu ≤ (dominantWeightSubmodule E mu).comap (E a b) := by
  refine iSup₂_le fun ν hν => ?_
  intro x hx
  rw [Submodule.mem_comap]
  have hs := v2rep_shift E hR a b ν x hx
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at h
    exact absurd h (Fin.not_lt_zero b)
  have hbl : b ≠ lastIdx n := by
    intro hb
    have : (a : ℕ) ≤ n - 1 := Nat.le_sub_one_of_lt a.2
    have h2 : (b : ℕ) < a := h
    rw [hb] at h2
    simp [lastIdx] at h2
    omega
  refine (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
    weightSp E ν) (ν + rootW a b) ?_) hs
  obtain ⟨h1, h2⟩ := hν
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm hbl, if_false, sub_zero]
    split_ifs <;> omega
  · simp only [Pi.add_apply, rootW, Pi.sub_apply, Pi.single_apply, Ne.symm ha0, if_false, zero_sub]
    split_ifs <;> omega

theorem v2rep_Y_Good [NeZero n] (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v)
    (k : ℕ) : cyclicLevelSubmodule E v k ≤ dominantWeightSubmodule E mu := by
  induction k with
  | zero =>
    refine (Submodule.span_singleton_le_iff_mem _ _).2 ?_
    exact (le_iSup₂ (f := fun ν (_ : ν ∈ {ν : Fin n → ℤ | mu (lastIdx n) ≤ ν (lastIdx n) ∧ ν 0 ≤ mu 0}) =>
      weightSp E ν) mu ⟨le_rfl, le_rfl⟩) hv.2.1
  | succ k ih =>
    refine sup_le ih (iSup_le fun ab => iSup_le fun hab => ?_)
    rw [Submodule.map_le_iff_le_comap]
    exact ih.trans (v2rep_Good_low E hR mu ab.1 ab.2 hab)

theorem highest_weight_module_bounds : HighestWeightModuleWeightBounds := by
  intro K V _ _ _ _ n _ E hR mu v hv u hu
  obtain ⟨k, hk⟩ := v2rep_Umon_Y E hR mu v hv u hu 0 v (Submodule.mem_span_singleton_self v)
  exact v2rep_Y_Good E hR mu v hv k hk

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section abs

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem isotypic_stable_gl_operator (E : GLOps n K V) (mu : Fin n → ℤ) (a b : Fin n) (x : V) (hx : x ∈ isoSub E mu) :
    E a b x ∈ isoSub E mu := by
  first | exact UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator .. | (apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> assumption) | (apply @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x hx | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b x | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a b | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu a | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E mu | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› E | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V ‹_› | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K V | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n K | exact @UpperTheory.Reformulated.B.Qe29.isotypic_stable_gl_operator n

theorem commuting_enveloping_monoid (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (u : Module.End K V) (hu : u ∈ Umon E) : X * u = u * X := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem u hu => obtain ⟨ab, rfl⟩ := hu; exact hX _ _
  | one => simp
  | mul u v _ _ hu hv => rw [← mul_assoc, hu, mul_assoc, hv, mul_assoc]

theorem isotypic_stable_commuting (E : GLOps n K V) (X : Module.End K V) (hX : ∀ c d, X * E c d = E c d * X)
    (mu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub E mu) : X x ∈ isoSub E mu := by
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    have h1 : X (u v) = u (X v) := by
      have := congrArg (fun f : Module.End K V => f v) (commuting_enveloping_monoid E X hX u hu)
      simpa using this
    rw [h1]
    by_cases h0 : X v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u, hu, X v, ⟨h0, ?_, ?_⟩, rfl⟩
      · rw [mem_weightSpace_iff_diag]
        intro a
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a a)
        have h3 := (mem_weightSpace_iff_diag E mu v).1 hv.2.1 a
        simp only [Module.End.mul_apply] at h2
        rw [← h2, h3, map_smul]
      · intro a b hab
        have h2 := congrArg (fun f : Module.End K V => f v) (hX a b)
        simp only [Module.End.mul_apply] at h2
        rw [← h2, hv.2.2 a b hab, map_zero]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem isotypic_projector_commutes (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (X : Module.End K V)
    (hX : ∀ mu, ∀ x ∈ isoSub E mu, X x ∈ isoSub E mu) : e * X = X * e := by
  ext x
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  simp only [Module.End.mul_apply]
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    by_cases h : mu = lam
    · subst h
      rw [he.1 x hx, he.1 _ (hX _ x hx)]
    · rw [he.2 mu h x hx, he.2 mu h _ (hX _ x hx), map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]

theorem isotypic_projector_selfAdjoint (E : GLOps n K V) (hT : (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤) (lam : Fin n → ℤ)
    (e : Module.End K V) (he : IsIsoProj E lam e) (B : V →ₗ[K] V →ₗ[K] K)
    (hB : ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0) (x y : V) :
    B (e x) y = B x (e y) := by
  have hx : x ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  have hy : y ∈ (⨆ mu : Fin n → ℤ, isoSub E mu) := by rw [hT]; trivial
  induction hx using Submodule.iSup_induction' with
  | mem mu x hx =>
    induction hy using Submodule.iSup_induction' with
    | mem nu y hy =>
      by_cases h : mu = lam
      · subst h
        rw [he.1 x hx]
        by_cases h' : nu = mu
        · subst h'; rw [he.1 y hy]
        · rw [he.2 nu h' y hy, map_zero, hB mu nu (Ne.symm h') x hx y hy]
      · rw [he.2 mu h x hx, map_zero, LinearMap.zero_apply]
        by_cases h' : nu = lam
        · subst h'; rw [he.1 y hy, hB mu nu h x hx y hy]
        · rw [he.2 nu h' y hy, map_zero]
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add (f := _), hy, hz]
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add (f := _), LinearMap.add_apply, hx, hz]

end abs

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.MemWeightSpaceIffDiagonalRep
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diagonal_rep (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]

theorem gl_commutation_apply {E : GLOps n K V} (hE : IsGLRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) + (if b = c then E a d x else 0) - (if d = a then E c b x else 0) := by
  have h := LinearMap.congr_fun (hE.1 a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have e1 : (if b = c then E a d else 0) x = (if b = c then E a d x else 0) := by split_ifs <;> rfl
  have e2 : (if d = a then E c b else 0) x = (if d = a then E c b x else 0) := by split_ifs <;> rfl
  rw [e1, e2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem gl_rep_weight_shift {E : GLOps n K V} (hE : IsGLRep E) {mu : Fin n → ℤ} {x : V}
    (hx : x ∈ weightSp E mu) (a b : Fin n) : E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [mem_weightSpace_iff_diagonal_rep] at hx ⊢
  intro c
  rw [gl_commutation_apply hE c c a b x, hx c, map_smul]
  simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  push_cast
  split_ifs <;> subst_vars <;> first | module | (exfalso; simp_all; done)

end Formalism.MainNotions.G.GLWeightTheory
end
end

