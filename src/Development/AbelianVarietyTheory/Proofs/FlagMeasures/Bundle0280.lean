module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnitaryUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProduct
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryUnitriangularizingFlagStabilizer
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagTorus

theorem witt_partners {E V : Type} [Field E] [CharZero E] [StarRing E] [AddCommGroup V] [Module E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e : Fin r → V) (he : LinearIndependent E e)
    (hee : ∀ a b, h (e a) (e b) = 0) :
    ∃ f : Fin r → V, (∀ a b, h (e a) (f b) = if a = b then 1 else 0) ∧ ∀ a b, h (f a) (f b) = 0 := by
  classical
  let Φ : V →ₗ[E] (Fin r → E) := LinearMap.pi (fun a => h (e a))
  have hΦ : ∀ y a, Φ y a = h (e a) y := fun y a => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    apply hφ0
    have hvan : ∀ y, ∑ a, φ (Pi.single a 1) * h (e a) y = 0 := by
      intro y
      have hcomp : φ ∘ₗ Φ = 0 := by
        rw [← LinearMap.range_eq_bot, LinearMap.range_comp, hφ]
      have h0 : φ (Φ y) = 0 := LinearMap.congr_fun hcomp y
      rw [← h0]
      conv_rhs => rw [pi_eq_sum_univ (Φ y)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul, hΦ, mul_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 2; ext j; simp [Pi.single_apply, eq_comm]
    have hz : ∑ a, star (φ (Pi.single a 1)) • e a = 0 := hnd _ (fun y => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, starRingEnd_apply, star_star]
      exact hvan y)
    have hc := Fintype.linearIndependent_iff.1 he _ hz
    ext a
    have := hc a
    simpa using this
  choose g hg using fun b : Fin r => hsurj (Pi.single b 1)
  have hge : ∀ a b, h (e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hΦ, hg b, Pi.single_apply]
  have hg'e : ∀ a b, h (g a) (e b) = if b = a then 1 else 0 := by
    intro a b; rw [← hsymm, hge b a]; split_ifs <;> simp
  refine ⟨fun b => g b - ∑ c, (h (g c) (g b) / 2) • e c, ?_, ?_⟩
  · intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, smul_eq_mul, hee, mul_zero, Finset.sum_const_zero, sub_zero, hge]
  · intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply, RingHom.id_apply, Finset.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hee, hge, hg'e, mul_zero, Finset.sum_const_zero, sub_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply]
    have hM : star (h (g b) (g a)) = h (g a) (g b) := hsymm _ _
    have h2 : star (2 : E) = 2 := by simp
    rw [star_div₀, hM, h2]
    have : (2 : E) ≠ 0 := two_ne_zero
    field_simp
    ring

theorem diag_isometry {E V : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E) (hsymm : ∀ x y, star (h x y) = h y x)
    (hnd : ∀ x, (∀ y, h x y = 0) → x = 0) {r : ℕ} (e f : Fin r → V)
    (hee : ∀ a b, h (e a) (e b) = 0) (hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0)
    (hff : ∀ a b, h (f a) (f b) = 0) (α : Fin r → E) (hα : ∀ a, α a ≠ 0) :
    ∃ t : V ≃ₗ[E] V, (∀ x y, h (t x) (t y) = h x y) ∧ (∀ a, t (e a) = α a • e a) ∧
      ∀ x, (∀ a, h (e a) x = 0) → t x - x ∈ Submodule.span E (Set.range e) := by
  classical
  set β : Fin r → E := fun a => (star (α a))⁻¹ with hβ
  have hβ1 : ∀ a, star (β a) * α a = 1 := by
    intro a; simp only [hβ, star_inv₀, star_star]; exact inv_mul_cancel₀ (hα a)
  have hβ2 : ∀ a, star (α a) * β a = 1 := by
    intro a; simp only [hβ]; exact mul_inv_cancel₀ (star_ne_zero.2 (hα a))
  have hfe : ∀ a b, h (f a) (e b) = if a = b then 1 else 0 := by
    intro a b; rw [← hsymm, hef b a]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]
  let L : V →ₗ[E] V := LinearMap.id + ∑ a, (α a - 1) • (h (f a)).smulRight (e a) +
    ∑ a, (β a - 1) • (h (e a)).smulRight (f a)
  have hL : ∀ x, L x = x + ∑ a, ((α a - 1) * h (f a) x) • e a + ∑ a, ((β a - 1) * h (e a) x) • f a := by
    intro x; simp [L, LinearMap.sum_apply, mul_smul]
  have key_e : ∀ b y, h (e b) (L y) = β b * h (e b) y := by
    intro b y
    rw [hL]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, hee, hef, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_f : ∀ b y, h (f b) (L y) = α b * h (f b) y := by
    intro b y
    rw [hL]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, hff, hfe, mul_zero, Finset.sum_const_zero, add_zero,
      mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have key_x : ∀ x y, h x (L y) = h x y + ∑ a, ((α a - 1) * h (f a) y) * star (h (e a) x) +
      ∑ a, ((β a - 1) * h (e a) y) * star (h (f a) x) := by
    intro x y
    rw [hL]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, hsymm]
  have hiso : ∀ x y, h (L x) (L y) = h x y := by
    intro x y
    rw [hL x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), LinearMap.add_apply, map_sum, Finset.sum_apply, LinearMap.sum_apply, map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul, key_e, key_f, key_x, RingHom.id_apply, starRingEnd_apply]
    have : ∀ a, ((α a - 1) * h (f a) y) * star (h (e a) x) + ((β a - 1) * h (e a) y) * star (h (f a) x) +
        star ((α a - 1) * h (f a) x) * (β a * h (e a) y) + star ((β a - 1) * h (e a) x) * (α a * h (f a) y) = 0 := by
      intro a
      simp only [star_mul', star_sub, star_one]
      linear_combination (star (h (e a) x) * h (f a) y) * hβ1 a + (star (h (f a) x) * h (e a) y) * hβ2 a
    have hsum := Finset.sum_eq_zero (s := Finset.univ) (fun a _ => this a)
    simp only [Finset.sum_add_distrib] at hsum
    linear_combination hsum
  have hinj : Function.Injective L := by
    intro x y hxy
    have : x - y = 0 := hnd _ (fun z => by
      rw [← hiso, map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply])
    exact sub_eq_zero.1 this
  refine ⟨LinearEquiv.ofInjectiveEndo L hinj, ?_, ?_, ?_⟩
  · intro x y; simpa using hiso x y
  · intro a
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hfe, hee, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, mul_ite, mul_one,
      ite_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_smul, one_smul]; abel
  · intro x hx
    simp only [LinearEquiv.coe_ofInjectiveEndo]
    rw [hL]
    simp only [hx, mul_zero, zero_smul, Finset.sum_const_zero, add_zero, add_sub_cancel_left]
    exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem flag_torus (D : D7) (T : D.host.E) (F0 : FlagG (VS D) D.R.rS T) (γ : GV D) (hγ : γ ∈ stabF D F0) :
    ∃ t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, (∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X) ∧
      Adapt (t * γ) (lf D F0) (lf D F0) := by
  obtain ⟨hγi, hγX, hγz⟩ := hγ
  have hsymm : ∀ x y, star ((VS D).hT x y) = (VS D).hT y x := fun x y => (VS D).herm.eq x y
  have hnd : ∀ x, (∀ y, (VS D).hT x y = 0) → x = 0 := fun x hx => (VS D).nondeg.1 x hx
  obtain ⟨f, hef, hff⟩ := witt_partners (VS D).hT hsymm hnd F0.e F0.e_indep F0.e_iso

  have hXa_succ : ∀ i : Fin D.R.rS, F0.Xa ((i : ℕ) + 1) = F0.Xa i ⊔ Submodule.span D.host.E {F0.e i} := by
    intro i
    have : {j : Fin D.R.rS | (j : ℕ) < (i : ℕ) + 1} = {j : Fin D.R.rS | (j : ℕ) < i} ∪ ({i} : Set (Fin D.R.rS)) := by
      ext j; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · intro hj; rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact Or.inl h
        · exact Or.inr (Fin.ext h)
      · rintro (h | rfl) <;> omega
    simp only [FlagG.Xa, this, Set.image_union, Set.image_singleton, Submodule.span_union]
  have hXa_top : F0.Xa D.R.rS = F0.X := by
    have : {j : Fin D.R.rS | (j : ℕ) < D.R.rS} = Set.univ := by ext j; simp [j.2]
    simp only [FlagG.Xa, FlagG.X, this, Set.image_univ]
  have he_mem : ∀ i : Fin D.R.rS, F0.e i ∈ F0.Xa ((i : ℕ) + 1) := fun i =>
    Submodule.subset_span ⟨i, by simp, rfl⟩
  have he_not : ∀ i : Fin D.R.rS, F0.e i ∉ F0.Xa i := fun i =>
    F0.e_indep.notMem_span_image (s := {j | (j : ℕ) < i}) (x := i) (by simp)
  have hdiag : ∀ i : Fin D.R.rS, ∃ u : D.host.E, u ≠ 0 ∧ γ (F0.e i) - u • F0.e i ∈ F0.Xa i := by
    intro i
    have h1 : γ (F0.e i) ∈ F0.Xa ((i : ℕ) + 1) := by
      rw [← hγX ((i : ℕ) + 1)]; exact Submodule.mem_map_of_mem (he_mem i)
    rw [hXa_succ i, Submodule.mem_sup] at h1
    obtain ⟨y, hy, w, hw, hyw⟩ := h1
    obtain ⟨u, rfl⟩ := Submodule.mem_span_singleton.1 hw
    refine ⟨u, ?_, ?_⟩
    · rintro rfl
      apply he_not i
      have : γ (F0.e i) ∈ (F0.Xa i).map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) := by
        rw [hγX i, ← hyw]; simpa using hy
      obtain ⟨w', hw', hw'e⟩ := Submodule.mem_map.1 this
      have : w' = F0.e i := γ.injective hw'e
      exact this ▸ hw'
    · rw [← hyw]; simpa using hy
  choose u hu0 hu using hdiag
  obtain ⟨t, ht_iso, ht_e, ht_perp⟩ := diag_isometry (VS D).hT hsymm hnd F0.e f F0.e_iso hef hff
    (fun i => (u i)⁻¹) (fun i => inv_ne_zero (hu0 i))
  have ht_mem : t ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun x y => ht_iso x y
  have ht_Xa : ∀ (j : ℕ), ∀ y ∈ F0.Xa j, t y ∈ F0.Xa j := by
    intro j y hy
    have : F0.Xa j ≤ (F0.Xa j).comap (t : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [FlagG.Xa, Submodule.span_le]
      rintro _ ⟨k, hk, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, ht_e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    exact this hy
  have hperp : ∀ x ∈ perpS (VS D) F0.X, t x - x ∈ F0.X := by
    intro x hx
    exact ht_perp x (fun a => hx (F0.e a) (Submodule.subset_span ⟨a, rfl⟩))
  refine ⟨t, ht_mem, hperp, Subgroup.mul_mem _ ht_mem hγi, ?_⟩
  intro a
  induction a using Fin.lastCases with
  | last =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_last, Fin.val_last, LinearEquiv.mul_apply, hγz, Xflag]
    rw [hXa_top]
    exact hperp _ (fun x hx => by
      have := Submodule.span_le (p := LinearMap.ker ((VS D).hT.flip F0.z)) |>.2 (by
        rintro _ ⟨a, rfl⟩; simpa using F0.z_orth a) hx
      simpa using this)
  | cast i =>
    simp only [frame, lf, FlagG.fvec, Fin.snoc_castSucc, Fin.coe_castSucc, LinearEquiv.mul_apply, Xflag]
    have : γ (F0.e i) = (γ (F0.e i) - u i • F0.e i) + u i • F0.e i := by abel
    rw [this, map_add (f := _), map_smul, ht_e, smul_smul, mul_inv_cancel₀ (hu0 i), one_smul, add_sub_cancel_right]
    exact ht_Xa _ _ (hu i)

end GlobalTheory.FlagTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentQuotientInvariantProbability
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
open scoped InnerProductSpace

namespace GlobalTheory.UnipQuot

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem exists_domain (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧ ∀ x : G, ∃! γ : Γ, γ • x ∈ D := by
  obtain ⟨ψ, hψm, hψi⟩ := MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated G
  have he := measurableEmbedding_embeddingReal (ℕ → Bool)
  set φ : G → ℝ := fun x => embeddingReal (ℕ → Bool) (ψ x) with hφ
  have hφm : Measurable φ := he.measurable.comp hψm
  have hφi : Function.Injective φ := he.injective.comp hψi
  have hCm : MeasurableSet C := hC.measurableSet
  refine ⟨C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)}, ?_, Set.inter_subset_left, ?_⟩
  · refine hCm.inter (MeasurableSet.iInter fun γ => ?_)
    have h1 : MeasurableSet {y : G | (γ : G) * y ∈ C} := (measurable_const_mul (γ : G)) hCm
    have h2 : MeasurableSet {y : G | φ y ≤ φ ((γ : G) * y)} :=
      measurableSet_le hφm (hφm.comp (measurable_const_mul (γ : G)))
    have : {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} =
        {y : G | (γ : G) * y ∈ C}ᶜ ∪ {y : G | φ y ≤ φ ((γ : G) * y)} := by
      ext y; simp [imp_iff_not_or]
    rw [this]; exact h1.compl.union h2
  · intro x
    have hK : IsCompact ((fun y => y * x⁻¹) '' C) := hC.image (continuous_mul_const _)
    have hF := hfin _ hK
    obtain ⟨γ₀, hγ₀, hγ₀C⟩ := hcov x
    have hne : ((fun y => y * x⁻¹) '' C ∩ (Γ : Set G)).Nonempty :=
      ⟨γ₀, ⟨γ₀ * x, hγ₀C, by simp⟩, hγ₀⟩
    obtain ⟨γ, ⟨⟨y, hy, hyγ⟩, hγΓ⟩, hmin⟩ := Set.exists_min_image _ (fun g => φ (g * x)) hF hne
    have hγx : γ * x ∈ C := by rw [← hyγ]; simpa using hy
    have hmem : (⟨γ, hγΓ⟩ : Γ) • x ∈
        C ∩ ⋂ γ : Γ, {y | (γ : G) * y ∈ C → φ y ≤ φ ((γ : G) * y)} := by
      refine ⟨hγx, Set.mem_iInter.2 fun δ hδ => ?_⟩
      have hδ' : (δ : G) * (γ * x) ∈ C := hδ
      have := hmin ((δ : G) * γ) ⟨⟨_, hδ', by simp [mul_assoc]⟩, Γ.mul_mem δ.2 hγΓ⟩
      show φ (γ * x) ≤ φ ((δ : G) * (γ * x))
      simpa [mul_assoc] using this
    refine ⟨⟨γ, hγΓ⟩, hmem, fun δ hδ => ?_⟩
    have hδC : (δ : G) * x ∈ C := hδ.1
    have h1 : φ ((δ : G) * x) ≤ φ (γ * x) := by
      have := Set.mem_iInter.1 hδ.2 ⟨γ * (δ : G)⁻¹, Γ.mul_mem hγΓ (Γ.inv_mem δ.2)⟩
      have e : γ * (δ : G)⁻¹ * (δ • x) = γ * x := by
        show γ * (δ : G)⁻¹ * ((δ : G) * x) = γ * x
        simp [mul_assoc]
      simp only [Set.mem_ofPred_eq, e] at this
      exact this hγx
    have h2 : φ (γ * x) ≤ φ ((δ : G) * x) := hmin δ ⟨⟨_, hδC, by simp⟩, δ.2⟩
    exact Subtype.ext (mul_right_cancel (hφi (le_antisymm h1 h2)))

theorem exists_prob [LocallyCompactSpace G] (Γ : Subgroup G) [Countable Γ]
    (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m : G, ∃ γ ∈ Γ, γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ y, f (γ * y) = f y) → ∀ g : G, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  obtain ⟨D, hDm, hDC, hD⟩ := exists_domain Γ hfin C hC hcov
  set μ : Measure G := Measure.haar
  have hfd : IsFundamentalDomain Γ D μ := IsFundamentalDomain.mk' hDm.nullMeasurableSet hD
  have hfd' : ∀ g : G, IsFundamentalDomain Γ ((fun y => y * g) ⁻¹' D) μ := fun g =>
    IsFundamentalDomain.mk' ((measurable_mul_const g) hDm).nullMeasurableSet fun x => by
      have := hD (x * g)
      simpa [Subgroup.smul_def, mul_assoc] using this
  have h0 : μ D ≠ 0 := hfd.measure_ne_zero (NeZero.ne μ)
  have htop : μ D ≠ ⊤ := ne_top_of_le_ne_top hC.measure_lt_top.ne (measure_mono hDC)
  have hinv : ∀ g : G, Measure.map (fun y => y * g) μ = μ := by
    intro g
    have : IsFiniteMeasureOnCompacts (Measure.map (fun y => y * g) μ) := ⟨fun K hK => by
      rw [Measure.map_apply (measurable_mul_const g) hK.measurableSet]
      exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top⟩
    have h := Measure.isMulLeftInvariant_eq_smul (Measure.map (fun y => y * g) μ) μ
    set c := (Measure.map (fun y => y * g) μ).haarScalarFactor μ
    have h1 : Measure.map (fun y => y * g) μ D = μ D := by
      rw [Measure.map_apply (measurable_mul_const g) hDm]
      exact (hfd' g).measure_eq hfd
    rw [h] at h1
    have h2 : (c : ENNReal) = 1 := by
      have : (c : ENNReal) * μ D = 1 * μ D := by simpa using h1
      exact (ENNReal.mul_left_inj h0 htop).1 this
    have h3 : c = 1 := by exact_mod_cast h2
    rw [h, h3, one_smul]
  refine ⟨(μ D)⁻¹ • μ.restrict D, ⟨?_⟩, ?_, ?_⟩
  · simp [ENNReal.inv_mul_cancel h0 htop]
  · have : Cᶜ ∩ D = ∅ := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
      exact fun h1 h2 => h1 (hDC h2)
    rw [smul_apply, Measure.restrict_apply hC.measurableSet.compl, this]
    simp
  · intro f hf g
    rw [integral_smul_measure, integral_smul_measure]
    congr 1
    have hemb : MeasurableEmbedding (fun y : G => y * g) := measurableEmbedding_mulRight g
    have h1 := hemb.setIntegral_map (μ := μ) f ((fun y => y * g⁻¹) ⁻¹' D)
    have h2 : (fun y : G => y * g) ⁻¹' ((fun y => y * g⁻¹) ⁻¹' D) = D := by
      ext y; simp
    rw [hinv g, h2] at h1
    rw [← h1]
    exact (hfd' g⁻¹).setIntegral_eq hfd fun γ x => hf γ γ.2 x

theorem exists_prob_subgroup [LocallyCompactSpace G] (N Γ : Subgroup G) (hN : IsClosed (N : Set G))
    [Countable Γ] (hfin : ∀ K : Set G, IsCompact K → (K ∩ (Γ : Set G)).Finite)
    (C : Set G) (hC : IsCompact C) (hcov : ∀ m ∈ N, ∃ γ ∈ Γ, γ ∈ N ∧ γ * m ∈ C) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν Cᶜ = 0 ∧ ν (N : Set G)ᶜ = 0 ∧
      ∀ f : G → ℂ, (∀ γ ∈ Γ, γ ∈ N → ∀ y, f (γ * y) = f y) →
        ∀ g ∈ N, ∫ m, f (m * g) ∂ν = ∫ m, f m ∂ν := by
  have hce : Topology.IsClosedEmbedding (Subtype.val : N → G) := hN.isClosedEmbedding_subtypeVal
  have : LocallyCompactSpace N := hce.locallyCompactSpace
  have : SecondCountableTopology N := hce.isEmbedding.secondCountableTopology
  have hemb : MeasurableEmbedding (Subtype.val : N → G) := hce.measurableEmbedding
  have : Countable (Γ.subgroupOf N) := by
    refine Function.Injective.countable (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ)) ?_
    intro a b h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : Γ => (z : G)) h))
  obtain ⟨ν, hν, hνC, hνf⟩ := exists_prob (Γ.subgroupOf N) (fun K hK => by
      have := hfin _ (hK.image continuous_subtype_val)
      refine (this.preimage (f := (Subtype.val : N → G)) Subtype.val_injective.injOn).subset ?_
      rintro x ⟨hx, hx'⟩
      exact ⟨⟨x, hx, rfl⟩, hx'⟩)
    (Subtype.val ⁻¹' C) (hce.isCompact_preimage hC) (fun m => by
      obtain ⟨γ, h1, h2, h3⟩ := hcov m m.2
      exact ⟨⟨γ, h2⟩, h1, h3⟩)
  refine ⟨ν.map Subtype.val, (by letI := hν; infer_instance), ?_, ?_, ?_⟩
  · rw [hemb.map_apply]; exact hνC
  · rw [hemb.map_apply]
    have : (Subtype.val : N → G) ⁻¹' (N : Set G)ᶜ = ∅ := by
      ext y; simp
    rw [this, measure_empty]
  · intro f hf g hg
    rw [hemb.integral_map, hemb.integral_map]
    exact hνf (fun y => f y) (fun γ hγ y => hf γ hγ γ.2 y) ⟨g, hg⟩

end General

theorem exists_quot_prob (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (hW : I.IsIsot W) :
    ∃ ν : Measure I.GA, IsProbabilityMeasure ν ∧ I.IsNQuotMeas W ν ∧
      ∃ Cp : Set I.GA, IsCompact Cp ∧ Cp ⊆ I.NA W ∧ ν Cpᶜ = 0 := by
  obtain ⟨h2, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I
  obtain ⟨⟨N, hN⟩, hcl, -, -, C, hC, hCN, hcov⟩ := _root_.GlobalTheory.UnipApprox.strong_approximation I W hW
  obtain ⟨Γ, hΓ, hΓc, hfin, -⟩ := _root_.GlobalTheory.RatDiscrete.rational_points I
  have : BorelSpace I.GA := inferInstance
  have mN : ∀ x, x ∈ N ↔ x ∈ I.NA W := fun x => by rw [← hN]; rfl
  have mΓ : ∀ x, x ∈ Γ ↔ x ∈ I.GFset := fun x => by rw [← hΓ]; rfl
  obtain ⟨ν, hν, hνC, hνN, hf⟩ := exists_prob_subgroup N Γ (hN ▸ hcl) (hΓ ▸ hfin) C hC (fun m hm => by
    obtain ⟨γ, ⟨h1, h1'⟩, h3⟩ := hcov m ((mN m).1 hm)
    exact ⟨γ⁻¹, Γ.inv_mem ((mΓ γ).2 h1), N.inv_mem ((mN γ).2 h1'), h3⟩)
  refine ⟨ν, hν, ⟨inferInstance, IsProbabilityMeasure.ne_zero ν, hN ▸ hνN, ?_⟩, C, hC, hCN, hνC⟩
  intro f hfi g hg
  exact hf f (fun γ h1 h1' y => hfi γ ⟨(mΓ γ).1 h1, (mN γ).1 h1'⟩ y) g ((mN g).2 hg)

end GlobalTheory.UnipQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ExtContRep

theorem comp_rep_ae_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Set G) (hΓ : Γ.Countable) (D : Set G) (hD : MeasurableSet D)
    (r : G → G) (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ r y ∈ D) (F f : G → ℂ)
    (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) (h : F =ᵐ[μ.restrict D] f) :
    (fun y => F (r y)) =ᵐ[μ] f := by
  have h1 : ∀ᵐ x ∂μ, x ∈ D → F x = f x := (ae_restrict_iff' hD).1 h
  have h2 : ∀ᵐ x ∂μ, ∀ γ ∈ Γ, γ * x ∈ D → F (γ * x) = f (γ * x) :=
    (ae_ball_iff hΓ).2 fun γ _ => (measurePreserving_mul_left μ γ).quasiMeasurePreserving.ae h1
  filter_upwards [h2] with x hx
  obtain ⟨γ, hγ, e, hm⟩ := hr x
  rw [e] at hm ⊢
  rw [hx γ hγ hm, hf γ hγ]

theorem ae_ae_mul {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (μ ν : Measure G)
    [μ.IsMulLeftInvariant] [SFinite μ] [SFinite ν] (p : G → Prop) (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, p (m * x) := by
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h0 : ∀ᵐ x ∂μ, x ∉ Z := measure_eq_zero_iff_ae_notMem.1 hZ0
  have hm : MeasurableSet {z : G × G | z.2 * z.1 ∉ Z} :=
    (measurable_snd.mul measurable_fst) hZm.compl
  have h1 : ∀ᵐ x ∂μ, ∀ᵐ m ∂ν, m * x ∉ Z :=
    (Measure.ae_ae_comm (p := fun x m => m * x ∉ Z) hm).2
      (Filter.Eventually.of_forall fun m =>
        (measurePreserving_mul_left μ m).quasiMeasurePreserving.ae h0)
  filter_upwards [h1] with x hx
  filter_upwards [hx] with m hmx
  by_contra hp
  exact hmx (hZ hp)

theorem ext_ae_eq_contRep : ∀ (B : RowsAut) (y : B.I.L2 B.μf B.fund) (f : B.I.GA → ℂ), IsContRep B y f → B.I.ext y =ᵐ[B.I.muA B.μf] f ∧ (∀ f', IsContRep B y f' → f' = f) ∧ (∀ g, IsContRep B (B.R g y) (fun x => f (x * g))) ∧ ∀ ν : Measure B.I.GA, IsFiniteMeasure ν → ∀ᵐ x ∂(B.I.muA B.μf), ∀ᵐ m ∂ν, B.I.ext y (m * x) = f (m * x) := by
  intro B y f hf
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨Γ, hΓ, hc, -, -⟩ := GlobalTheory.RatDiscrete.rational_points B.I
  obtain ⟨hl, hrt, -, -, hop⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : (B.I.muA B.μf).IsMulRightInvariant := ⟨hrt⟩
  have : (B.I.muA B.μf).IsOpenPosMeasure := ⟨fun U hU hne => (hop U hU hne).ne'⟩
  have : SFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hcount : B.I.GFset.Countable := by
    rw [← hΓ]; exact Set.countable_coe_iff.1 hc
  have hr : ∀ z, ∃ γ ∈ B.I.GFset, B.I.rep B.fund z = γ * z ∧ B.I.rep B.fund z ∈ B.fund := by
    intro z
    have h := B.fund_spec.2.1 z
    have e : B.I.rep B.fund z = h.choose * z := by
      unfold AutInst.rep; exact dif_pos h
    exact ⟨h.choose, h.choose_spec.1, e, e ▸ h.choose_spec.2⟩
  have key : ∀ f', IsContRep B y f' → B.I.ext y =ᵐ[B.I.muA B.μf] f' := fun f' hf' =>
    comp_rep_ae_eq (B.I.muA B.μf) _ hcount _ B.fund_spec.1 _ hr _ f' hf'.2.1 hf'.2.2
  refine ⟨key f hf, fun f' hf' => ?_, fun g => ⟨?_, ?_, ?_⟩, fun ν hν => ?_⟩
  · exact (Continuous.ae_eq_iff_eq (B.I.muA B.μf) hf'.1 hf.1).1 ((key f' hf').symm.trans (key f hf))
  · exact hf.1.comp (continuous_id.mul continuous_const)
  · intro γ hγ x
    simp only [mul_assoc]
    exact hf.2.1 γ hγ _
  · refine (B.R_spec g y).trans (ae_restrict_of_ae ?_)
    exact (measurePreserving_mul_right (B.I.muA B.μf) g).quasiMeasurePreserving.ae (key f hf)
  · exact ae_ae_mul (B.I.muA B.μf) ν (fun x => B.I.ext y x = f x) (key f hf)

end GlobalTheory.ExtContRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarFrameStabilizerLocalFixerSectionProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_frameStabilizer_local_fixer_section_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ μ0 : Measure (S0 (Fv F v) σ J P), μ0.IsHaarMeasure → (∀ s ∈ Ssub (Fv F v) σ J P, ∀ f : HA (Fv F v) σ J → ℝ≥0∞, Measurable f → ∫⁻ h, f (s * (h : HA (Fv F v) σ J) * s⁻¹) ∂μ0 = ∫⁻ h, f (h : HA (Fv F v) σ J) ∂μ0) → ∀ μU : Measure ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), μU.IsAddHaarMeasure → ∃ μS : Measure (Ssub (Fv F v) σ J P), μS.IsHaarMeasure ∧ ∀ h : HA (Fv F v) σ J → ℝ≥0∞, Measurable h → ∀ t : ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E) → HA (Fv F v) σ J, (∀ x b, lin (Fv F v) σ J (t x) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a)) → ∫⁻ s, h s ∂(amb μS) = ∫⁻ x, ∫⁻ s0, h ((s0 : HA (Fv F v) σ J) * t x) ∂μ0 ∂μU := by
  first | exact @GlobalTheory.HaarSectionProd.haar_S_local | exact GlobalTheory.HaarSectionProd.haar_S_local | (intros; apply GlobalTheory.HaarSectionProd.haar_S_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ a : E ⊗[F] Ad F, a ∈ OAd F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), prV (E := E) v a ∈ intV E v) ∧ (∀ a ∈ OAd F E, ∀ m : ℕ, 0 < m → ∃ x : 𝓞 E, ∃ t ∈ OAd F E, a = inclE (F := F) (Ad F) (x : E) + (m : E ⊗[F] Ad F) * t) ∧ (∀ a : E ⊗[F] Ad F, (∀ m : ℕ, 0 < m → ∃ t ∈ OAd F E, a = (m : E ⊗[F] Ad F) * t) → a = 0) ∧ (∀ a : E ⊗[F] Ad F, ∃ m : ℕ, 0 < m ∧ (m : E ⊗[F] Ad F) * a ∈ OAd F E) ∧ (∀ x : E, inclE (F := F) (Ad F) x ∈ OAd F E ↔ x ∈ intOE E) := by
  first | exact @GlobalTheory.St.G.IntAd.integral_adeles_properties | exact GlobalTheory.St.G.IntAd.integral_adeles_properties | (intros; apply GlobalTheory.St.G.IntAd.integral_adeles_properties <;> assumption)
end

