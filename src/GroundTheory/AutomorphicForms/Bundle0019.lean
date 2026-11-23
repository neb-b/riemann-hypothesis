module

public import Mathlib
public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.AutomorphicForms.QuotientKernel
public import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
public import GroundTheory.AutomorphicForms.TraceClass
public import GroundTheory.AutomorphicForms.Bundle0008
public import GroundTheory.AutomorphicForms.UnitaryRepresentations.IsInvariantIffCommuteStarProjection
public import GroundTheory.AutomorphicForms.Bundle0016
public import GroundTheory.AutomorphicForms.Bundle0018
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.ContragredientTranspose.GelfandKazhdan
public import GroundTheory.AutomorphicForms.ContragredientTranspose.Character
public import GroundTheory.AutomorphicForms.Bundle0017
public import GroundTheory.PowerSubgroups.CountableNeighbourhoods.MapThetaTInvariant
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasureNormOne

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AdmissibleInduction
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure

section General

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {ρ' : Representation ℂ G V'}


omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem isAdmissible_of_injective (hρ : IsSmooth ρ) (hρ' : IsAdmissible ρ')
    (f : Representation.IntertwiningMap ρ ρ') (hf : Function.Injective f) : IsAdmissible ρ := by
  refine ⟨hρ, fun K hKc hKo => ?_⟩
  have := hρ'.2 K hKc hKo
  exact Module.Finite.of_injective (fixedMap ρ f K) (fixedMap_injective ρ hf)

end General

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

section Permute


variable (F) in
def permuteGL (s : Equiv.Perm (Fin n)) : GL (Fin n) F ≃* GL (Fin n) F :=
  Units.mapEquiv (reindexAlgEquiv F F s).toMulEquiv

theorem permuteGL_apply (s : Equiv.Perm (Fin n)) (g : GL (Fin n) F) (i j : Fin n) :
    permuteGL F s g i j = g (s.symm i) (s.symm j) := rfl

theorem permuteGL_mem_integralGL_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ integralGL F n ↔ g ∈ integralGL F n := by
  rw [mem_integralGL_iff, mem_integralGL_iff, ← map_inv]
  simp only [permuteGL_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (s i) (s j)
    · simpa using h2 (s i) (s j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem permuteGL_mem_blockUpper_iff (s : Equiv.Perm (Fin n)) {g : GL (Fin n) F} :
    permuteGL F s g ∈ blockUpper F n β ↔ g ∈ blockUpper F n (β ∘ s) := by
  rw [mem_blockUpper, mem_blockUpper]
  constructor
  · intro h i j hij
    have := @h (s i) (s j) hij
    simpa [permuteGL_apply] using this
  · intro h i j hij
    rw [permuteGL_apply]
    exact h (show β (s (s.symm j)) < β (s (s.symm i)) by simpa using hij)

end Permute

theorem exists_blockUpper_mul_integralGL' (g : GL (Fin n) F) :
    ∃ p ∈ blockUpper F n β, ∃ k ∈ integralGL F n, g = p * k := by
  set s : Equiv.Perm (Fin n) := Tuple.sort β
  have hs : Monotone (β ∘ s) := Tuple.monotone_sort β
  obtain ⟨p, hp, k, hk, hpk⟩ :=
    exists_blockUpper_mul_integralGL F n hs ((permuteGL F s).symm g)
  refine ⟨permuteGL F s p, (permuteGL_mem_blockUpper_iff s).2 hp, permuteGL F s k,
    (permuteGL_mem_integralGL_iff s).2 hk, ?_⟩
  rw [← map_mul, ← hpk, MulEquiv.apply_symm_apply]

theorem isClosed_levi : IsClosed (levi F n β : Set (GL (Fin n) F)) := by
  rw [levi, Subgroup.coe_inf]
  exact (Measures.isClosed_blockUpper F n β).inter
    (Measures.isClosed_blockUpper F n (OrderDual.toDual ∘ β))

theorem sqrtModular_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ integralGL F n) : sqrtModular F n β p = 1 := by
  show ((NNReal.sqrt (modularCharacter p) : ℝ) : ℂ) = 1
  rw [Measures.modularCharacter_eq_one_of_mem_integralGL p hp]
  simp

theorem isCompact_subgroupOf_levi {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) :
    IsCompact ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [Subgroup.coe_subgroupOf]
  exact isClosed_levi.isClosedEmbedding_subtypeVal.isCompact_preimage hK

theorem isOpen_subgroupOf_levi {K : Subgroup (GL (Fin n) F)}
    (hK : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen ((K.subgroupOf (levi F n β) : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [Subgroup.coe_subgroupOf]
  exact hK.preimage continuous_subtype_val

section Admissible

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem apply_mem_fixedVectors {m : ℕ}
    (f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) {k : GL (Fin n) F}
    (hk : k ∈ integralGL F n) :
    ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) k ∈
      fixedVectors σ ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  intro y hy
  rw [Subgroup.mem_subgroupOf] at hy
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 (leviIncl y) k)
  rw [inflateTwist_apply, leviProj_leviIncl,
    sqrtModular_of_mem_integralGL _ (congruenceSubgroup_le F n m hy), one_smul] at h1
  rw [← h1]
  have hc : k⁻¹ * (y : GL (Fin n) F) * k ∈ congruenceSubgroup F n m := by
    simpa using conj_mem_congruenceSubgroup F n ((integralGL F n).inv_mem hk) hy
  have h2 := congrArg (fun x : parabolicIndSpace F n β σ => (x : GL (Fin n) F → W) k)
    (f.2 _ hc)
  simp only [coe_indRep_apply] at h2
  rw [show ((leviIncl y : blockUpper F n β) : GL (Fin n) F) * k = k * (k⁻¹ * (y : GL (Fin n) F) * k)
    by rw [leviIncl_coe]; group]
  exact h2

theorem exists_apply_eq_out (m : ℕ) (x : GL (Fin n) F) :
    ∃ (p : blockUpper F n β) (c : integralGL F n ⧸ (congruenceSubgroup F n m).subgroupOf
      (integralGL F n)), ∀ f : fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m),
      ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) x =
        sqrtModular F n β p • σ (leviProj F n β p)
          (((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : integralGL F n) : GL (Fin n) F)) := by
  obtain ⟨p, hp, k, hk, rfl⟩ := exists_blockUpper_mul_integralGL' (β := β) x
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  set c : K₀ ⧸ Km.subgroupOf K₀ := QuotientGroup.mk (⟨k, hk⟩ : K₀)
  refine ⟨⟨p, hp⟩, c, fun f => ?_⟩
  have h1 := ((f : parabolicIndSpace F n β σ).2.1 ⟨p, hp⟩ k)
  simp only [inflateTwist_apply] at h1
  rw [h1]
  obtain ⟨y, hyk⟩ := QuotientGroup.mk_out_eq_mul (Km.subgroupOf K₀) (⟨k, hk⟩ : K₀)
  have hym : (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) ∈ Km :=
    Subgroup.mem_subgroupOf.1 ((Km.subgroupOf K₀).inv_mem y.2)
  have h2 := congrArg
    (fun z : parabolicIndSpace F n β σ => (z : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F))
    (f.2 _ hym)
  simp only [coe_indRep_apply] at h2
  have h3 : ((Quotient.out c : K₀) : GL (Fin n) F) * (((y : K₀)⁻¹ : K₀) : GL (Fin n) F) = k := by
    have : (Quotient.out c : K₀) = ⟨k, hk⟩ * (y : K₀) := hyk
    rw [this]
    simp
  rw [h3] at h2
  rw [h2]

theorem isAdmissible_parabolicInd (hσ : IsAdmissible σ) : IsAdmissible (parabolicInd F n β σ) := by
  classical
  refine ⟨isSmooth_parabolicInd σ, fun K hKc hKo => ?_⟩
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hKo.mem_nhds K.one_mem)
  have hle : congruenceSubgroup F n m ≤ K := hm
  suffices h : FiniteDimensional ℂ
      (fixedVectors (parabolicInd F n β σ) (congruenceSubgroup F n m)) from
    Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)
  set K₀ := integralGL F n
  set Km := congruenceSubgroup F n m
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 (isCompact_integralGL F n)
  have hQ : Finite (K₀ ⧸ Km.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (isOpen_congruenceSubgroup F n m).preimage continuous_subtype_val
  set L : Subgroup (levi F n β) := Km.subgroupOf (levi F n β)
  have hL : FiniteDimensional ℂ (fixedVectors σ L) :=
    hσ.2 L (isCompact_subgroupOf_levi (isCompact_congruenceSubgroup F n m))
      (isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m))

  let ev : fixedVectors (parabolicInd F n β σ) Km →ₗ[ℂ] (K₀ ⧸ Km.subgroupOf K₀ → fixedVectors σ L) :=
    LinearMap.pi fun c =>
      LinearMap.codRestrict _
        ((LinearMap.proj (((Quotient.out c : K₀) : GL (Fin n) F))).comp
          ((parabolicIndSpace F n β σ).subtype.comp (fixedVectors _ Km).subtype))
        fun f => apply_mem_fixedVectors f (Quotient.out c).2
  have hinj : Function.Injective ev := by
    intro f g hfg
    have hz : ∀ c : K₀ ⧸ Km.subgroupOf K₀,
        ((f : parabolicIndSpace F n β σ) : GL (Fin n) F → W) ((Quotient.out c : K₀) : GL (Fin n) F)
          = ((g : parabolicIndSpace F n β σ) : GL (Fin n) F → W)
            ((Quotient.out c : K₀) : GL (Fin n) F) :=
      fun c => congrArg Subtype.val (congrFun hfg c)
    apply Subtype.ext
    apply Subtype.ext
    funext x
    obtain ⟨p, c, hp⟩ := exists_apply_eq_out (σ := σ) m x
    rw [hp f, hp g, hz c]
  exact FiniteDimensional.of_injective ev hinj

end Admissible

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.CompactFormulaSums
section
open MeasureTheory Topology Filter Set Function
open scoped ENNReal Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace UnitaryRep

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

theorem ccToL1_add (f g : CompactlySupportedContinuousMap G ℂ) :
    ccToL1 μ (f + g) = ccToL1 μ f + ccToL1 μ g := by
  unfold ccToL1
  rw [← MemLp.toLp_add]
  rfl

end UnitaryRep

namespace RightCosetSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (RightCosetSpace Γ)]
  (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

end RightCosetSpace

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.ContragredientTranspose
section
namespace GroundTheory.Automorphic.ContragredientTranspose

open MeasureTheory Measure GroundTheory.Automorphic.Whittaker

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def subrepCompOrderIso {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (α : G ≃* G) :
    Subrepresentation (ρ.comp α.toMonoidHom) ≃o Subrepresentation ρ where
  toFun W := ⟨W.toSubmodule, fun g v hv => by
    have := W.apply_mem_toSubmodule (α.symm g) hv
    simpa using this⟩
  invFun W := ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (α g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (α : G ≃* G) :
    Representation.IsIrreducible (ρ.comp α.toMonoidHom) :=
  (OrderIso.isSimpleOrder_iff (subrepCompOrderIso ρ α)).2 inferInstance

theorem map_thetaT_eq [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
    (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] :
    μ.map (thetaT : GL (Fin n) F ≃* GL (Fin n) F) = μ :=
  _root_.GroundTheory.Variant₂.N1.map_thetaT_eq_self μ

theorem nonempty_equiv_contragredient {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Nonempty ((contragredient π).Equiv
      (π.comp (thetaT : GL (Fin n) F ≃* GL (Fin n) F).toMonoidHom)) := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  set μ : Measure (GL (Fin n) F) := haar
  have : μ.IsMulRightInvariant := Measures.isMulRightInvariant_GL F n μ
  have : μ.IsInvInvariant := ⟨Measures.inv_eq_self_GL F n μ⟩
  have hc : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F) := continuous_thetaT
  have hc' : Continuous (thetaT : GL (Fin n) F ≃* GL (Fin n) F).symm := continuous_thetaT
  have := isIrreducible_contragredient hπ
  have := isIrreducible_comp π (thetaT : GL (Fin n) F ≃* GL (Fin n) F)
  apply nonempty_equiv_of_distChar_eq (μ := μ) (isAdmissible_contragredient hπ)
    (isAdmissible_comp _ hc hc' hπ)
  refine LinearMap.ext fun f => ?_
  rw [distChar_contragredient, distChar_comp μ _ hc hc' (map_thetaT_eq μ) hπ]
  have e : compHomeoL (mulEquivHomeo (thetaT : GL (Fin n) F ≃* GL (Fin n) F) hc hc').symm f =
      compHomeoL transposeHomeo (compHomeoL (Homeomorph.inv (GL (Fin n) F)) f) :=
    Subtype.ext (funext fun x => rfl)
  rw [e, distribution_transpose_invariant (distChar μ π hπ) (fun g f => distChar_biTranslL μ hπ g f)]

noncomputable def longestWeyl : GL (Fin n) F := permGL F (Fin.revPerm (n := n))

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem longestWeyl_mul_self : (longestWeyl : GL (Fin n) F) * longestWeyl = 1 := by
  rw [longestWeyl, ← map_mul]
  have : (Fin.revPerm (n := n)) * Fin.revPerm = 1 := Equiv.ext fun i => by simp
  rw [this, map_one]


omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem thetaT_eq_longestWeyl (g : GL (Fin n) F) :
    thetaT g = longestWeyl * theta g * longestWeyl := by
  have hs : sigma g = longestWeyl * transposeGL g * longestWeyl :=
    Units.ext (by rw [coe_sigma, sigmaMat_eq, Units.val_mul, Units.val_mul, coe_transposeGL]; rfl)
  have hw : (longestWeyl : GL (Fin n) F)⁻¹ = longestWeyl :=
    inv_eq_of_mul_eq_one_right longestWeyl_mul_self
  rw [theta, hs, thetaT_apply]
  simp only [_root_.mul_inv_rev, hw, mul_assoc, longestWeyl_mul_self, mul_one]
  rw [← mul_assoc, longestWeyl_mul_self, one_mul]

theorem rank_whittaker_le_one (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  by_cases h0 : equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F)) = ⊥
  · rw [h0, rank_bot]
    exact zero_le_one
  refine rank_whittaker_le_one_of_contragredient ψ₀ hψ hψ₁ π hπ ?_
  obtain ⟨ℓ, hℓ, hℓ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨E⟩ := nonempty_equiv_contragredient π hπ
  set w₀ : GL (Fin n) F := longestWeyl
  let ℓ' : Module.Dual ℂ (smoothVectors (Representation.dual π)) :=
    ℓ ∘ₗ π w₀ ∘ₗ E.toLinearEquiv.toLinearMap
  have hℓ' : ∀ x, ℓ' x = ℓ (π w₀ (E.toLinearEquiv x)) := fun _ => rfl
  have hmem : ℓ' ∈ equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) := by
    intro u x
    rw [hℓ', hℓ', Representation.Equiv.toLinearEquiv_apply, E.toIntertwiningMap.isIntertwining,
      ← Representation.Equiv.toLinearEquiv_apply]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, thetaT_eq_longestWeyl]
    have e : w₀ * (longestWeyl * theta (u : GL (Fin n) F) * longestWeyl) =
        theta (u : GL (Fin n) F) * w₀ := by
      simp only [w₀, ← mul_assoc, longestWeyl_mul_self, one_mul]
    rw [e, map_mul, Module.End.mul_apply]
    have := hℓ ⟨theta (u : GL (Fin n) F), theta_mem_unipotent u.2⟩ (π w₀ (E.toLinearEquiv x))
    simp only at this
    rw [this, psiN_theta ψ₀ u.2]
  intro hbot
  rw [hbot] at hmem
  have h0' : ℓ' = 0 := (Submodule.mem_bot ℂ).1 hmem
  apply hℓ0
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun φ : Module.Dual ℂ (smoothVectors (Representation.dual π)) =>
    φ (E.toLinearEquiv.symm (π w₀ v))) h0'
  simp only [hℓ', LinearEquiv.apply_symm_apply, LinearMap.zero_apply] at this
  rw [← Module.End.mul_apply, ← map_mul, longestWeyl_mul_self, map_one, Module.End.one_apply]
    at this
  rw [this, LinearMap.zero_apply]

end GroundTheory.Automorphic.ContragredientTranspose
end

-- bundled from GroundTheory.AutomorphicForms.ReductionIdele
section
open NumberField Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup

namespace GroundTheory.Automorphic

namespace Reduction

variable {K : Type*} [Field K] [NumberField K]

theorem exists_isCompact_mul_mem_of_ideleModule_mem_Icc {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∃ S : Set (IdeleGroup K), IsCompact S ∧ ∀ s : IdeleGroup K,
      a ≤ (ideleModule K s : ℝ) → (ideleModule K s : ℝ) ≤ b → ∃ c : Kˣ, diagonal K c * s ∈ S := by
  obtain ⟨D, hD, -, hxD⟩ := exists_isCompact_normOneSubgroup K
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace K) := inferInstance
  set I : Set {r : ℝ // 0 < r} := Subtype.val ⁻¹' Icc a b with hI
  have hIc : IsCompact I := by
    rw [Subtype.isCompact_iff]
    have : Subtype.val '' I = Icc a b := by
      ext r
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ht
      · intro hr
        exact ⟨⟨r, lt_of_lt_of_le ha hr.1⟩, hr, rfl⟩
    rw [this]
    exact isCompact_Icc
  refine ⟨(fun p : IdeleGroup K × {r : ℝ // 0 < r} => p.1 * moduleSection w₀ p.2) '' (D ×ˢ I),
    (hD.prod hIc).image (continuous_fst.mul ((continuous_moduleSection w₀).comp continuous_snd)),
    fun s has hsb => ?_⟩
  obtain ⟨c, hc⟩ := hxD _ (mul_inv_moduleSection_mem w₀ s)
  refine ⟨c, ⟨(diagonal K c * (s * (moduleSection w₀ (ideleModule K s))⁻¹), ideleModule K s),
    ⟨hc, has, hsb⟩, ?_⟩⟩
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Reduction

end GroundTheory.Automorphic
end

