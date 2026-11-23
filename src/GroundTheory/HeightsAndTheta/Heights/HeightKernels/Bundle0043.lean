module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeIndex
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoFirst
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeModPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace DualLatticeModPrimeAlt

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

abbrev locAt (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors

theorem exists_smul_mem (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] (L : Submodule (𝓞 K) (Fin i → K)) {x : Fin i → K}
    (hx : x ∈ Submodule.span (locAt 𝔭) (L : Set (Fin i → K))) :
    ∃ s ∈ 𝔭.primeCompl, s • x ∈ L := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, 𝔭.primeCompl.one_mem, by rwa [one_smul]⟩
  | zero => exact ⟨1, 𝔭.primeCompl.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, hs₁, hx⟩ := hx
    obtain ⟨s₂, hs₂, hy⟩ := hy
    refine ⟨s₁ * s₂, 𝔭.primeCompl.mul_mem hs₁ hs₂, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hx
    · rw [mul_smul]
      exact L.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl a
    refine ⟨q * s, 𝔭.primeCompl.mul_mem q.2 hs, ?_⟩
    have hq : (q : 𝓞 K) • (IsLocalization.mk' (locAt 𝔭) p q) = algebraMap (𝓞 K) (locAt 𝔭) p := by
      rw [Algebra.smul_def, mul_comm, IsLocalization.mk'_spec]
    have e : (q * s) • (IsLocalization.mk' (locAt 𝔭) p q • x) = p • (s • x) := by
      rw [mul_comm, mul_smul, ← smul_assoc (q : 𝓞 K), hq, algebraMap_smul, smul_comm]
    rw [e]
    exact L.smul_mem _ hx

theorem span_dual_eq_top (F : HermLattice K i) :
    Submodule.span K (DualLatticeIndexAlt.dual F.lattice : Set (Fin i → K)) = ⊤ := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_le_box F.lattice F.fg
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  have hbox : DualLatticeIndexAlt.box (i := i) (algebraMap (𝓞 K) K e) ≤ DualLatticeIndexAlt.dual F.lattice := by
    have := DualLatticeIndexAlt.dual_anti hle
    rwa [DualLatticeIndexAlt.dual_box (inv_ne_zero heK), inv_inv] at this
  rw [eq_top_iff, ← (Pi.basisFun K (Fin i)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hj : (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) ∈ DualLatticeIndexAlt.dual F.lattice := by
    refine hbox (DualLatticeIndexAlt.mem_box.mpr fun l => ?_)
    by_cases hl : l = j
    · subst hl
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hl]⟩
  have e1 : Pi.basisFun K (Fin i) j = (algebraMap (𝓞 K) K e)⁻¹ • (Pi.single j (algebraMap (𝓞 K) K e) : Fin i → K) := by
    ext l
    by_cases hl : l = j
    · subst hl
      simp [heK]
    · simp [Pi.basisFun_apply, hl]
  rw [SetLike.mem_coe, e1]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hj)

theorem dual_le_span (F : HermLattice K i) :
    ∃ u : Fin i → Fin i → K, DualLatticeIndexAlt.dual F.lattice ≤ Submodule.span (𝓞 K) (Set.range u) := by
  obtain ⟨e, he0, hle⟩ := DualLatticeIndexAlt.exists_box_le F.lattice F.span_eq
  have heK : algebraMap (𝓞 K) K e ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr he0
  refine ⟨fun j => Pi.single j (algebraMap (𝓞 K) K e)⁻¹, fun x hx => ?_⟩
  have hx' := DualLatticeIndexAlt.dual_anti hle hx
  rw [DualLatticeIndexAlt.dual_box heK, DualLatticeIndexAlt.mem_box] at hx'
  choose a ha using hx'
  have e1 : x = ∑ j, a j • (Pi.single j (algebraMap (𝓞 K) K e)⁻¹ : Fin i → K) := by
    ext l
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact (ha l).symm
  rw [e1]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end DualLatticeModPrimeAlt


open DualLatticeModPrimeAlt in
theorem DualLatticeModPrime.proof : DualLatticeModPrime.Statement := by
  intro K _ _ i F 𝔭 h𝔭
  classical
  have hbot : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField K)
  have : IsDiscreteValuationRing (locAt 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hbot (locAt 𝔭)
  set D := DualLatticeIndexAlt.dual F.lattice
  set DA := Submodule.span (locAt 𝔭) (D : Set (Fin i → K))
  obtain ⟨u, hu⟩ := dual_le_span F
  have hDA : DA ≤ Submodule.span (locAt 𝔭) (Set.range u) :=
    Submodule.span_le.mpr fun x hx =>
      Submodule.span_le_restrictScalars (𝓞 K) (locAt 𝔭) _ (hu hx)
  have := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range u)) (R := locAt 𝔭)
  have : Module.Finite (locAt 𝔭) DA := Module.Finite.iff_fg.mpr (isNoetherian_submodule.mp this DA hDA)
  have : Module.IsTorsionFree (locAt 𝔭) DA := inferInstance
  let b := Module.Free.chooseBasis (locAt 𝔭) DA
  have hspan : Submodule.span K (Set.range fun j => (b j : Fin i → K)) = ⊤ := by
    rw [eq_top_iff, ← span_dual_eq_top F, Submodule.span_le]
    intro d hd
    have e0 : d = ∑ j, ((b.repr ⟨d, Submodule.subset_span hd⟩ j • b j : DA) : Fin i → K) := by
      rw [← Submodule.coe_sum, b.sum_repr]
    rw [e0, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Submodule.coe_smul]
    exact Submodule.span_le_restrictScalars (locAt 𝔭) K _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have hcard : Fintype.card (Fin i) ≤ Fintype.card (Module.Free.ChooseBasisIndex (locAt 𝔭) DA) := by
    have := finrank_range_le_card (R := K) fun j => (b j : Fin i → K)
    rw [Set.finrank, hspan, finrank_top, Module.finrank_fin_fun] at this
    simpa using this
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hcard
  let ρ : locAt 𝔭 →+* 𝓞 K ⧸ 𝔭 := IsLocalization.lift (M := 𝔭.primeCompl) (g := Ideal.Quotient.mk 𝔭)
    fun s => by
      obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv (I := 𝔭) (a := Ideal.Quotient.mk 𝔭 s)
        fun h => s.2 (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact ⟨⟨_, c, hc, by rw [mul_comm]; exact hc⟩, rfl⟩
  have hρ : ∀ a, ρ (algebraMap (𝓞 K) (locAt 𝔭) a) = Ideal.Quotient.mk 𝔭 a := fun a =>
    IsLocalization.lift_eq _ _
  have incl : ∀ φ : dualLattice F, (φ : Fin i → K) ∈ DA := fun φ => Submodule.subset_span φ.2
  let ι : dualLattice F →+ DA := AddMonoidHom.mk' (fun φ => ⟨φ, incl φ⟩) fun _ _ => rfl
  let τ : DA →+ (Fin i → 𝓞 K ⧸ 𝔭) := AddMonoidHom.mk' (fun x l => ρ (b.repr x (g l)))
    fun x y => by funext l; simp [map_add (f := _)]
  have hsmul : ∀ (μ : 𝓞 K) (x : DA), ((algebraMap (𝓞 K) (locAt 𝔭) μ • x : DA) : Fin i → K) =
      algebraMap (𝓞 K) K μ • (x : Fin i → K) := fun μ x => by
    rw [Submodule.coe_smul, algebraMap_smul, algebraMap_smul]
  refine ⟨τ.comp ι, ?_, ?_⟩
  · intro v
    let w : Module.Free.ChooseBasisIndex (locAt 𝔭) DA → 𝓞 K ⧸ 𝔭 := Function.extend g v 0
    choose a ha using fun j => Ideal.Quotient.mk_surjective (I := 𝔭) (w j)
    let x : DA := ∑ j, algebraMap (𝓞 K) (locAt 𝔭) (a j) • b j
    have hx : ∀ j, b.repr x j = algebraMap (𝓞 K) (locAt 𝔭) (a j) := by
      intro j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [x, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem 𝔭 D x.2
    have hs0 : Ideal.Quotient.mk 𝔭 s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨c, hc⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (I := 𝔭) c
    refine ⟨⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩, ?_⟩
    have e1 : ι ⟨t • s • (x : Fin i → K), D.smul_mem t hsx⟩ = algebraMap (𝓞 K) (locAt 𝔭) (t * s) • x := by
      apply Subtype.ext
      rw [hsmul, algebraMap_smul, mul_smul]
      rfl
    funext l
    have key : ∀ y : DA, τ y l = ρ (b.repr y (g l)) := fun _ => rfl
    rw [AddMonoidHom.comp_apply, e1, key, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, hx, hρ,
      map_mul, ht, mul_comm c, hc, one_mul, ha]
    exact g.injective.extend_apply _ _ _
  · intro μ φ ψ h
    have e1 : ι ψ = algebraMap (𝓞 K) (locAt 𝔭) μ • ι φ := by
      apply Subtype.ext
      rw [hsmul]
      exact h
    funext l
    have key : ∀ x : DA, τ x l = ρ (b.repr x (g l)) := fun _ => rfl
    rw [Pi.smul_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, e1, key, key, map_smul,
      Finsupp.smul_apply, smul_eq_mul, map_mul, hρ, smul_eq_mul]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcBaseLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalBaseBound

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]

theorem centre_mem {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')} {a : T → ℤ}
    (hab : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {k : Type} [Field k] {α : T → k}
    {M : T → Fin i → k} (hres : IsExcResidueData b b' α M) (t : T) :
    C (a t) * graphFirst t ∈ linPrime α M := by
  obtain ⟨ρ, ρ', σ, -, -, -, hker, -, -, hα, -⟩ := hres
  have hmem : ((a t • b' t : dualLattice F') : Fin i → K) ∈ dualLattice F := by
    rw [Submodule.coe_smul_of_tower, ← hab t]
    exact (b t).2
  have h0 : ((a t : ℤ) : k) * α t = 0 := by
    rw [hα t, ← zsmul_eq_mul, ← map_zsmul]
    exact (hker _).mpr hmem
  have h1 : linPointMap α M (C (a t)) = C ((a t : k)) := by simp [linPointMap]
  rw [linPrime, RingHom.mem_ker, map_mul, h1, LinPrimeExample.linPointMap_first, ← mul_assoc, ← C_mul, h0, C_0,
    zero_mul]

end StackedExceptionalBaseBound


open StackedExceptionalBaseBound in
theorem DualStackedExcBaseLe.proof (hBihom : DualStackedGraphBihomog.Statement)
    (hLead : DualStackedExcLeadForm.Statement) : DualStackedExcBaseLe.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab k _ α M hres
  refine sup_le ?_ ?_
  · intro f hf
    obtain ⟨s, g, rfl, hg⟩ := hBihom K i F F' T b b' a hab f hf
    set_option synthInstance.maxHeartbeats 100000 in
      rw [linPrime, RingHom.mem_ker, map_sum]
    exact Finset.sum_eq_zero fun p hp =>
      hLead K i F F' T b b' a hi hlt hcov hab k α M hres p.1 p.2 (g p) (hg p hp).1 (hg p hp).2
  · rw [Ideal.span_le, Set.range_subset_iff]
    exact centre_mem hab hres

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcResidueExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField StackedExceptionalFirstGeometric

noncomputable section

namespace StackedExceptionalResidueExists

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i}

theorem exists_mem_not_mem (hlt : F'.lattice < F.lattice) :
    ∃ φc ∈ dualLattice F', φc ∉ dualLattice F := by
  by_contra! h
  have h1 : (dualLattice F).toAddSubgroup.relIndex (dualLattice F').toAddSubgroup = 1 :=
    AddSubgroup.relIndex_eq_one.mpr fun φ hφ => h φ hφ
  rw [DualLatticeIndex.proof K i F F' hlt.le] at h1
  have h2 := AddSubgroup.relIndex_eq_one.mp h1
  exact hlt.not_ge fun x hx => h2 hx

def annIdeal (F : HermLattice K i) (φc : Fin i → K) : Ideal (𝓞 K) where
  carrier := {μ | algebraMap (𝓞 K) K μ • φc ∈ dualLattice F}
  add_mem' {a b} ha hb := by
    show algebraMap (𝓞 K) K (a + b) • φc ∈ dualLattice F
    rw [map_add (f := _), add_smul]
    exact add_mem ha hb
  zero_mem' := by
    show algebraMap (𝓞 K) K 0 • φc ∈ dualLattice F
    rw [map_zero, zero_smul]
    exact zero_mem _
  smul_mem' c x hx := by
    show algebraMap (𝓞 K) K (c * x) • φc ∈ dualLattice F
    rw [map_mul, mul_smul]
    exact smul_mem_dual F c hx

theorem mem_annIdeal {φc : Fin i → K} {μ : 𝓞 K} :
    μ ∈ annIdeal F φc ↔ algebraMap (𝓞 K) K μ • φc ∈ dualLattice F := Iff.rfl

theorem annIdeal_isMaximal (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) : (annIdeal F φc).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hc' ?_, fun J x hle hx hxJ => ?_⟩
  · have := mem_annIdeal.mp h
    rwa [map_one, one_smul] at this
  obtain ⟨l, hl⟩ := exists_sub_mem_dual hlt hcov (smul_mem_dual F' x hc) (mem_annIdeal.not.mp hx) hc
  have h1 : 1 - l * x ∈ annIdeal F φc := by
    rw [mem_annIdeal, map_sub, map_one, map_mul, sub_smul, one_smul, mul_smul]
    exact hl
  have h2 := J.add_mem (hle h1) (J.mul_mem_left l hxJ)
  rwa [sub_add_cancel] at h2

theorem mk_eq_of {φc φ : Fin i → K} {l l' : 𝓞 K} (h : φ - algebraMap (𝓞 K) K l • φc ∈ dualLattice F)
    (h' : φ - algebraMap (𝓞 K) K l' • φc ∈ dualLattice F) :
    Ideal.Quotient.mk (annIdeal F φc) l = Ideal.Quotient.mk (annIdeal F φc) l' := by
  rw [Ideal.Quotient.eq, mem_annIdeal, map_sub, sub_smul]
  have e : algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l' • φc =
      (φ - algebraMap (𝓞 K) K l' • φc) - (φ - algebraMap (𝓞 K) K l • φc) := by abel
  rw [e]
  exact sub_mem h' h

def coeff (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') : 𝓞 K :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose

theorem coeff_spec (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') :
    (φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc ∈ dualLattice F :=
  (exists_sub_mem_dual hlt hcov hc hc' φ.2).choose_spec

def rhoDual (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) :
    dualLattice F' →+ 𝓞 K ⧸ annIdeal F φc where
  toFun φ := Ideal.Quotient.mk _ (coeff hlt hcov hc hc' φ)
  map_zero' := by
    rw [← map_zero (Ideal.Quotient.mk (annIdeal F φc))]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' 0) ?_
    rw [map_zero, zero_smul, sub_zero]
    exact zero_mem _
  map_add' φ ψ := by
    rw [← map_add (f := _)]
    refine mk_eq_of (coeff_spec hlt hcov hc hc' (φ + ψ)) ?_
    have e : ((φ + ψ : dualLattice F') : Fin i → K) - algebraMap (𝓞 K) K
        (coeff hlt hcov hc hc' φ + coeff hlt hcov hc hc' ψ) • φc =
        ((φ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' φ) • φc) +
        ((ψ : Fin i → K) - algebraMap (𝓞 K) K (coeff hlt hcov hc hc' ψ) • φc) := by
      rw [Submodule.coe_add, map_add (f := _), add_smul]
      abel
    rw [e]
    exact add_mem (coeff_spec hlt hcov hc hc' φ) (coeff_spec hlt hcov hc hc' ψ)

theorem rhoDual_eq (hlt : F'.lattice < F.lattice)
    (hcov : ∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice)
    {φc : Fin i → K} (hc : φc ∈ dualLattice F') (hc' : φc ∉ dualLattice F) (φ : dualLattice F') (l : 𝓞 K)
    (h : (φ : Fin i → K) - algebraMap (𝓞 K) K l • φc ∈ dualLattice F) :
    rhoDual hlt hcov hc hc' φ = Ideal.Quotient.mk _ l :=
  mk_eq_of (coeff_spec hlt hcov hc hc' φ) h

end StackedExceptionalResidueExists


open StackedExceptionalResidueExists in
theorem DualStackedExcResidueExists.proof (hσ : DualLatticeModPrime.Statement) :
    DualStackedExcResidueExists.Statement := by
  intro K _ _ i F F' T _ _ b b' a _ hlt hcov _
  obtain ⟨φc, hc, hc'⟩ := exists_mem_not_mem hlt
  set 𝔭 := annIdeal F φc with h𝔭
  have hmax : 𝔭.IsMaximal := annIdeal_isMaximal hlt hcov hc hc'
  let _ : Field (𝓞 K ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  obtain ⟨σ, hσs, hσl⟩ := hσ K i F 𝔭 hmax
  set ρ' := rhoDual hlt hcov hc hc' with hρ'
  have hker : ∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F := by
    intro φ
    have hs := coeff_spec hlt hcov hc hc' φ
    change Ideal.Quotient.mk 𝔭 (coeff hlt hcov hc hc' φ) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_annIdeal]
    constructor
    · intro h
      have := add_mem hs h
      rwa [sub_add_cancel] at this
    · intro h
      have := sub_mem h hs
      rwa [sub_sub_cancel] at this
  have hsurj : Function.Surjective ρ' := by
    intro x
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨⟨algebraMap (𝓞 K) K l • φc, smul_mem_dual F' l hc⟩, rhoDual_eq hlt hcov hc hc' _ l ?_⟩
    show algebraMap (𝓞 K) K l • φc - algebraMap (𝓞 K) K l • φc ∈ dualLattice F
    rw [sub_self]
    exact zero_mem _
  have hcard : Nat.card (𝓞 K ⧸ 𝔭) = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup := by
    rw [← DualLatticeIndex.proof K i F F' hlt.le]
    have hk : (dualLattice F).toAddSubgroup.addSubgroupOf (dualLattice F').toAddSubgroup = ρ'.ker := by
      ext φ
      rw [AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_ker, hker]
      rfl
    rw [AddSubgroup.relIndex, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  refine ⟨𝓞 K ⧸ 𝔭, inferInstance, Fintype.ofFinite _, fun t => ρ' (b' t), fun t => σ (b t),
    ⟨Ideal.Quotient.mk 𝔭, ρ', σ, Ideal.Quotient.mk_surjective, hsurj, hσs, hker, ?_, hσl,
      fun t => rfl, fun t => rfl⟩, ?_⟩
  · intro μ φ ψ h
    rw [rhoDual_eq hlt hcov hc hc' ψ (μ * coeff hlt hcov hc hc' φ), map_mul]
    · rfl
    rw [h, map_mul, mul_smul, ← smul_sub]
    exact smul_mem_dual F μ (coeff_spec hlt hcov hc hc' φ)
  · rw [← hcard]
    exact Fintype.card_eq_nat_card

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdModelRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section


open StandardModelDualRank in
theorem DualStdModelRank.proof : DualStdModelRank.Statement := by
  intro K _ _ i T _ _ b Φ₀ _ _ hΦ _ c
  have hrange : Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i)) = Set.range (u K i) := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟩, j⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨⟨(), j⟩, rfl⟩
  rw [hrange] at hΦ
  refine ⟨?_, ?_⟩
  · change dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i ≠ 0
    exact mul_ne_zero (coord_ne_zero b c) S_ne_zero
  have hr : (fun t : T => dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      fun t => w b t * (w b c)⁻¹ := by
    funext t
    change dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i /
      (dualStdModelEmb K i (dualLatticeCoord b ⟨(), c⟩) * dualStdModelS K i) = _
    rw [← div_eq_mul_inv, w, w, mul_div_mul_right (_ * dualStdModelS K i) _ (T_ne_zero (K := K) (i := i))]
  rw [hr]
  let B := Module.finBasis ℚ K
  let M' := Algebra.adjoin Φ₀ (Set.range (embK K i))
  have hM' : Subalgebra.toSubmodule M' = Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) :=
    adjoin_embK_eq_span B Φ₀
  have hfg : (Subalgebra.toSubmodule M').FG := by
    rw [hM']
    exact Submodule.fg_span (Set.finite_range _)
  have hwM' : ∀ t, w b t ∈ M' := fun t => by
    rw [w_eq]
    refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, rfl⟩) ?_
    have hu : u K i j ∈ (algebraMap Φ₀ (dualStdModelField K i)).fieldRange := by
      rw [hΦ]
      exact Subfield.subset_closure ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := RingHom.mem_fieldRange.mp hu
    rw [← hg]
    exact Subalgebra.algebraMap_mem _ g
  have hMM' : Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) ≤ M' := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨t, rfl⟩
    exact Subalgebra.mul_mem _ (hwM' t) (Subalgebra.inv_mem_of_algebraic M' (x := ⟨w b c, hwM' c⟩)
      (IsIntegral.of_mem_of_fg M' hfg _ (hwM' c)).isAlgebraic)
  have hβM : ∀ a, embK K i a ∈ Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹) := fun a => by
    obtain ⟨N, hN, n, hn⟩ := GroundTheory.Heights₂.Heights.StandardModelDualRank.exists_int_comb b c a
    have hNΩ : (N : dualStdModelField K i) ≠ 0 := by
      rw [← map_intCast (embK K i)]
      exact (map_ne_zero_iff _ (embK K i).injective).mpr (Int.cast_ne_zero.mpr hN)
    have he : embK K i a =
        algebraMap Φ₀ _ ((N : Φ₀)⁻¹) * ∑ t, (n t : dualStdModelField K i) * (w b t * (w b c)⁻¹) := by
      rw [map_inv₀, map_intCast]
      simp only [← mul_assoc, ← Finset.sum_mul, hn]
      field_simp [w_ne_zero b c]
    rw [he]
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun t _ =>
      Subalgebra.mul_mem _ (intCast_mem _ _) (Algebra.subset_adjoin ⟨t, rfl⟩))
  have hMeq : Subalgebra.toSubmodule (Algebra.adjoin Φ₀ (Set.range fun t => w b t * (w b c)⁻¹)) =
      Submodule.span Φ₀ (Set.range fun k => embK K i (B k)) := by
    apply le_antisymm
    · rw [← hM']
      exact fun x hx => hMM' hx
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hβM (B k)
  rw [← Subalgebra.finrank_toSubmodule, hMeq, finrank_span_eq_card (linIndep B Φ₀ hΦ), Fintype.card_fin]

end

end GroundTheory.Heights₂.Heights
end

