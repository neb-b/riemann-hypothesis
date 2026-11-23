module

public import Mathlib
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0174
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeCompactPowSmulNhdsBasis
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.LocDualTop

theorem eq_zero_of_forall_pow_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ c : O} (hϖ : Irreducible ϖ) (h : ∀ n : ℕ, ϖ ^ n ∣ c) : c = 0 := by
  by_contra hc
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  obtain ⟨d, hd⟩ := h (k + 1)
  have hk : ϖ ^ k ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hu : (u : O) = ϖ * d := by
    apply mul_right_cancel₀ hk
    rw [hd]; ring
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro d hu.symm) u.isUnit)

section Lat

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem bT_smul_left (k : FractionRing O) (x : VT) (y : VT') :
    D.bT (k • x) y = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT
    (FractionRing O)).map_smul (D.bT.flip y) k x

theorem bT_smul_right (k : FractionRing O) (x : VT) (y : VT') :
    D.bT x (k • y) = k * D.bT x y :=
  (IsLocalization.linearMap_compatibleSMul (nonZeroDivisors O) (FractionRing O) VT'
    (FractionRing O)).map_smul (D.bT x) k y

theorem eq_zero_of_bT (hP : PerfectRight D.bT) {y : VT'} (h : ∀ x, D.bT x y = 0) : y = 0 :=
  (hP 0).unique h (fun x => by simp)

theorem dualLatticePairing_eq_zero_of_mem_lattice (hL : IsLatticeIn D.T) {y : VT'} (h : ∀ x ∈ D.T, D.bT x y = 0) (x : VT) :
    D.bT x y = 0 := by
  let ψ := (D.bT.flip y).extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O)
  have hs : Submodule.span (FractionRing O) (D.T : Set VT) ≤ LinearMap.ker ψ :=
    Submodule.span_le.2 fun z hz => LinearMap.mem_ker.2 (h z hz)
  have hx : x ∈ Submodule.span (FractionRing O) (D.T : Set VT) := hL.2 ▸ Submodule.mem_top
  exact LinearMap.mem_ker.1 (hs hx)

theorem cont_bT (x : VT) : Continuous fun y : VT' => D.bT x y :=
  D.contbT.comp (continuous_const.prodMk continuous_id)

theorem isOpen_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsOpen ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
  have : ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) =
      Set.range (algebraMap O (FractionRing O)) := by
    ext t; simp [Submodule.mem_one]
  rw [this]; exact hemb.isOpen_range

theorem isClosed_one (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) :=
  AddSubgroup.isClosed_of_isOpen (1 : Submodule O (FractionRing O)).toAddSubgroup (isOpen_one hemb)

theorem isClosed_dualLattice_of_pairing (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O))) :
    IsClosed (D.T' : Set VT') := by
  have : (D.T' : Set VT') = ⋂ x ∈ D.T,
      (fun y => D.bT x y) ⁻¹' ((1 : Submodule O (FractionRing O)) : Set (FractionRing O)) := by
    ext y
    exact ⟨fun h => Set.mem_iInter₂.2 fun x hx => h x hx, fun h x hx => Set.mem_iInter₂.1 h x hx⟩
  rw [this]
  exact isClosed_biInter fun x _ => (isClosed_one hemb).preimage (cont_bT D x)

end Lat

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isCompact_dualLattice_of_pairing [CompactSpace O] (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) : IsCompact (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hL.1
  have hsK : Submodule.span (FractionRing O) (s : Set VT) = ⊤ := by
    rw [eq_top_iff, ← hL.2]
    refine Submodule.span_le.2 fun x hx => ?_
    rw [← hs] at hx
    exact Submodule.span_subset_span O (FractionRing O) (s : Set VT) hx
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (FractionRing O) (s : Set VT)
  haveI : Fintype b := (s.finite_toSet.subset hbs).fintype
  obtain ⟨e, he⟩ : ∃ e : Module.Basis b (FractionRing O) VT, ∀ i, e i = (i : VT) :=
    ⟨Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hsK])),
      fun i => Module.Basis.mk_apply _ _ i⟩
  have hbT : ∀ i : b, (i : VT) ∈ D.T := fun i => hs ▸ Submodule.subset_span (hbs i.2)
  choose f hf using fun i : b => (hP (e.coord i)).exists
  let Φ : (b → O) → VT' := fun c => ∑ i, c i • f i
  have hΦ : Continuous Φ := continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hsub : (D.T' : Set VT') ⊆ Set.range Φ := by
    intro y hy
    have hy' : ∀ i : b, D.bT (i : VT) y ∈ (1 : Submodule O (FractionRing O)) := fun i => hy _ (hbT i)
    choose c hc using fun i => Submodule.mem_one.1 (hy' i)
    refine ⟨c, ?_⟩
    symm
    rw [← sub_eq_zero]
    apply eq_zero_of_bT D hP
    intro x
    have hx : D.bT x y = ∑ i, e.coord i x * algebraMap O (FractionRing O) (c i) := by
      conv_lhs => rw [← e.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bT_smul_left, he, ← hc i, Module.Basis.coord_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, hx, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hf, Algebra.smul_def, mul_comm]
  exact (isCompact_range hΦ).of_isClosed_subset (isClosed_dualLattice_of_pairing D hemb) hsub

end Lat2

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

section Lat3

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT')

theorem isOpen_powSub (hemb : Topology.IsOpenEmbedding (algebraMap O (FractionRing O)))
    (hL : IsLatticeIn D.T) {ϖ : O} (hϖ : Irreducible ϖ) (n : ℕ) :
    IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
  obtain ⟨s, hs⟩ := hL.1
  set a : FractionRing O := algebraMap O (FractionRing O) ϖ ^ n with ha
  have ha0 : a ≠ 0 := pow_ne_zero _ (fun h => hϖ.ne_zero
    (IsFractionRing.injective O (FractionRing O) (by rw [h, map_zero])))
  let W : Set ↥D.T' := ⋂ x ∈ s, (fun z : ↥D.T' => D.bT (a⁻¹ • x) (z : VT')) ⁻¹'
    ((1 : Submodule O (FractionRing O)) : Set (FractionRing O))
  have hW : IsOpen W := isOpen_biInter_finset fun x _ =>
    (isOpen_one hemb).preimage ((cont_bT D _).comp continuous_subtype_val)
  have h0 : (0 : ↥D.T') ∈ W := Set.mem_iInter₂.2 fun x _ => by
    simp only [Set.mem_preimage, ZeroMemClass.coe_zero, map_zero, SetLike.mem_coe]
    exact Submodule.zero_mem _
  have hWsub : W ⊆ ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') := by
    intro z hz
    have hz' := Set.mem_iInter₂.1 hz
    have hyT : a⁻¹ • (z : VT') ∈ D.T' := by
      intro x hx
      have hle : Submodule.span O (s : Set VT) ≤
          (1 : Submodule O (FractionRing O)).comap (D.bT.flip (a⁻¹ • (z : VT'))) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have := hz' x hx
        simp only [Set.mem_preimage, SetLike.mem_coe] at this
        show D.bT x (a⁻¹ • (z : VT')) ∈ (1 : Submodule O (FractionRing O))
        rwa [bT_smul_right, ← bT_smul_left]
      rw [hs] at hle
      exact hle hx
    refine mem_powSub.2 ⟨⟨a⁻¹ • (z : VT'), hyT⟩, Subtype.ext ?_⟩
    show ϖ ^ n • a⁻¹ • (z : VT') = z
    rw [← algebraMap_smul (FractionRing O) (ϖ ^ n), smul_smul, map_pow, ← ha, mul_inv_cancel₀ ha0,
      one_smul]
  exact AddSubgroup.isOpen_of_mem_nhds (powSub (M := ↥D.T') ϖ n).toAddSubgroup
    (Filter.mem_of_superset (hW.mem_nhds h0) hWsub)

theorem eq_zero_of_mem_powSub (hL : IsLatticeIn D.T) (hP : PerfectRight D.bT) {ϖ : O}
    (hϖ : Irreducible ϖ) {z : ↥D.T'} (hz : ∀ n, z ∈ powSub (M := ↥D.T') ϖ n) : z = 0 := by
  refine Subtype.ext (eq_zero_of_bT D hP (dualLatticePairing_eq_zero_of_mem_lattice D hL (fun x hx => ?_)))
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (z.2 x hx)
  have hdvd : ∀ n : ℕ, ϖ ^ n ∣ c := by
    intro n
    obtain ⟨w, hw⟩ := mem_powSub.1 (hz n)
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (w.2 x hx)
    refine ⟨d, IsFractionRing.injective O (FractionRing O) ?_⟩
    rw [hc, ← hw, map_mul, hd]
    show D.bT x (ϖ ^ n • (w : VT')) = _
    rw [map_smul, Algebra.smul_def]
  rw [← hc, eq_zero_of_forall_pow_dvd hϖ hdvd, map_zero]

end Lat3

end GlobalTheory.LocDualTop

namespace GlobalTheory.LocDualTop

theorem dualLat_compact_powSub_nhds : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] {VT VT' : Type} [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT] [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT] [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT'] [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT'] {G : Type} [Group G] [TopologicalSpace G] (D : LatData O G VT VT'), CompactSpace O → Topology.IsOpenEmbedding (algebraMap O (FractionRing O)) → IsLatticeIn D.T → PerfectRight D.bT → T2Space VT' → ∀ ϖ : O, Irreducible ϖ → CompactSpace ↥D.T' ∧ (∀ n : ℕ, IsOpen ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T')) ∧ ∀ U ∈ nhds (0 : ↥D.T'), ∃ n : ℕ, ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T') ⊆ U := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ D hO hemb hL hP hT2 ϖ hϖ
  have hK : IsCompact (D.T' : Set VT') := isCompact_dualLattice_of_pairing D hemb hL hP
  haveI : CompactSpace ↥D.T' := isCompact_iff_compactSpace.1 hK
  have hopen := isOpen_powSub D hemb hL hϖ
  refine ⟨inferInstance, hopen, fun U hU => ?_⟩
  obtain ⟨V, hVU, hV, h0V⟩ := mem_nhds_iff.1 hU
  obtain ⟨n, hn⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed
    (fun n : ℕ => ((powSub (M := ↥D.T') ϖ n : Submodule O ↥D.T') : Set ↥D.T'))
    (fun n => AddSubgroup.isClosed_of_isOpen (powSub (M := ↥D.T') ϖ n).toAddSubgroup (hopen n))
    (by
      rw [Set.disjoint_left]
      intro z hz hz'
      have : z = 0 := eq_zero_of_mem_powSub D hL hP hϖ fun n => Set.mem_iInter.1 hz' n
      exact hz (this ▸ h0V))
    (fun a b => ⟨max a b, fun x hx => powSub_anti ϖ (le_max_left a b) hx,
      fun x hx => powSub_anti ϖ (le_max_right a b) hx⟩)
  refine ⟨n, fun z hz => hVU ?_⟩
  by_contra hc
  exact Set.disjoint_left.1 hn hc hz

end GlobalTheory.LocDualTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffHasSumUntiltFrobeniusCombination
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PSer

theorem emod_toNat_lt (h : ℕ) (hh : 1 ≤ h) (k : ℤ) : (k % (h : ℤ)).toNat < h := by
  have h0 : (0 : ℤ) < h := by exact_mod_cast hh
  have := Int.emod_lt_of_pos k h0
  have := Int.emod_nonneg k h0.ne'
  omega

def reCoef (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) : ℂ_[l] :=
  (l : ℂ_[l]) ^ (-(k / (h : ℤ))) * μ ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩

theorem reCoef_add (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (k : ℤ) :
    reCoef l h hh μ k = (l : ℂ_[l]) * reCoef l h hh μ (k + h) := by
  have hl : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have e1 : (k + h) / (h : ℤ) = k / h + 1 := by
    have := Int.add_mul_ediv_right k 1 h0; simpa using this
  have e2 : (k + h) % (h : ℤ) = k % h := by simp
  unfold reCoef
  simp only [e1, e2]
  rw [neg_add, zpow_add₀ hl, zpow_neg_one]
  field_simp

theorem reCoef_at (l : ℕ) [Fact l.Prime] (h : ℕ) (hh : 1 ≤ h) (μ : Fin h → ℂ_[l]) (n : ℤ) (i : Fin h) :
    reCoef l h hh μ (n * h + i) = (l : ℂ_[l]) ^ (-n) * μ i := by
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
  have hih : (i : ℤ) < h := by exact_mod_cast i.isLt
  have e1 : (n * h + i) / (h : ℤ) = n := by
    rw [add_comm, Int.add_mul_ediv_right _ _ h0, Int.ediv_eq_zero_of_lt hi0 hih, zero_add]
  have e2 : (n * h + i) % (h : ℤ) = i := by
    rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]
  unfold reCoef
  congr 2
  · rw [e1]
  · ext; simp [e2]

theorem emod_at (h : ℕ) (hh : 1 ≤ h) (n : ℤ) (i : Fin h) :
    (n * h + ((i : ℕ) : ℤ)) % (h : ℤ) = ((i : ℕ) : ℤ) := by
  have hi0 : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := by positivity
  have hih : ((i : ℕ) : ℤ) < h := by exact_mod_cast i.isLt
  rw [add_comm, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hi0 hih]

theorem exists_coef_hasSum_lam : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), 1 ≤ h → μ ≠ 0 →
    ∃ m : ℤ → ℂ_[l], (∀ k, m k = (l : ℂ_[l]) * m (k + h)) ∧ (∃ k, m k ≠ 0) ∧
      ∀ x : Fl l, ‖sh x‖ < 1 →
        HasSum (fun k : ℤ => m k * sh (pw k x)) (∑ i : Fin h, μ i * lam h i x) := by
  intro l _ h μ hh hμ
  have h0 : (h : ℤ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
  refine ⟨reCoef l h hh μ, reCoef_add l h hh μ, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
      by_contra H; push_neg at H; exact hμ (funext H)
    refine ⟨((i : ℕ) : ℤ), ?_⟩
    have := reCoef_at l h hh μ 0 i
    simp only [zero_mul, zero_add, neg_zero, zpow_zero, one_mul] at this
    rw [this]; exact hi
  · intro x hx
    let f : ℤ → ℂ_[l] := fun k => reCoef l h hh μ k * sh (pw k x)
    let F : Fin h → ℤ → ℂ_[l] := fun i k => if k % (h : ℤ) = ((i : ℕ) : ℤ) then f k else 0
    have hF : ∀ k, f k = ∑ i, F i k := by
      intro k
      have hn : 0 ≤ k % (h : ℤ) := Int.emod_nonneg k h0
      rw [Finset.sum_eq_single ⟨(k % (h : ℤ)).toNat, emod_toNat_lt h hh k⟩]
      · simp only [F]; rw [if_pos (by simp [Int.toNat_of_nonneg hn])]
      · intro b _ hb
        simp only [F]
        rw [if_neg]
        intro hbk
        apply hb
        ext
        simp only
        omega
      · intro hc; exact absurd (Finset.mem_univ _) hc
    have hFi : ∀ i : Fin h, HasSum (F i) (μ i * lam h i x) := by
      intro i
      have hg : Function.Injective (fun n : ℤ => n * h + ((i : ℕ) : ℤ)) := by
        intro a b e
        have e' : a * (h : ℤ) = b * h := by simpa using e
        exact mul_right_cancel₀ h0 e'
      rw [← hg.hasSum_iff]
      · have := ((_root_.GlobalTheory.PSer.lam_hasSum_norm_le_frob l h i ‖sh x‖ x hh hx le_rfl).1).mul_left (μ i)
        have heq : (F i ∘ fun n : ℤ => n * h + ((i : ℕ) : ℤ)) =
            fun n : ℤ => μ i * ((l : ℂ_[l]) ^ (-n) * sh (pw (n * h + ((i : ℕ) : ℤ)) x)) := by
          funext n
          simp only [Function.comp, F, f]
          rw [if_pos (emod_at h hh n i), reCoef_at]
          ring
        rw [heq]; exact this
      · intro k hk
        simp only [F]
        rw [if_neg]
        intro hki
        apply hk
        refine ⟨k / h, ?_⟩
        have := Int.ediv_mul_add_emod k (h : ℤ)
        simp only
        rw [← hki]
        linarith [mul_comm (k / (h : ℤ)) (h : ℤ)]
    have := hasSum_sum (s := Finset.univ) (fun i _ => hFi i)
    have hf : f = fun k => ∑ i, F i k := funext hF
    show HasSum f _
    rw [hf]; exact this

end GlobalTheory.PSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousCocycleLiftOfCompatible
section
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

noncomputable section

namespace GlobalTheory.CocycleLimit

theorem exists_continuous_cocycle_lift_of_compatible : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [T2Space M] [CompactSpace M] (ρ : Representation O G M) (a : O) (r : ℕ), (∀ n : ℕ, IsOpen ((powSub (M := M) a n : Submodule O M) : Set M)) → (∀ U ∈ nhds (0 : M), ∃ n : ℕ, ((powSub (M := M) a n : Submodule O M) : Set M) ⊆ U) → ∀ w : ℕ → G → M, (∀ k, (fun g => (Submodule.Quotient.mk (w k g) : M ⧸ powSub (M := M) a (r + k))) ∈ Z1 (quotRep ρ a (r + k))) → (∀ k g, w (k + 1) g - w k g ∈ powSub (M := M) a (r + k)) → ∃ e ∈ Z1 ρ, ∀ k g, e g - w k g ∈ powSub (M := M) a (r + k) := by
  intro O _ G _ _ M _ _ _ _ _ _ _ ρ a r hopen hbasis w hw hstep
  set N : ℕ → Submodule O M := fun n => powSub (M := M) a n with hN

  have hclosedN : ∀ n, IsClosed ((N n : Submodule O M) : Set M) := fun n =>
    AddSubgroup.isClosed_of_isOpen (N n).toAddSubgroup (hopen n)

  have hex : ∀ g, ∃ x, ∀ k, x - w k g ∈ N (r + k) := by
    intro g
    let C : ℕ → Set M := fun k => {x | x - w k g ∈ N (r + k)}
    have hsub : ∀ k, C (k + 1) ⊆ C k := by
      intro k x hx
      have h1 : x - w (k + 1) g ∈ N (r + k) :=
        powSub_anti a (by omega : r + k ≤ r + (k + 1)) hx
      have h2 := hstep k g
      show x - w k g ∈ N (r + k)
      have : x - w k g = (x - w (k + 1) g) + (w (k + 1) g - w k g) := by abel
      rw [this]; exact (N (r + k)).add_mem h1 h2
    have hne : ∀ k, (C k).Nonempty := fun k => ⟨w k g, by simp [C, (N (r + k)).zero_mem]⟩
    have hcl : ∀ k, IsClosed (C k) := fun k =>
      (hclosedN (r + k)).preimage (continuous_id.sub continuous_const)
    obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hsub hne
      (hcl 0).isCompact hcl
    exact ⟨x, fun k => Set.mem_iInter.1 hx k⟩
  choose e he using hex

  have hzero : ∀ x : M, (∀ k, x ∈ N (r + k)) → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := hbasis ({x}ᶜ) (isOpen_compl_singleton.mem_nhds (Ne.symm hne))
    have : x ∈ N (r + n) := hx n
    exact hn (powSub_anti a (by omega : n ≤ r + n) this) rfl

  have hcoc : ∀ k g h, w k (g * h) - (w k g + ρ g (w k h)) ∈ N (r + k) := by
    intro k g h
    have := (hw k).2 g h
    simp only [quotRep_mk] at this
    rw [← Submodule.Quotient.mk_add] at this
    exact (Submodule.Quotient.eq _).1 this
  refine ⟨e, ⟨?_, ?_⟩, fun k g => he g k⟩
  ·
    rw [continuous_iff_continuousAt]
    intro g0 U hU
    have hV : {y : M | y + e g0 ∈ U} ∈ nhds (0 : M) :=
      (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨n, hn⟩ := hbasis _ hV
    let q : G → M ⧸ powSub (M := M) a (r + n) := fun g => Submodule.Quotient.mk (w n g)
    have hq : Continuous q := (hw n).1
    have hsing : IsOpen ({q g0} : Set (M ⧸ powSub (M := M) a (r + n))) := by
      rw [← (Submodule.isOpenQuotientMap_mkQ (powSub (M := M) a (r + n))).isQuotientMap.isOpen_preimage]
      have : (Submodule.mkQ (powSub (M := M) a (r + n))) ⁻¹' {q g0} =
          (fun y => y - w n g0) ⁻¹' ((N (r + n) : Submodule O M) : Set M) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Submodule.mkQ_apply, q,
          SetLike.mem_coe, N]
        exact Submodule.Quotient.eq _
      rw [this]
      exact (hopen (r + n)).preimage (continuous_id.sub continuous_const)
    have hS : q ⁻¹' {q g0} ∈ nhds g0 := (hsing.preimage hq).mem_nhds rfl
    show e ⁻¹' U ∈ nhds g0
    refine Filter.mem_of_superset hS ?_
    intro g hg
    have hg' : w n g - w n g0 ∈ N (r + n) := (Submodule.Quotient.eq _).1 hg
    have hmem : e g - e g0 ∈ N (r + n) := by
      have : e g - e g0 = (e g - w n g) + (w n g - w n g0) - (e g0 - w n g0) := by abel
      rw [this]
      exact (N (r + n)).sub_mem ((N (r + n)).add_mem (he g n) hg') (he g0 n)
    have := hn (powSub_anti a (by omega : n ≤ r + n) hmem)
    simpa using this
  ·
    intro g h
    rw [← sub_eq_zero]
    apply hzero
    intro k
    have : e (g * h) - (e g + ρ g (e h)) =
        (e (g * h) - w k (g * h)) - (e g - w k g) - ρ g (e h - w k h) +
          (w k (g * h) - (w k g + ρ g (w k h))) := by
      rw [map_sub]; abel
    rw [this]
    refine (N (r + k)).add_mem ((N (r + k)).sub_mem ((N (r + k)).sub_mem (he _ k) (he _ k))
      (powSub_stable ρ a _ g _ (he h k))) (hcoc k g h)

end GlobalTheory.CocycleLimit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteTwistedInvariantLatticeStatement
section
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_twistedInvariantLattice : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  first | exact @GlobalTheory.BK.BKDat.isAdicComplete_Y' | exact GlobalTheory.BK.BKDat.isAdicComplete_Y' | (intros; apply GlobalTheory.BK.BKDat.isAdicComplete_Y' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftImageEulerEInvariantsQuotient
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.LiftImage

theorem lift_image : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₀ : BKDat O K l e a ι η H) (D₁ : BKDat O K l e a κ η H) (F : BKHom D₀ D₁) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Image D₁ U → ∀ ω : D₁.Pol, (∃ w ∈ D₁.Zl, D₁.Lc w = ω) → ∀ c : ℕ, (∃ w₀ ∈ D₀.Zl, F.onPol w₀ = (l : K) ^ c • ω) → ∃ w ∈ D₀.Zl, F.onPol (D₀.Lc w) = ω := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₀ D₁ F U hIm ω hω c hc
  obtain ⟨w₁, hw₁, hw₁ω⟩ := hω
  obtain ⟨w₀, hw₀, hw₀ω⟩ := hc
  let W : Submodule K D₁.Zl := (D₀.Zl.map F.onPol).comap D₁.Zl.subtype
  have hW : W ≤ W.comap D₁.LcZ := by
    rintro z ⟨x, hx, hxz⟩
    refine ⟨D₀.Lc x, D₀.Lc_mem_Zl hx, ?_⟩
    rw [BKHom.onPol_Lc, hxz]
    rfl
  have hωZ : ω ∈ D₁.Zl := hw₁ω ▸ D₁.Lc_mem_Zl hw₁
  have hl : ((l : K) ^ c) ≠ 0 := pow_ne_zero _ (l_ne_zero (K := K) l)
  have hrange : (⟨ω, hωZ⟩ : D₁.Zl) ∈ LinearMap.range D₁.LcZ := ⟨⟨w₁, hw₁⟩, Subtype.ext hw₁ω⟩
  have hmemW : (⟨ω, hωZ⟩ : D₁.Zl) ∈ W := by
    refine ⟨((l : K) ^ c)⁻¹ • w₀, D₀.Zl.smul_mem _ hw₀, ?_⟩
    rw [map_smul, hw₀ω, smul_smul, inv_mul_cancel₀ hl, one_smul]
    rfl
  have hmap := hIm.2 W hW
  have h2 : (⟨ω, hωZ⟩ : D₁.Zl) ∈ W.map D₁.LcZ := hmap ▸ ⟨hrange, hmemW⟩
  obtain ⟨z, ⟨x, hx, hxz⟩, hzω⟩ := h2
  refine ⟨x, hx, ?_⟩
  rw [BKHom.onPol_Lc, hxz]
  exact congrArg Subtype.val hzω

end GlobalTheory.Proof.LiftImage
end

