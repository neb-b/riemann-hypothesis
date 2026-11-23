module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.CuspidalAdmissible
public import GroundTheory.AutomorphicForms.JacquetAdmissible
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import GroundTheory.AutomorphicForms.IwahoriFactorization
public import GroundTheory.AutomorphicForms.ReductionMahler
public import GroundTheory.AutomorphicForms.GeometricLemmaGraded
public import GroundTheory.AutomorphicForms.GeometricLemmaCellKernel
public import GroundTheory.AutomorphicForms.GeometricLemmaCellSurjective
public import GroundTheory.AutomorphicForms.SphericalIntegral

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.AdmissibleFiniteLength
section
noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology Filter Set

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem fixedVectors_jacquetRep_congruenceSubgroup (m : ℕ) :
    fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) =
      fixedVectors (jacquetAction F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β)) := by
  ext x
  simp only [mem_fixedVectors]
  refine forall₂_congr fun y hy => ?_
  rw [jacquetRep, twist_apply, MonoidHom.comp_apply,
    invSqrtModular_leviIncl_of_mem y (congruenceSubgroup_le F n m (Subgroup.mem_subgroupOf.1 hy)),
    one_smul]

theorem isAdmissible_jacquetRep (hπ : IsAdmissible π) : IsAdmissible (jacquetRep F n β π) := by
  refine ⟨isSmooth_jacquetRep π hπ.1, fun L hLc hLo => ?_⟩
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset (hLo.mem_nhds L.one_mem)
  set m := max m₁ 1
  have hle : (congruenceSubgroup F n m).subgroupOf (levi F n β) ≤ L := fun x hx =>
    hm₁ (Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n (le_max_left _ _)
      (Subgroup.mem_subgroupOf.1 hx)))
  have : FiniteDimensional ℂ (fixedVectors π (congruenceSubgroup F n m)) :=
    hπ.2 _ (isCompact_congruenceSubgroup F n m) (isOpen_congruenceSubgroup F n m)
  have hfin : FiniteDimensional ℂ
      (fixedVectors (jacquetRep F n β π) ((congruenceSubgroup F n m).subgroupOf (levi F n β))) := by
    rw [fixedVectors_jacquetRep_congruenceSubgroup]
    exact Module.Finite.of_surjective _
      (jacquetFixedMap_surjective_congruenceSubgroup β hπ (le_max_right m₁ 1))
  exact Submodule.finiteDimensional_of_le (fixedVectors_antitone _ hle)

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.AnisotropicOrbit
section
set_option maxSynthPendingDepth 1

open NumberField IsDedekindDomain Topology Set Matrix
open scoped NumberField.AdeleRing Pointwise

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

section Orbit

variable {𝒢 W : Type*} [Group 𝒢]

theorem exists_finset_of_orbit (Φ : 𝒢 → W) (G Γ : Subgroup 𝒢)
    (hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ G) (C : Set 𝒢)
    (hfin : (Φ '' C ∩ Φ '' (Γ : Set 𝒢)).Finite) :
    ∃ T : Finset 𝒢, (∀ δ ∈ T, δ ∈ Γ) ∧ ∀ g ∈ G, ∀ γ ∈ Γ, ∀ c ∈ C, g = γ * c →
      ∃ δ ∈ T, γ * δ ∈ G ∧ δ⁻¹ * c ∈ G := by
  classical
  have hch : ∀ s ∈ hfin.toFinset, ∃ δ ∈ Γ, Φ δ = s := fun s hs => by
    obtain ⟨-, δ, hδ, rfl⟩ := hfin.mem_toFinset.1 hs
    exact ⟨δ, hδ, rfl⟩
  choose! f hfΓ hfΦ using hch
  refine ⟨hfin.toFinset.image f, fun δ hδ => ?_, fun g hg γ hγ c hc hgc => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hδ
    exact hfΓ s hs
  · have h1 : Φ γ⁻¹ = Φ c := (hΦ _ _).2 (by rw [inv_inv, ← hgc]; exact hg)
    have hs : Φ c ∈ hfin.toFinset := hfin.mem_toFinset.2 ⟨⟨c, hc, rfl⟩, γ⁻¹, inv_mem hγ, h1⟩
    refine ⟨f (Φ c), Finset.mem_image_of_mem _ hs, ?_, (hΦ _ _).1 (hfΦ _ hs)⟩
    have := (hΦ γ⁻¹ (f (Φ c))).1 (by rw [hfΦ _ hs, h1])
    rwa [inv_inv] at this

theorem conj_eq_conj_iff {R : Type*} [Ring R] (g g' : Rˣ) (x : R) :
    (g : R) * x * ↑g⁻¹ = g' * x * ↑g'⁻¹ ↔ ((g⁻¹ * g' : Rˣ) : R) * x = x * ((g⁻¹ * g' : Rˣ) : R) := by
  rw [Units.val_mul]
  have e1 : (↑g⁻¹ * ↑g' * x : R) = ↑g⁻¹ * (↑g' * x * ↑g'⁻¹) * ↑g' := by
    simp [mul_assoc]
  have e2 : (x * (↑g⁻¹ * ↑g') : R) = ↑g⁻¹ * (↑g * x * ↑g⁻¹) * ↑g' := by
    simp [mul_assoc]
  constructor
  · intro h
    rw [e1, e2, h]
  · intro h
    have e3 : (↑g' * x * ↑g'⁻¹ : R) = ↑g * (↑g⁻¹ * ↑g' * x) * ↑g'⁻¹ := by
      simp [mul_assoc]
    have e4 : (↑g * x * ↑g⁻¹ : R) = ↑g * (x * (↑g⁻¹ * ↑g')) * ↑g'⁻¹ := by
      simp [mul_assoc]
    rw [e3, e4, h]

end Orbit

variable {K : Type*} [Field K] [NumberField K]

theorem finite_algebraMap_preimage {X : Set 𝔸[K]} (hX : IsCompact X) :
    (algebraMap K 𝔸[K] ⁻¹' X).Finite := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hc := GroundTheory.Global.isClosed_principalSubgroup K
  set P : Set 𝔸[K] := (AdeleRing.principalSubgroup (𝓞 K) K : Set 𝔸[K]) with hP
  have hXP : IsCompact (X ∩ P) := hX.inter_right hc
  have hdP : DiscreteTopology P := hd
  have hdisc : DiscreteTopology (X ∩ P : Set 𝔸[K]) :=
    DiscreteTopology.of_subset hdP Set.inter_subset_right
  have hfin : (X ∩ P).Finite := hXP.finite ⟨hdisc⟩
  refine (hfin.preimage (AdeleRing.algebraMap_injective (𝓞 K) K).injOn).subset ?_
  intro k hk
  exact ⟨hk, k, rfl⟩

theorem finite_of_isCompact_coords {α Y J : Type*} [Finite J] [TopologicalSpace Y] {X : Set Y}
    (hX : IsCompact X) (ψ : α → Y) (π : J → Y → 𝔸[K]) (hπ : ∀ j, Continuous (π j))
    (φ : α → J → K) (hφ : Function.Injective φ)
    (hψ : ∀ a j, π j (ψ a) = algebraMap K 𝔸[K] (φ a j)) : {a | ψ a ∈ X}.Finite := by
  have h : (Set.univ.pi fun j => algebraMap K 𝔸[K] ⁻¹' (π j '' X)).Finite :=
    Set.Finite.pi fun j => finite_algebraMap_preimage (hX.image (hπ j))
  refine Set.Finite.of_finite_image (h.subset ?_) hφ.injOn
  rintro _ ⟨a, ha, rfl⟩ j -
  exact ⟨ψ a, ha, hψ a j⟩

variable {n : ℕ} {m : Type*}

def adelicCentralizer (L : m → Matrix (Fin n) (Fin n) K) : Subgroup (AdelicGLn.AdelicGL K n) where
  carrier := {g | ∀ k, (g : Matrix (Fin n) (Fin n) 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
    (L k).map (algebraMap K 𝔸[K]) * g}
  one_mem' k := by simp
  mul_mem' {a b} ha hb k := by
    show ((a * b : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * _ = _ * _
    rw [Units.val_mul, Matrix.mul_assoc, hb k, ← Matrix.mul_assoc, ha k, Matrix.mul_assoc]
  inv_mem' {a} ha k := by
    have h := ha k
    set M := (L k).map (algebraMap K 𝔸[K])
    show ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M =
      M * ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
    calc ((a⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * M
        = ↑a⁻¹ * (M * ↑a) * ↑a⁻¹ := by simp [mul_assoc]
      _ = ↑a⁻¹ * (↑a * M) * ↑a⁻¹ := by rw [h]
      _ = M * ↑a⁻¹ := by simp

theorem diagonal_mem_adelicCentralizer_iff {L : m → Matrix (Fin n) (Fin n) K}
    {γ : GL (Fin n) K} :
    AdelicGLn.diagonal K n γ ∈ adelicCentralizer L ↔
      ∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ := by
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) K => M.map (algebraMap K 𝔸[K]) :=
    Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 K) K)
  refine forall_congr' fun k => ?_
  show (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) * (L k).map (algebraMap K 𝔸[K]) =
      (L k).map (algebraMap K 𝔸[K]) * (γ : Matrix (Fin n) (Fin n) K).map (algebraMap K 𝔸[K]) ↔ _
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact hinj.eq_iff

theorem exists_isCompact_centralizer_reduction [Finite m] (L : m → Matrix (Fin n) (Fin n) K)
    (G : Subgroup (AdelicGLn.AdelicGL K n)) (hG1 : G ≤ Reduction.normOneGL (K := K) (n := n))
    (hGL : G ≤ adelicCentralizer L) {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G, ∀ x : Fin n → K, x ≠ 0 → ε ≤ Reduction.height g x) :
    ∃ C : Set (AdelicGLn.AdelicGL K n), IsCompact C ∧ ∀ g ∈ G, ∃ γ : GL (Fin n) K,
      (∀ k, (γ : Matrix (Fin n) (Fin n) K) * L k = L k * γ) ∧
        (AdelicGLn.diagonal K n γ)⁻¹ * g ∈ C := by
  classical
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n) hε
  let Lm : m → Matrix (Fin n) (Fin n) 𝔸[K] := fun k => (L k).map (algebraMap K 𝔸[K])
  let Φ : AdelicGLn.AdelicGL K n → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun g k => (g : Matrix (Fin n) (Fin n) 𝔸[K]) * Lm k *
      ((g⁻¹ : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ adelicCentralizer L := by
    intro g g'
    rw [funext_iff]
    exact forall_congr' fun k => conj_eq_conj_iff g g' (Lm k)
  have hΦc : Continuous Φ := continuous_pi fun k =>
    ((Units.continuous_val.matrix_mul continuous_const).matrix_mul Units.continuous_coe_inv)
  let ψ : (m → Matrix (Fin n) (Fin n) K) → m → Matrix (Fin n) (Fin n) 𝔸[K] :=
    fun r k => (r k).map (algebraMap K 𝔸[K])
  have hψfin : {r | ψ r ∈ Φ '' C}.Finite := by
    refine finite_of_isCompact_coords (hC.image hΦc) ψ
      (fun p : m × Fin n × Fin n => fun M => M p.1 p.2.1 p.2.2)
      (fun p => (continuous_apply p.1).matrix_elem p.2.1 p.2.2)
      (fun r p => r p.1 p.2.1 p.2.2) ?_ (fun r p => rfl)
    intro r r' h
    funext k i j
    exact congrFun h (k, i, j)
  have hfin : (Φ '' C ∩ Φ '' (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n))).Finite := by
    refine (hψfin.image ψ).subset ?_
    rintro _ ⟨hC1, _, ⟨γ, rfl⟩, rfl⟩
    have e : Φ (AdelicGLn.diagonal K n γ) = ψ fun k => (γ : Matrix (Fin n) (Fin n) K) * L k *
        ((γ⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      funext k
      simp only [ψ, Φ, Lm, ← map_inv]
      rw [Matrix.map_mul, Matrix.map_mul]
      rfl
    rw [e] at hC1 ⊢
    exact ⟨_, hC1, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (adelicCentralizer L) (AdelicGLn.rationalGL K n)
    hΦ C hfin
  refine ⟨⋃ δ ∈ T, (fun c => δ⁻¹ * c) '' C,
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id), ?_⟩
  intro g hg
  obtain ⟨_, ⟨γ₀, rfl⟩, c, hc, hgc⟩ := hC' g (hG1 hg) (hh g hg)
  obtain ⟨δ, hδT, hγδ, hδc⟩ := hT g (hGL hg) _ ⟨γ₀, rfl⟩ c hc hgc.symm
  obtain ⟨δ₀, rfl⟩ := hTΓ δ hδT
  refine ⟨γ₀ * δ₀, ?_, ?_⟩
  · rw [← diagonal_mem_adelicCentralizer_iff, map_mul]
    exact hγδ
  · refine Set.mem_biUnion hδT ⟨c, hc, ?_⟩
    rw [map_mul, ← hgc, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel_left]

end Anisotropic

end

end GroundTheory.Automorphic
end

-- bundled from GroundTheory.AutomorphicForms.CuspidalSplittingSums
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function
open scoped Pointwise

section Sums

variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]

def quotSum (Φ : G → M) : M :=
  ∑ᶠ q : G ⧸ H, Φ q.out

variable {H}

theorem quotSum_def (Φ : G → M) : quotSum H Φ = ∑ᶠ q : G ⧸ H, Φ q.out := rfl

theorem apply_out_mk {X : Type*} {Φ : G → X} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (g : G) :
    Φ (QuotientGroup.mk g : G ⧸ H).out = Φ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hΦ g h h.2]

theorem quotSum_mul_left {Φ : G → M} (hΦ : ∀ g, ∀ h ∈ H, Φ (g * h) = Φ g) (x : G) :
    quotSum H (fun g => Φ (x * g)) = quotSum H Φ := by
  unfold quotSum
  calc ∑ᶠ q : G ⧸ H, Φ (x * q.out)
      = ∑ᶠ q : G ⧸ H, (fun q' : G ⧸ H => Φ q'.out) (MulAction.toPerm x q) := by
        refine finsum_congr fun q => ?_
        have hq : (MulAction.toPerm x q : G ⧸ H) = QuotientGroup.mk (x * q.out) := by
          rw [MulAction.toPerm_apply]
          conv_lhs => rw [← QuotientGroup.out_eq' q]
          rfl
        simp only [hq, apply_out_mk hΦ]
    _ = ∑ᶠ q : G ⧸ H, Φ q.out := finsum_comp_equiv (MulAction.toPerm x) (f := fun q' : G ⧸ H => Φ q'.out)

theorem quotSum_congr {Φ Ψ : G → M} (h : ∀ g, Φ g = Ψ g) : quotSum H Φ = quotSum H Ψ := by
  unfold quotSum
  exact finsum_congr fun q => h _

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem finite_support_quotSum (hH : IsOpen (H : Set G)) (hZH : Subgroup.center G ≤ H)
    {Φ : G → M} {C : Set G} (hC : IsCompact C)
    (hsupp : support Φ ⊆ (Subgroup.center G : Set G) * C) :
    (support fun q : G ⧸ H => Φ q.out).Finite := by
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  refine ((hC.image QuotientGroup.continuous_mk).finite_of_discrete).subset ?_
  intro q hq
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp hq
  replace hzc : z * c = q.out := hzc
  refine ⟨c, hc, ?_⟩
  rw [← QuotientGroup.out_eq' q, ← hzc, QuotientGroup.eq]
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  rw [hzc', ← mul_assoc, inv_mul_cancel, one_mul]
  exact hZH hz

end Sums

section CompactModCenter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}


theorem IsCompactModCenter.comp_inv {φ : GL (Fin n) F → ℂ} (hφ : IsCompactModCenter φ) :
    IsCompactModCenter fun g => φ g⁻¹ := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  refine ⟨C⁻¹, hC.inv, fun g hg => ?_⟩
  obtain ⟨z, hz, c, hc, hzc⟩ := hsupp (show g⁻¹ ∈ support φ from hg)
  replace hzc : z * c = g⁻¹ := hzc
  refine ⟨z⁻¹, inv_mem hz, c⁻¹, by simpa using hc, ?_⟩
  have hzc' : z * c = c * z := (Subgroup.mem_center_iff.1 hz c).symm
  show z⁻¹ * c⁻¹ = g
  rw [← mul_inv_rev, ← hzc', hzc, inv_inv]

end CompactModCenter

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.GeometricLemmaUnnormalized
section
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem cellUnion_mul_mem {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (j : ℕ) :
    (∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) j, ∀ q ∈ blockUpper F n γ, g * q ∈ cellUnion (fun l => doubleCoset
          (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j) ∧
      (∀ p ∈ blockUpper F n β, ∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j, p * g ∈ cellUnion
          (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
            (blockUpper F n γ)) j) := by
  constructor
  · intro g hg q hq
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p', hp', q' * q,
      (blockUpper F n γ).mul_mem hq' hq, by group⟩⟩
  · intro p hp g hg
    obtain ⟨l, hl, hgl⟩ := (mem_cellUnion _).1 hg
    obtain ⟨p', hp', q', hq', rfl⟩ := mem_doubleCoset.1 hgl
    exact (mem_cellUnion _).2 ⟨l, hl, mem_doubleCoset.2 ⟨p * p',
      (blockUpper F n β).mul_mem hp hp', q', hq', by group⟩⟩

theorem exists_filtration_jacquetModule_parabolicInd (hσ : IsSmooth σ) :
    ∃ (k : ℕ) (w : Fin k → Equiv.Perm (Fin n)),
      (∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
      ∃ V : ℕ → Submodule ℂ (JacquetModule F n γ (parabolicInd F n β σ)),
        V 0 = ⊥ ∧ V k = ⊤ ∧ Monotone V ∧
        ∃ hV : ∀ i (m : levi F n γ), V i ≤ (V i).comap (jacquetRep F n γ (parabolicInd F n β σ) m),
          ∀ j : Fin k, ∃ Ψ : Representation.IntertwiningMap
              ((jacquetRep F n γ (parabolicInd F n β σ)).subrepresentation (V (j + 1)) (hV (j + 1)))
              (twist ((invSqrtModular F n γ).comp leviIncl)
                (indRep (cellLeviSub F β γ (w j)) (cellInducing β γ (w j) σ))),
            Function.Surjective Ψ ∧
              ∀ x, Ψ x = 0 ↔ (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ V j := by
  obtain ⟨k, w, hcov, hanti⟩ := exists_cellEnumeration (F := F) β γ
  set C : Fin k → Set (GL (Fin n) F) := fun l =>
    doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)
  have hdisj : Pairwise fun i j => Disjoint (C i) (C j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro g hgi hgj
    obtain ⟨l, -, hl⟩ := hcov g
    exact hij ((hl i hgi).trans (hl j hgj).symm)
  have hcov' : ∀ g, ∃ l, g ∈ C l := fun g => (hcov g).exists
  have hcl := closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, w, hcov, fun i => jacquetFiltration γ (σ := σ) (cellUnion C i), ?_, ?_, ?_, ?_⟩
  · show jacquetFiltration γ (cellUnion C 0) = ⊥
    rw [cellUnion_zero, jacquetFiltration_empty]
  · show jacquetFiltration γ (cellUnion C k) = ⊤
    rw [cellUnion_of_cover hcov', jacquetFiltration_univ]
  · exact fun i i' h => jacquetFiltration_mono γ (cellUnion_mono h)
  refine ⟨fun i m => jacquetFiltration_le_comap γ (cellUnion_mul_mem w i).1 m, fun j => ?_⟩
  have hYo : IsOpen (cellUnion C ((j : ℕ) + 1)) := isOpen_cellUnion hdisj hcov' hcl _
  have hCY : closure (C j) ∩ cellUnion C ((j : ℕ) + 1) = C j :=
    closure_inter_cellUnion_succ hdisj hcl j
  have hYQ := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).1
  have hYP := (cellUnion_mul_mem (F := F) (β := β) (γ := γ) w ((j : ℕ) + 1)).2
  have hdiff : cellUnion C ((j : ℕ) + 1) \ C j = cellUnion C j := by
    rw [cellUnion_succ j, union_sdiff_right, (disjoint_cellUnion hdisj j).symm.sdiff_eq_left]
  refine ⟨⟨gradedJacquetMap γ (w j) σ hYo hCY hYQ, fun m => ?_⟩, ?_, fun x => ?_⟩
  · refine LinearMap.ext fun x => ?_
    exact gradedJacquetMap_jacquetRep σ hYo hCY hYQ m x
  · exact gradedJacquetMap_surjective σ hYo hCY hYQ (cellJacquetMap_surjective hYo hCY hYP hYQ hσ)
  · have := gradedJacquetMap_eq_zero_iff σ hYo hCY hYQ
      (fun f hf h0 => exists_sub_mem_ker_of_cellJacquet_eq_zero σ hσ hYo hCY hYQ hf h0) x
    rw [hdiff] at this
    exact this

end Parabolic

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.Spherical
section
noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra HeckeAlgebraLevel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Characters

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem exists_ker_sphericalCharacter_eq (I : Ideal (SphericalHecke μ (F := F) (n := n)))
    [I.IsMaximal] : ∃ w : Fin n → ℂˣ,
      RingHom.ker (sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w)) = I := by
  haveI := isIntegral_satake (μ := μ) (F := F) (n := n)
  obtain ⟨w, hw⟩ := exists_ker_evalAt_comp_eq (satakeHom μ) satakeHom_injective I
  exact ⟨w, by rw [← evalAt_comp_satakeHom]; exact hw⟩

end Characters

end Spherical

end GroundTheory.Automorphic
end
end

