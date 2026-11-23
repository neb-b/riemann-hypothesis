module

public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyPacketOfEquivalentStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.MinkowskiDividesFactorialOfBound
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0003
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusOrthonormalIntegralUnimodular
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

theorem c3eqv_mem_orth (U : Submodule E S.V) (x : S.V) : x ∈ orth S U ↔ ∀ v ∈ U, S.hT v x = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem c3eqv_gmap_iff (n : S.V ≃ₗ[E] S.V) (Λ : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ ↔ (∀ y ∈ Λ, n y ∈ Λ) ∧ ∀ y ∈ Λ, n.symm y ∈ Λ := by
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h]
      exact ⟨y, hy, rfl⟩
    · rw [← h] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      simpa using hz
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact h1 z hz
    · intro y hy
      exact ⟨n.symm y, h2 y hy, by simp⟩

theorem c3eqv_symm_mem (n : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) (h : ∀ x ∈ U, n x ∈ U) :
    ∀ x ∈ U, n.symm x ∈ U := by
  have hle : U.map (n : S.V →ₗ[E] S.V) ≤ U := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have heq : U.map (n : S.V →ₗ[E] S.V) = U :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq n U)
  intro x hx
  have hx' : x ∈ U.map (n : S.V →ₗ[E] S.V) := heq.symm ▸ hx
  obtain ⟨y, hy, rfl⟩ := hx'
  simpa using hy

theorem c3eqv_isom_symm {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) : n.symm ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  show ∀ x y, S.hT (n.symm x) (n.symm y) = S.hT x y
  intro x y
  have := hiso (n.symm x) (n.symm y)
  simp only [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem c3eqv_isom_trans {n m : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h' : m ∈ Formalism.HermitianLatticesTheory.isom S.hT) :
    n.trans m ∈ Formalism.HermitianLatticesTheory.isom S.hT := by
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have hiso' : ∀ x y, S.hT (m x) (m y) = S.hT x y := h'
  show ∀ x y, S.hT ((n.trans m) x) ((n.trans m) y) = S.hT x y
  intro x y
  simp only [LinearEquiv.trans_apply, hiso', hiso]

theorem c3eqv_orth_map {n : S.V ≃ₗ[E] S.V} (h : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (U₁ U₂ : Submodule E S.V)
    (hU : ∀ v ∈ U₂, n.symm v ∈ U₁) {x : S.V} (hx : x ∈ orth S U₁) : n x ∈ orth S U₂ := by
  rw [c3eqv_mem_orth] at hx ⊢
  intro v hv
  have hiso : ∀ x y, S.hT (n x) (n y) = S.hT x y := h
  have := hiso (n.symm v) x
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  exact hx _ (hU v hv)

variable {T : E} (F : LFlag S r T)

theorem c3eqv_Xflag_mono (j : ℕ) : Xflag F j ≤ Xflag F (j + 1) := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < j) => Nat.lt_succ_of_lt hi)

theorem c3eqv_Xflag_zero : Xflag F 0 = ⊥ := by
  unfold Xflag Formalism.MainNotions.S.FlagG.Xa
  simp

theorem c3eqv_Xsp_eq : Xsp F = Xflag F r := by
  unfold Xsp Xflag Formalism.MainNotions.S.FlagG.X Formalism.MainNotions.S.FlagG.Xa
  congr 1
  ext v
  simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, Fin.is_lt, true_and]

variable {F} {Λ : Submodule (𝓞 E) S.V}

theorem c3eqv_N_flag {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, n x ∈ Xflag F j := by
  unfold NLam at hn
  simp only [Set.mem_setOf_eq] at hn
  obtain ⟨_, h1, _⟩ := hn
  intro x hx
  cases j with
  | zero =>
    rw [c3eqv_Xflag_zero] at hx ⊢
    rw [(Submodule.mem_bot E).1 hx, map_zero]
    exact Submodule.zero_mem _
  | succ j =>
    have h2 := c3eqv_Xflag_mono F j (h1 j x hx)
    have e : n x = (n x - x) + x := by abel
    rw [e]
    exact Submodule.add_mem _ h2 hx

theorem c3eqv_N_X {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ Xsp F, n x ∈ Xsp F := by
  rw [c3eqv_Xsp_eq]
  exact c3eqv_N_flag hn r

theorem c3eqv_N_orth {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : ∀ x ∈ orth S (Xsp F), n x ∈ orth S (Xsp F) := by
  have hX := c3eqv_N_X hn
  have h' := hn
  unfold NLam at h'
  simp only [Set.mem_setOf_eq] at h'
  unfold IsAutLam at h'
  exact fun x hx => c3eqv_orth_map h'.1.1 _ _ (c3eqv_symm_mem n _ hX) hx

theorem c3eqv_NLam_trans {n m : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F) : n.trans m ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  have hm' := hm
  unfold NLam at hn' hm' ⊢
  simp only [Set.mem_setOf_eq] at hn' hm' ⊢
  unfold IsAutLam at hn' hm' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  obtain ⟨⟨hmi, hmg⟩, hm1, hm2⟩ := hm'
  refine ⟨⟨c3eqv_isom_trans hni hmi, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng hmg ⊢
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      exact hmg.1 _ (hng.1 _ hy)
    · simp only [LinearEquiv.symm_trans_apply]
      exact hng.2 _ (hmg.2 _ hy)
  · intro j x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm1 j _ (hnf (j + 1) x hx)) (hn1 j x hx)
  · intro x hx
    have e : (n.trans m) x - x = (m (n x) - n x) + (n x - x) := by
      simp only [LinearEquiv.trans_apply]; abel
    rw [e]
    exact Submodule.add_mem _ (hm2 _ (hno x hx)) (hn2 x hx)

theorem c3eqv_NLam_symm {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) : n.symm ∈ NLam Λ F := by
  have hnf := c3eqv_N_flag hn
  have hno := c3eqv_N_orth hn
  have hn' := hn
  unfold NLam at hn' ⊢
  simp only [Set.mem_setOf_eq] at hn' ⊢
  unfold IsAutLam at hn' ⊢
  obtain ⟨⟨hni, hng⟩, hn1, hn2⟩ := hn'
  refine ⟨⟨c3eqv_isom_symm hni, ?_⟩, ?_, ?_⟩
  · rw [c3eqv_gmap_iff] at hng ⊢
    rw [LinearEquiv.symm_symm]
    exact ⟨hng.2, hng.1⟩
  · intro j x hx
    have hy := c3eqv_symm_mem n _ (hnf (j + 1)) x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn1 j _ hy)
  · intro x hx
    have hy := c3eqv_symm_mem n _ hno x hx
    have e : n.symm x - x = -(n (n.symm x) - n.symm x) := by
      rw [LinearEquiv.apply_symm_apply]; abel
    rw [e]
    exact Submodule.neg_mem _ (hn2 _ hy)

end Gen

section D7

variable (D : D7)

variable (Λ : LatV D) {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)

end D7

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.ForPrimeFlagLattice
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ForPrimeFlagLattice (D : D7) (u : D.what₂.Word)
    (Q : (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) → LatV D → Prop) : Prop :=
  (Tu D u).Prime → 3 ≤ Tu D u → SplitsCompletely (E := D.host.E) (Tu D u) →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ → Q F0 Λ

def BaseLatticeStructure (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ =>
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) ∧
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ (lf D F0)) ∧
    latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ) ∧
    DiscGen (D.sp.X 0).hT (L0X D Λ (lf D F0)) 1 ∧
    ∀ p : Ideal (𝓞 D.host.F), p.IsMaximal → ((Tu D u : ℕ) : 𝓞 D.host.F) ∈ p →
      eP (D.sp.X 0).hT (L0X D Λ (lf D F0)) p = 1

def WordRowsGluing (D : D7) (u : D.what₂.Word) : Prop :=
  ForPrimeFlagLattice D u fun F0 Λ => ∀ s : Finset (LatV D), IsRowReps D F0 s →
    massRows D F0 s = Formalism.HermitianLatticesTheory.mass (D.sp.X 0).hT (L0X D Λ (lf D F0)) * ((Tu D u : ℝ) - 1) ^ D.R.f

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleAllConstants
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.HermitianLatticeCounting
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SW

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def classWeightAlt : ℝ :=
  (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f * (classNumber D.host.E : ℝ) * 2 ^ D.R.f

end SW

section W0

variable (D : D7) (large₂ : SizeData₂ D)

end W0

section SWF

variable {eps : ℝ} (Fm : FamP eps)

end SWF

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenusMassPosOfMassLowerBound
section
noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

end Count

section Lat

variable (D : D7)

end Lat

section Num

end Num

section Main

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Main

section Inv

variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem c3sub_dual_gmap (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual h (Formalism.HermitianLatticesTheory.gmap γ M) = Formalism.HermitianLatticesTheory.gmap γ (Formalism.HermitianLatticesTheory.dual h M) := by
  have hiso : ∀ x y : V, h (γ x) (γ y) = h x y := fun x y => hγ x y
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap Formalism.HermitianLatticesTheory.dual E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_map]
  constructor
  · intro hx
    refine ⟨γ.symm x, ?_, by simp⟩
    intro m hm
    have hm' := hx (γ m) ⟨m, hm, rfl⟩
    simpa [← hiso m (γ.symm x)] using hm'
  · rintro ⟨z, hz, rfl⟩ y ⟨m, hm, rfl⟩
    have hm' := hz m hm
    simpa [hiso] using hm'

end Inv

section Mean

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

end Mean

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PlaneMassBoundOfFacts
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.HermitianLatticesTheory

def SecondOrthogonalVector (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsIntegralLat h M → dual h M = M →
    ∀ x ∈ M, x ≠ 0 → ∃ y ∈ M, y ≠ 0 ∧ h x y = 0 ∧ ∀ φ : K →+* ℂ, ‖φ (h y y)‖ ≤ ‖φ (h x x)‖ * rootDiscriminant K

def PlaneClassCount (K : Type) [Field K] [NumberField K] [StarRing K] : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), h.IsSymm → IsOrthoLattice h L 2 →
    ∀ s : Finset (Submodule (𝓞 K) V), Formalism.ThetaLiftIndependence.IsClassReps h L s → ∀ B₁ B₂ : ℝ,
    (∀ M ∈ s, IsIntegralLat h M) →
    (∀ M ∈ s, ∃ x ∈ M, ∃ y ∈ M, x ≠ 0 ∧ y ≠ 0 ∧ h x y = 0 ∧
      ∀ φ : K →+* ℂ, ‖φ (h x x)‖ ≤ B₁ ∧ ‖φ (h y y)‖ ≤ B₂) →
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * B₂) ^ (2 * finrank ℚ K) *
      (B₁ * B₂) ^ (4 * finrank ℚ K)

theorem card_class_reps_plane_le (K : Type) [Field K] [NumberField K] [StarRing K] (B₁ : ℝ)
    (hA : ShortVectorEveryPlace K B₁) (hB : SecondOrthogonalVector K) (hC : PlaneClassCount K) (hrd : 0 ≤ rootDiscriminant K)
    (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hs : h.IsSymm) (hL : IsOrthoLattice h L 2)
    (s : Finset (Submodule (𝓞 K) V)) (hreps : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    (s.card : ℝ) ≤ (1 + 2 * B₁) ^ (2 * finrank ℚ K) * (1 + 2 * (B₁ * rootDiscriminant K)) ^ (2 * finrank ℚ K) *
      (B₁ * (B₁ * rootDiscriminant K)) ^ (4 * finrank ℚ K) := by
  refine hC V h L hs hL s hreps B₁ (B₁ * rootDiscriminant K)
    (fun M hM => (genus_orthonormal_integral_unimodular h hs L hL M (hreps.1 M hM)).1) fun M hM => ?_
  have hg := hreps.1 M hM
  have hMlat : Submodule.IsLattice K M := hg.1.toIsLattice
  obtain ⟨hint, huni⟩ := genus_orthonormal_integral_unimodular h hs L hL M hg
  obtain ⟨x, hx, hx0, hxB⟩ := hA V h L hs hL M hg
  obtain ⟨y, hy, hy0, hxy, hyB⟩ := hB V h L hs hL M hMlat hint huni x hx hx0
  exact ⟨x, hx, y, hy, hx0, hy0, hxy, fun φ =>
    ⟨hxB φ, (hyB φ).trans (mul_le_mul_of_nonneg_right (hxB φ) hrd)⟩⟩

end Formalism.MainNotions.BridgeLemma₂

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem plane_mass_bound_of_facts (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C B₁ : ℝ)
    (hA : ShortVectorEveryPlace D.host.E B₁) (hB : SecondOrthogonalVector D.host.E) (hCt : PlaneClassCount D.host.E)
    (hB0 : 0 ≤ B₁) (hB1 : B₁ ≤ 4 * D.R.f * D.host.rdE) (hC : 55 * max 1 (1 / Cl) ≤ C ^ 2)
    (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) : UnitaryVolumeMass.Mass2At D large₂ C := by
  intro V _ _ _ _ h L hs ho
  obtain ⟨-, -, h3, -, h5, -, -, -, -, -, h11, -, -, -, -, -, -, -, h19, -⟩ := hH
  have hm := D.R.two_le_m
  have hf : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) h3
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hrd : 2 ≤ D.host.rdE := by
    have e : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
    rw [← e]; linarith
  have hlrd : Real.log D.host.rdE ≤ max 1 (1 / Cl) * large₂.sc.L := by
    refine le_trans h11 ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  have hlf : Real.log (D.R.f : ℝ) ≤ (D.R.m : ℝ) := by
    refine le_trans h5 ?_
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have h2 : (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast h1
    have h3 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hrdE : rootDiscriminant D.host.E = D.host.rdE := rfl
  have hnum := mass_pow_le_exp_rpow D.R.f D.R.m D.host.rdE large₂.sc.L B₁ C (max 1 (1 / Cl)) hf hm hrd hL1 (le_max_left _ _) hlf hlrd hB0 hB1 hC
  have hb : large₂.sc.b = Real.exp large₂.sc.L := rfl
  rw [hb]
  refine mass_le_of_card_class_reps_le h L _ (by positivity) fun s hreps => ?_
  have hc := card_class_reps_plane_le D.host.E B₁ hA hB hCt (by rw [hrdE]; linarith) V h L hs ho s hreps
  rw [hrdE, Formalism.MainNotions.StandardLattice.finrank_host] at hc
  exact hc.trans hnum

end Formalism.MainNotions.BridgeLemma₂

end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.RowsDef
section
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.HermitianLatticeCounting Formalism.MainNotions.BridgeLemma

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7}

abbrev termGramMatrix (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : GramM D := ZhatL (X.fl t) (X.fl' t)

def wordPairGramNorm (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ := ∏ τ, nV D (Tu D u) (Tu D u') Z τ

def wordPairGramProduct (D : D7) (u u' : D.what₂.Word) (Z : GramM D) : ℝ :=
  (∏ τ, Formalism.MainNotions.S.Cnt.Gz D (Tu D u) (Tu D u') Z τ) * ((gS D : ℝ)⁻¹) ^ (D.R.m * D.R.f)

def pairDeterminant (X : TermTie D) {u u' : D.what₂.Word} (p : D.s.Pair u u') : ℝ :=
  latDet (hS D) (Mlat (X.abelian₂ (D.s.pfst p)) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) (X.fl' (D.s.psnd p)) (X.beta p) (gS D)) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.pfst p)) : ℝ) *
    (iIdx (X.abelian₂ (D.s.pfst p)) (gS D) (X.fl (D.s.pfst p)) (X.fl' (D.s.psnd p)) : ℝ)

def wordPairDeterminantGeOne (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ pairDeterminant X p

def wordPairEntriesInLattice (X : TermTie D) (u u' : D.what₂.Word) : Prop :=
  ∀ a b : Fin (D.R.rS + 1), ∃ Λ : AddSubgroup (D.what₂.Tau → ℂ), (∀ x ∈ Λ, x ≠ 0 → 1 ≤ ∏ v, ‖x v‖) ∧
    ∀ (t : D.s.Term u u') (Z : GramM D), D.s.Gterm t ≠ 0 → D.s.relevant t → ZEquiv (termGramMatrix X t) Z →
      (fun τ => ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (Z a b)) ∈ Λ

end Defs

end Formalism.MainNotions.BridgeLemma₂

end
end

