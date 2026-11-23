module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CntPrimLatticeImageIsometry
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC

section

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [NumberField K] [StarRing K] in
theorem primInv_span_gmap (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Submodule.span K ((Formalism.HermitianLatticesTheory.gmap γ M : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.map_coe, ← Submodule.span_image]
  try rfl


omit [NumberField K] [StarRing K] in
theorem primInv_gmap_injective (γ : V ≃ₗ[K] V) :
    Function.Injective (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) := by
  intro M N hMN
  exact Submodule.map_injective_of_injective (f := (γ : V →ₗ[K] V).restrictScalars (𝓞 K))
    γ.injective hMN

omit [NumberField K] [StarRing K] in
theorem primInv_gmap_symm (γ : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap γ⁻¹ (Formalism.HermitianLatticesTheory.gmap γ M) = M := by
  ext x
  unfold Formalism.HermitianLatticesTheory.gmap
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    change γ.symm (γ z) ∈ M
    rwa [γ.symm_apply_apply]
  · intro hx
    exact ⟨γ x, ⟨x, hx, rfl⟩, γ.symm_apply_apply x⟩

theorem primInv_mem (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) (M : Submodule (𝓞 K) V) (hM : M ∈ PrimSubs h L j de) :
    Formalism.HermitianLatticesTheory.gmap γ M ∈ PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  obtain ⟨⟨hle, heq⟩, hrk, hdet⟩ := hM
  have hspan := primInv_span_gmap γ M
  refine ⟨⟨Submodule.map_mono hle, ?_⟩, ?_, ?_⟩
  ·
    have hres : ((Submodule.span K (M : Set V)).map (γ : V →ₗ[K] V)).restrictScalars (𝓞 K) =
        ((Submodule.span K (M : Set V)).restrictScalars (𝓞 K)).map
          ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) := by
      ext x; exact Iff.rfl
    rw [hspan, hres]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_inf ((γ : V →ₗ[K] V).restrictScalars (𝓞 K)) γ.injective, ← heq]
  · rw [hspan, LinearEquiv.finrank_map_eq]
    exact hrk
  · rw [← hdet]
    exact _root_.GlobalTheory.LoopC.DetMap.latDetH_map K V V h h (γ : V →ₗ[K] V) γ.injective (fun x y => hγ x y) M

theorem primInv_le (h : V →ₗ⋆[K] V →ₗ[K] K) (γ : V ≃ₗ[K] V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom h)
    (L : Submodule (𝓞 K) V) (j de : ℕ) : cntPrim h L j de ≤ cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
  unfold cntPrim
  rw [← Set.InjOn.encard_image (f := fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M)
    (s := PrimSubs h L j de) (fun _ _ _ _ hab => primInv_gmap_injective γ hab)]
  have hsub : (fun M : Submodule (𝓞 K) V => Formalism.HermitianLatticesTheory.gmap γ M) '' PrimSubs h L j de ⊆
      PrimSubs h (Formalism.HermitianLatticesTheory.gmap γ L) j de := by
    rintro _ ⟨M, hM, rfl⟩
    exact primInv_mem h γ hγ L j de M hM
  first
    | exact Set.encard_le_encard hsub
    | exact Set.encard_mono hsub
    | exact Set.encard_le_card hsub

end

theorem cntPrim_gmap_isom : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), ∀ γ ∈ Formalism.HermitianLatticesTheory.isom h, ∀ (L : Submodule (𝓞 K) V) (j de : ℕ), cntPrim h (Formalism.HermitianLatticesTheory.gmap γ L) j de = cntPrim h L j de := by
  intro K V _ _ _ _ _ _ _ h γ hγ L j de
  refine le_antisymm ?_ (primInv_le h γ hγ L j de)
  have := primInv_le h γ⁻¹ (inv_mem hγ) (Formalism.HermitianLatticesTheory.gmap γ L) j de
  rwa [primInv_gmap_symm] at this

end GlobalTheory.LoopC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CwContIntegralCommStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cwCont_integral_comm_alt : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (Bm : R.H → V), (∀ v ∈ R.sm, ∀ w ∈ R.sm, Bm (v + w) = Bm v + Bm w) → (∀ (a : ℂ), ∀ v ∈ R.sm, Bm (a • v) = a • Bm v) → PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ Bm → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Mx k r) (p : X → ℂ), Continuous κ → (∀ x, κ x ∈ GG k r) → Continuous p → ∀ v ∈ R.sm, (∫ x, p x • R.σ (κ x) v ∂μ) ∈ R.sm → Bm (∫ x, p x • R.σ (κ x) v ∂μ) = ∫ x, p x • Bm (R.σ (κ x) v) ∂μ := by
  first | exact @GlobalTheory.cwCont_integral_comm | exact GlobalTheory.cwCont_integral_comm | (intros; apply GlobalTheory.cwCont_integral_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLatticeDiscriminantModuleCardDetSq
section
namespace GlobalTheory.LoopC.DetCard

section General

open NumberField GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.MainNotions.S

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V] [Module K V]
  [IsScalarTower (𝓞 K) K V]

theorem map_latIn {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : ∀ x ∈ N, x ∈ U) :
    N.toAddSubgroup = (latIn U N).toAddSubgroup.map U.subtype.toAddMonoidHom := by
  ext x
  constructor
  · intro h1
    exact ⟨⟨x, hN x h1⟩, h1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

theorem idxN_latIn {U : Submodule K V} {A B : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, x ∈ U)
    (hB : ∀ x ∈ B, x ∈ U) : idxN A B = idxN (latIn U A) (latIn U B) := by
  rw [idxN, idxN, map_latIn hA, map_latIn hB, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem isLattice_latIn_span {U : Submodule K V} {N : Submodule (𝓞 K) V} (hN : N.FG)
    (hU : Submodule.span K (N : Set V) = U) : Submodule.IsFullLattice K (latIn U N) := by
  haveI : Submodule.IsLattice K (latIn U N) := by
    apply Submodule.IsLattice.of_fg K
    refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hN (Submodule.map_comap_le _ _)
  refine ⟨?_⟩
  apply Submodule.map_injective_of_injective U.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  rw [← hU]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hU ▸ Submodule.subset_span hx⟩, hx, rfl⟩

variable [StarRing K]

theorem latIn_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    latIn U (Lat.dualInH h N) = dual (hRes h U) (latIn U N) := by
  ext x
  constructor
  · rintro ⟨h1, -⟩
    exact (dualBasic_mem_dual _ _ _).2 fun y hy => (dualBasic_mem_dual _ _ _).1 h1 y hy
  · intro hx
    refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, ?_⟩
    · exact (dualBasic_mem_dual _ _ _).1 hx ⟨z, hU ▸ Submodule.subset_span hz⟩ hz
    · change (x : V) ∈ Submodule.span K (N : Set V)
      rw [hU]
      exact x.2

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) {U : Submodule K V} {N : Submodule (𝓞 K) V}
    (hU : Submodule.span K (N : Set V) = U) :
    idxN (Lat.dualInH h N) N = discN (hRes h U) (latIn U N) := by
  rw [idxN_latIn (U := U) (A := Lat.dualInH h N) (B := N) (fun x hx => hU ▸ (Submodule.mem_inf.1 hx).2) (fun x hx => hU ▸ Submodule.subset_span hx),
    latIn_dualInH h hU, discN]

theorem general [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hK : IsCMUnram K) (hs : h.IsSymm) (hp : PD h)
    (M : Submodule (𝓞 K) V) (hM : M.FG) (hI : IsIntegralLat h M) :
    1 ≤ idxN (Lat.dualInH h M) M ∧ (idxN (Lat.dualInH h M) M : ℝ) = Lat.latDetH h M ^ 2 ∧
      ∀ P : Submodule (𝓞 K) V, P ≤ M →
        Module.finrank K (Submodule.span K (P : Set V)) = Module.finrank K (Submodule.span K (M : Set V)) →
        1 ≤ idxN M P ∧ Lat.latDetH h P = Lat.latDetH h M * idxN M P := by
  set U := Submodule.span K (M : Set V) with hUdef
  have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
  have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
  have hnU := DetAgree.nondeg_of_pd hpU
  have key : ∀ N : Submodule (𝓞 K) V, N ≤ M → Submodule.span K (N : Set V) = U →
      IsIntLat (hRes h U) (latIn U N) ∧ discN (hRes h U) (latIn U N) ≠ 0 ∧
        Lat.latDetH h N = Real.sqrt (discN (hRes h U) (latIn U N) : ℝ) := by
    intro N hN hU
    have a : IsIntLat (hRes h U) (latIn U N) :=
      ⟨isLattice_latIn_span (hM.of_le hN) hU, fun x hx y hy => hI x (hN hx) y (hN hy)⟩
    have n0 := (DiscOrder.main K U _ hK hsU hnU _ a).1
    refine ⟨a, n0, ?_⟩
    rw [← idxN_dualInH h hU] at n0 ⊢
    rw [Lat.latDetH, DetAgree.genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hI y (hN hy) x (hN hx), Submodule.subset_span hx⟩
  obtain ⟨m1, m2, m3⟩ := key M le_rfl rfl
  refine ⟨?_, ?_, fun P hP hr => ?_⟩
  · rw [idxN_dualInH h hUdef.symm]
    exact Nat.pos_of_ne_zero m2
  · rw [idxN_dualInH h hUdef.symm, m3, Real.sq_sqrt (Nat.cast_nonneg _)]
  · have hU : Submodule.span K (P : Set V) = U :=
      Submodule.eq_of_le_of_finrank_eq (Submodule.span_mono hP) hr
    obtain ⟨p1, -, p3⟩ := key P hP hU
    obtain ⟨q1, q2⟩ := (DiscOrder.main K U _ hK hsU hnU _ p1).2.2.1 _ m1 (Submodule.comap_mono hP)
    rw [← idxN_latIn (U := U) (fun x hx => Submodule.subset_span hx)
      (fun x hx => Submodule.subset_span (hP hx))] at q1 q2
    refine ⟨Nat.pos_of_ne_zero q1, ?_⟩
    rw [p3, m3, q2, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (Nat.cast_nonneg _),
      Real.sqrt_sq (Nat.cast_nonneg _)]

end General

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (D : D7) (M : LatW D), M.FG → IsPosDef (D.sp.X 0).hT → Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT M → 1 ≤ idxW D (dualInH (D.sp.X 0).hT M) M ∧ (idxW D (dualInH (D.sp.X 0).hT M) M : ℝ) = detW D M ^ 2 ∧ ∀ P : LatW D, P ≤ M → rkW D P = rkW D M → 1 ≤ idxW D M P ∧ detW D P = detW D M * idxW D M P := by
  intro D M hM hp hI
  exact general (D.sp.X 0).hT D.sp.cm.cmUnram (D.sp.X 0).herm hp M hM hI

end GlobalTheory.LoopC.DetCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetMatrixSandwichLinearMapStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_matrix_sandwich_linear_map : ∀ (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ) (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ)), (∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) → LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first | exact @GlobalTheory.MatMulDet.det_real_mul_mul | exact GlobalTheory.MatMulDet.det_real_mul_mul | (intros; apply GlobalTheory.MatMulDet.det_real_mul_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAutStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  letI := hΛ
  exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL E hE j Λ inferInstance γ hγ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsClosedEmbeddingOrthogonalUnitaryRealPlaceStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedEmbedding_orthogonalUnitary_realPlace : ∀ (n m : ℕ) (ε : Fin n → Bool) (ε' : Fin m → Bool) (s : Bool) (x₀ : Fin n → ℂ) (B : Matrix (Fin n) (Fin m) ℂ), m + 1 = n → qEps ε x₀ = sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → ∃ j : Formalism.REAL.UJ ε' →* Formalism.REAL.UJ ε, Topology.IsClosedEmbedding j ∧ ∀ g, uMat (j g) *ᵥ x₀ = x₀ ∧ uMat (j g) * B = B * uMat g := by
  first | exact @GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | exact GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal | (intros; apply GlobalTheory.StabUnfold.exists_closedEmbedding_unitary_orthogonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualFamilyInSelfDualLattice
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.SelfDualFrame

section Algebra

variable {E : Type} [CommRing E] (O : Subring E)

def consZero (n : ℕ) : (Fin n → O) →ₗ[O] (Fin (n + 1) → O) where
  toFun v := Fin.cons 0 v
  map_add' v w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' k v := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem eq_top_of_dual
    (hQ : ∀ J : Ideal O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ O) → d ∈ O) → J = ⊤) :
    ∀ (n : ℕ) (I : Submodule O (Fin n → O)),
      (∀ c : Fin n → E, (∀ x ∈ I, ∑ i, c i * (x i : E) ∈ O) → ∀ i, c i ∈ O) → I = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro I _
    rw [eq_top_iff]
    intro x _
    rw [Subsingleton.elim x 0]
    exact I.zero_mem
  | succ n ih =>
    intro I hI
    have hJ : I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) = ⊤ := by
      refine hQ _ (fun d hd => ?_)
      have h := hI (Pi.single 0 d) (fun x hx => by
        have h1 : ∑ i, (Pi.single 0 d : Fin (n + 1) → E) i * (x i : E) = d * (x 0 : E) := by
          rw [Finset.sum_eq_single 0]
          · simp
          · intro b _ hb; simp [Pi.single_apply, hb]
          · simp
        rw [h1]
        exact hd (x 0) ⟨x, hx, rfl⟩)
      simpa using h 0
    obtain ⟨x₁, hx₁, h1⟩ : ∃ x ∈ I, x 0 = 1 := by
      have : (1 : O) ∈ I.map (LinearMap.proj 0 : (Fin (n + 1) → O) →ₗ[O] O) := by
        rw [hJ]; exact Submodule.mem_top
      obtain ⟨x, hx, e⟩ := this
      exact ⟨x, hx, e⟩
    have hret : ∀ w : Fin (n + 1) → O, consZero O n (Fin.tail (w - w 0 • x₁)) = w - w 0 • x₁ := by
      intro w
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [consZero, h1]
      · simp [consZero, Fin.tail]
    have hI₀ : I.comap (consZero O n) = ⊤ := by
      refine ih _ (fun c hc => ?_)
      have h := hI (Fin.cons (-∑ i, c i * (x₁ i.succ : E)) c) (fun w hw => by
        have hm : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by
          rw [Submodule.mem_comap, hret]
          exact I.sub_mem hw (I.smul_mem _ hx₁)
        have h2 := hc _ hm
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        convert h2 using 1
        simp only [Fin.tail, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        push_cast
        rw [neg_mul, Finset.sum_mul]
        simp only [mul_sub, Finset.sum_sub_distrib]
        have e3 : ∀ i, c i * ((w 0 : E) * (x₁ i.succ : E)) = c i * (x₁ i.succ : E) * (w 0 : E) :=
          fun i => by ring
        simp only [e3]
        ring)
      intro i
      simpa using h i.succ
    rw [eq_top_iff]
    intro w _
    have e : w = consZero O n (Fin.tail (w - w 0 • x₁)) + w 0 • x₁ := by rw [hret]; abel
    rw [e]
    refine I.add_mem ?_ (I.smul_mem _ hx₁)
    have : Fin.tail (w - w 0 • x₁) ∈ I.comap (consZero O n) := by rw [hI₀]; exact Submodule.mem_top
    exact this

end Algebra

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem ideal_eq_top_of_inv [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) :
    ∀ J : Ideal L.O, (∀ d : E, (∀ j ∈ J, d * (j : E) ∈ L.O) → d ∈ L.O) → J = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -, hPIR, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx => (hO2 x hx).1
  have hz : ∀ u : F, (∀ t : F, algebraMap F E (t * u) ∈ L.O) → u = 0 := by
    intro u hu
    by_contra h0
    have h3 := (hmem _).1 (hu ((ϖ : F)⁻¹ * u⁻¹))
    rw [mul_assoc, inv_mul_cancel₀ h0, mul_one] at h3
    have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a := ϖ) ⟨_, h3⟩ (Subtype.ext (by simp [hϖ0])))
  intro J hJ
  obtain ⟨a, rfl⟩ := (hPIR.principal J).principal
  by_cases hu : IsUnit (a : E)
  · obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hbO : b ∈ L.O := hJ b (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show b * ((k : E) * a) = k by linear_combination (k : E) * hb]
      exact k.2)
    exact Ideal.span_singleton_eq_top.2 (IsUnit.of_mul_eq_one (a := a) ⟨b, hbO⟩ (Subtype.ext hb))
  · exfalso
    haveI : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
    have hns : ¬ Function.Surjective (LinearMap.mulLeft F (a : E)) := fun h => hu (by
      obtain ⟨b, hb⟩ := h 1
      exact IsUnit.of_mul_eq_one b hb)
    have hni : ¬ Function.Injective (LinearMap.mulLeft F (a : E)) :=
      fun h => hns (LinearMap.injective_iff_surjective.1 h)
    obtain ⟨s, hs, hs0⟩ : ∃ s : E, (a : E) * s = 0 ∧ s ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hni ((injective_iff_map_eq_zero _).2 (fun s h => hc s h))
    have hts : ∀ t : F, algebraMap F E t * s ∈ L.O := fun t => hJ _ (fun j hj => by
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.1 hj
      push_cast
      rw [show algebraMap F E t * s * ((k : E) * a) = 0 by
        linear_combination (algebraMap F E t * k) * hs]
      exact L.O.zero_mem)
    have hs1 : s ∈ L.O := by simpa using hts 1
    obtain ⟨u, hu'⟩ := (L.cj_fix (s + L.cj s)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
    obtain ⟨m, hm⟩ := (L.cj_fix (s * L.cj s)).1 (by rw [map_mul, L.cj_cj, mul_comm])
    have hu0 : u = 0 := hz u (fun t => by
      have h4 := L.O.add_mem (hts t) (hcj _ (hts t))
      convert h4 using 1
      rw [map_mul, hu', map_mul, AlgEquiv.commutes]
      ring)
    have hm0 : m = 0 := hz m (fun t => by
      have h4 := L.O.mul_mem (hts t) (hcj _ hs1)
      convert h4 using 1
      rw [map_mul, hm]
      ring)
    rw [hu0, map_zero] at hu'
    rw [hm0, map_zero] at hm
    have hss : s ^ 2 = 0 := by linear_combination (-s) * hu' + hm
    have := L.reduced
    exact hs0 (IsReduced.eq_zero s ⟨2, hss⟩)

end Local

theorem exists_dual_family : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ y : Fin (r + 1) → V, (∀ b, y b ∈ Λ) ∧ ∀ a b, H.h (y b) (Fr.f a) = if a = b then 1 else 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hsd hfr
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨-, hO2, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hcj : ∀ x ∈ M.L.O, M.L.cj x ∈ M.L.O := fun x hx => (hO2 x hx).1
  obtain ⟨-, -, hd⟩ := hsd
  obtain ⟨⟨hfΛ, hli, hprim⟩, -⟩ := hfr
  have hval : ∀ y ∈ Λ, ∀ a, H.h y (Fr.f a) ∈ M.L.O := fun y hy a => (hd y).1 hy _ (hfΛ a)
  have hsum : ∀ (y : V) (g : Fin (r + 1) → V), H.h (∑ a, g a) y = ∑ a, H.h (g a) y := fun y g =>
    map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) g Finset.univ
  have hh2 : ∀ (y : V) (k : Fin (r + 1) → E),
      H.h y (∑ a, k a • Fr.f a) = ∑ a, M.L.cj (k a) * H.h y (Fr.f a) := by
    intro y k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [H.h_herm, hsum, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [H.h_smul_left, map_mul, ← H.h_herm]
  let I : Submodule M.L.O (Fin (r + 1) → M.L.O) :=
    { carrier := {x | ∃ y ∈ Λ, ∀ a, (x a : E) = H.h y (Fr.f a)}
      add_mem' := by
        rintro x x' ⟨y, hy, e⟩ ⟨y', hy', e'⟩
        refine ⟨y + y', Λ.add_mem hy hy', fun a => ?_⟩
        simp only [Pi.add_apply, Subring.coe_add, H.h_add_left, e, e']
      zero_mem' := ⟨0, Λ.zero_mem, fun a => by simp [H.h_zero_left]⟩
      smul_mem' := by
        rintro k x ⟨y, hy, e⟩
        refine ⟨k • y, Λ.smul_mem k hy, fun a => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul, e]
        rw [Subring.smul_def, H.h_smul_left] }
  have hItop : I = ⊤ := by
    refine eq_top_of_dual M.L.O (ideal_eq_top_of_inv M.L) (r + 1) I (fun c hc => ?_)
    set w := ∑ a, M.L.cj (c a) • Fr.f a with hwdef
    have hw : ∀ y ∈ Λ, H.h y w ∈ M.L.O := fun y hy => by
      have h1 := hc (fun a => ⟨H.h y (Fr.f a), hval y hy a⟩) ⟨y, hy, fun a => rfl⟩
      rw [hwdef, hh2]
      simpa [M.L.cj_cj] using h1
    have hwΛ : w ∈ Λ := (hd w).2 (fun y hy => by
      rw [H.h_herm y w]
      exact hcj _ (hw y hy))
    have hwE : w ∈ Submodule.span E (Set.range Fr.f) :=
      Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
    obtain ⟨d, hdw⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hprim w hwΛ hwE)
    have heq : ∀ a, M.L.cj (c a) = d a := by
      have h2 := Fintype.linearIndependent_iff.1 hli (fun a => M.L.cj (c a) - (d a : E)) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hwdef, ← hdw]
        simp [Subring.smul_def])
      intro a
      exact sub_eq_zero.1 (h2 a)
    intro a
    have h3 := hcj _ (show M.L.cj (c a) ∈ M.L.O by rw [heq a]; exact (d a).2)
    rwa [M.L.cj_cj] at h3
  have hmemb : ∀ b, ∃ y ∈ Λ, ∀ a, ((Pi.single b 1 : Fin (r + 1) → M.L.O) a : E) = H.h y (Fr.f a) :=
    fun b => by
      have h4 : (Pi.single b 1 : Fin (r + 1) → M.L.O) ∈ I := by rw [hItop]; exact Submodule.mem_top
      exact h4
  choose y hyΛ hy using hmemb
  refine ⟨y, hyΛ, fun a b => ?_⟩
  rw [← hy b a, Pi.single_apply]
  split_ifs <;> simp

end GlobalTheory.SelfDualFrame
end
end

