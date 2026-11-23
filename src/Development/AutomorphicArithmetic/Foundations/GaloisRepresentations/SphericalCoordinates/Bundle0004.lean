module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0833
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerCoordLoc
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj colMat)

namespace UpperTheory.Gal.W2

theorem perCoordLoc_of : PerCoordLoc := by
  intro O _ bar g ρ D P₀ M₀ hP₀ hM₀ d co hco m B P b₀ hB hb₀ hHol hPb₀
  obtain ⟨α, β, hαβ⟩ := PerCoordU.exists_colMat_per hP₀
  obtain ⟨A, hA⟩ : ∃ A : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, A b = colMat α ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bm, hBm⟩ : ∃ Bm : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ, ∀ b, Bm b = colMat β ⇑(P b) :=
    ⟨_, fun _ => rfl⟩
  have hrep : ∀ b ∈ B, ∀ x, P b x = realMap (A b) (Bm b) (P₀ x) := by
    intro b hb x
    rw [hA, hBm]
    exact hαβ _ (hHol.1 b hb) x
  have hPd : ∀ (x : D.La) (i : Fin g), DifferentiableOn ℂ (fun b => P b x i) B :=
    fun x i => differentiableOn_pi.1 (hHol.2 x) i
  have hAd : ∀ i j, DifferentiableOn ℂ (fun b => A b i j) B := by
    intro i j
    simp only [hA, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hBd : ∀ i j, DifferentiableOn ℂ (fun b => Bm b i j) B := by
    intro i j
    simp only [hBm, colMat, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun x _ => (hPd x i).const_mul _
  have hAc : ContinuousOn A B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hdet : ContinuousOn (fun b => (A b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hAc
  have hSo : IsOpen (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton
  have hAB0 : A b₀ = 1 ∧ Bm b₀ = 0 := by
    apply realMap_inj
    apply PerCoordU.ext_per hP₀
    intro x
    have h1 := hrep b₀ hb₀ x
    rw [hPb₀] at h1
    rw [← h1, realMap_apply]
    simp
  have hb₀S : b₀ ∈ B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ := by
    refine ⟨hb₀, ?_⟩
    simp [hAB0.1]
  have hnhds : B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ ∈ 𝓝 b₀ := hSo.mem_nhds hb₀S
  have hinvd : ∀ i j, DifferentiableOn ℂ (fun b => (A b)⁻¹ i j) (B ∩ (fun b => (A b).det) ⁻¹' {0}ᶜ) :=
    RiemannRel.differentiableOn_left_inverse A (fun b => (A b)⁻¹)
      (fun i j => (hAd i j).mono Set.inter_subset_left)
      (fun b hb => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (by simpa using hb.2)))
  obtain ⟨gL, hgL⟩ := LinearMap.exists_leftInverse_of_injective co (LinearMap.ker_eq_bot.mpr hco.1)
  refine ⟨fun b => gL ((A b)⁻¹ * Bm b), ?_, ?_, ?_⟩
  · rw [differentiableAt_pi]
    intro k
    have e : (fun b => gL ((A b)⁻¹ * Bm b) k) =
        fun b => ∑ i, ∑ j, ((A b)⁻¹ * Bm b) i j * gL (Matrix.single i j 1) k :=
      funext fun b => PerCoordU.coords_sum gL _ k
    rw [e]
    refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
    refine DifferentiableAt.mul_const ?_ _
    simp only [Matrix.mul_apply]
    refine DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_mul ?_ ?_
    · exact (hinvd i l).differentiableAt hnhds
    · exact (hBd l j).differentiableAt (hB.mem_nhds hb₀)
  · simp only
    rw [hAB0.1, hAB0.2, Matrix.mul_zero, map_zero]
  · filter_upwards [hnhds] with b hb
    have hdetb : IsUnit (A b).det := isUnit_iff_ne_zero.mpr (by simpa using hb.2)
    have hCmem : (A b)⁻¹ * Bm b ∈ LinearMap.range co := by
      rw [hco.2]
      exact PerCoordU.mem_Tsp_of_period hP₀ (hHol.1 b hb.1) hM₀.2.2 (hrep b hb.1) hdetb.ne_zero
    obtain ⟨y, hy⟩ := hCmem
    have hcy : co (gL ((A b)⁻¹ * Bm b)) = (A b)⁻¹ * Bm b := by
      rw [← hy, ← LinearMap.comp_apply gL co, hgL, LinearMap.id_apply]
    letI := Matrix.invertibleOfIsUnitDet (A b) hdetb
    refine ⟨Matrix.toLinearEquiv' (A b) this, fun x => ?_⟩
    simp only [hcy, perC_apply]
    rw [hrep b hb.1 x, realMap_apply]
    show A b *ᵥ P₀ x + Bm b *ᵥ star (P₀ x) = A b *ᵥ (P₀ x + ((A b)⁻¹ * Bm b) *ᵥ star (P₀ x))
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ _ hdetb]

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPerNear
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.PerCoordU GlobalTheory.PeriodCoord

namespace UpperTheory.Gal.W2

theorem perNear_of : PerNear := by
  intro O _ bar g ρ D P₀ M₀ hP hM d co hco
  obtain ⟨hHerm, hPos, hIm⟩ := hM
  have hdet : M₀.det ≠ 0 := det_ne_zero_of_pos hPos
  obtain ⟨t, ht, htO, ht0⟩ := eventually_nhds_iff.mp (_root_.GlobalTheory.PosOpen.posopen M₀ hPos)
  have hcont : Continuous co := LinearMap.continuous_of_finiteDimensional co
  refine ⟨co ⁻¹' t, htO.preimage hcont, by simpa using ht0, ?_, ?_⟩
  · intro b hb
    obtain ⟨h1, h2, h3⟩ := ht (co b) hb
    have hT : (co b)ᵀ * M₀ ∈ Tsp bar ρ := hco b
    obtain ⟨hH, hF⟩ := T.riemann_relation_converse_conjAffine M₀ (co b) hHerm hdet hT.1 h1
    have hcomm := comm_of_mem_Tsp hP hIm hdet hT
    refine T.isPeriodMap_comp_injective_realLinear D ρ P₀ (realMap 1 (co b)) (M₀ * (1 - (co b).map star * co b)⁻¹) hP
      (realMap_one_injective h2) ?_ hH h3 ?_
    · intro a x
      simp only [realMap_apply, Matrix.one_mulVec, Matrix.mulVec_add, star_mulVec_map,
        Matrix.mulVec_mulVec, hcomm a]
      rw [Matrix.one_mul]
    · intro x y
      simp only [realMap_apply, Matrix.one_mulVec]
      rw [hF, hIm]
  · intro x
    set v := star (P₀ x)
    let f : (Fin d → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
      { toFun := fun b => co b *ᵥ v
        map_add' := by intro a b; simp [Matrix.add_mulVec]
        map_smul' := by intro c b; simp [Matrix.smul_mulVec] }
    have hf : Differentiable ℂ (fun b => co b *ᵥ v) :=
      (LinearMap.toContinuousLinearMap f).differentiable
    have : (fun b => (perC P₀ (co b)) x) = fun b => P₀ x + co b *ᵥ v := by
      funext b; simp [perC_apply, v]
    rw [this]
    exact ((differentiable_const _).add hf).differentiableOn

end UpperTheory.Gal.W2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem pow_map_ext {X : Scheme.{0}} {A : Over X} {k : ℕ} {T : Scheme.{0}}
    (a b : T ⟶ (GlobalTheory.KS.pow A k).left) (h0 : a ≫ (GlobalTheory.KS.pow A k).hom = b ≫ (GlobalTheory.KS.pow A k).hom)
    (h : ∀ j, a ≫ (GlobalTheory.KS.pr A j).left = b ≫ (GlobalTheory.KS.pr A j).left) : a = b := by
  let Y : Over X := Over.mk (a ≫ (GlobalTheory.KS.pow A k).hom)
  let fa : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk a rfl
  let fb : Y ⟶ GlobalTheory.KS.pow A k := Over.homMk b h0.symm
  have hab : fa = fb := by
    unfold GlobalTheory.KS.pow at fa fb ⊢
    apply Limits.Pi.hom_ext
    intro j
    ext
    simp only [Over.comp_left, Over.homMk_left, fa, fb]
    exact h j
  exact congrArg (fun f => f.left) hab

section
variable {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ} {D : PLat O bar}
  {X : Scheme.{0}} {s : X ⟶ Sp ℂ} {A : Over X} [GrpObj A] (S : Sheet s A D ρ) (k : ℕ)

private theorem pt_hom (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) :
    S.pt k P z ≫ (GlobalTheory.KS.pow A k).hom = S.u P :=
  Over.w (Pi.lift (fun j => S.ex P (z j)) : Over.mk (S.u P) ⟶ GlobalTheory.KS.pow A k)

private theorem pt_pr (P : D.La →+ (Fin g → ℂ)) (z : Fin k → Fin g → ℂ) (j : Fin k) :
    S.pt k P z ≫ (GlobalTheory.KS.pr A j).left = (S.ex P (z j)).left := by
  unfold Sheet.pt GlobalTheory.KS.pr
  rw [← Over.comp_left]
  exact congrArg Over.Hom.left (Limits.Pi.lift_comp_π _ j)

private theorem ex_sub (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ρ P) (a b : Fin g → ℂ) :
    S.ex P a = S.ex P (a - b) * S.ex P b := by
  have h := S.exp P hP
  unfold IsExp at h
  have e := h.1 (a - b) b
  rwa [sub_add_cancel] at e

end

theorem UpperTheory.Gal.W2.ptFibre_of :
    UpperTheory.Gal.W2.PtFibre := by
  intro O _ bar g ρ D X s A _ S k P hP
  have hE := S.exp P hP
  unfold IsExp at hE
  have hu : ∀ (P' : D.La →+ (Fin g → ℂ)) (w : Fin g → ℂ), (S.ex P' w).left ≫ A.hom = S.u P' :=
    fun P' w => Over.w (S.ex P' w)
  refine ⟨fun z => pt_hom S k P z, fun z j => pt_pr S k P z j, ?_, ?_, ?_⟩
  · intro y hy
    have hc : ∀ j : Fin k, ∃ w, S.ex P w =
        Over.homMk (U := Over.mk (S.u P)) (V := A) (y ≫ (GlobalTheory.KS.pr A j).left) (by
          show _ = S.u P
          rw [Category.assoc, Over.w]
          exact hy) := fun j => hE.2.1 _
    choose z hz using hc
    refine ⟨z, pow_map_ext _ _ ?_ ?_⟩
    · rw [hy, pt_hom]
    · intro j
      rw [pt_pr, hz j]
      rfl
  · intro z z'
    constructor
    · intro heq j
      have e1 : (S.ex P (z j)).left = (S.ex P (z' j)).left := by
        rw [← pt_pr S k P z j, ← pt_pr S k P z' j, heq]
      have e2 : S.ex P (z j) = S.ex P (z' j) := Over.OverMorphism.ext e1
      have e3 : S.ex P (z j - z' j) = 1 := by
        have e4 := ex_sub S P hP (z j) (z' j)
        rw [e2] at e4
        exact mul_eq_right.mp e4.symm
      exact (S.ker P hP _).mp e3
    · intro hr
      apply pow_map_ext
      · rw [pt_hom, pt_hom]
      · intro j
        rw [pt_pr, pt_pr, ex_sub S P hP (z j) (z' j), (S.ker P hP _).mpr (hr j), _root_.one_mul]
  · intro P' h hP' hx z
    have hu' : S.u P' = S.u P := by
      calc S.u P' = (S.ex P' (h 0)).left ≫ A.hom := (hu P' (h 0)).symm
        _ = (S.ex P 0).left ≫ A.hom := by rw [S.lin P P' h hP hP' hx 0]
        _ = S.u P := hu P 0
    apply pow_map_ext
    · rw [pt_hom, pt_hom, hu']
    · intro j
      rw [pt_pr, pt_pr]
      exact S.lin P P' h hP hP' hx (z j)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtHol
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.ptHol_of :
    UpperTheory.Gal.W2.HolPi → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.PtHol := by
  intro hHP hPF O _ bar g ρ D X s A _ S k m B P hB hP
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hS := S.hol m B P hB hP
  refine hHP ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X A k (B ×ˢ Set.univ)
    (fun bz => S.pt k (P bz.1) bz.2) hBU ?_ ?_
  · have hu : IsHolTo (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) (fun bz => S.u (P bz.1)) :=
      GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.1 hBU differentiableOn_fst
        (fun bz hbz => hbz.1)
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr hu ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
  · intro j
    let φ : (Fin m → ℂ) × (Fin k → Fin g → ℂ) → (Fin m → ℂ) × (Fin g → ℂ) :=
      fun bz => (bz.1, bz.2 j)
    have hφ : Differentiable ℂ φ := by
      fun_prop
    have hmaps : Set.MapsTo φ (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)))
        (B ×ˢ (Set.univ : Set (Fin g → ℂ))) :=
      fun bz hbz => ⟨hbz.1, Set.mem_univ _⟩
    have he := GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_precomp hS.2 hBU hφ.differentiableOn hmaps
    refine GlobalTheory.CompanionTheory.Ar.Flat.ExpLoc.isHolTo_congr he ?_
    intro bz hbz
    exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPtImm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem flat_of_eventuallyEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}}
    {s s' : V → (Sp ℂ ⟶ Y)} {v₀ w : V} (h : s =ᶠ[𝓝 v₀] s') (hf : Flat s v₀ w) : Flat s' v₀ w := by
  intro U f hU
  have h0 : s v₀ = s' v₀ := h.eq_of_nhds
  have hfd : fderiv ℂ (fun v => valAt' (s' v) U f) v₀ = fderiv ℂ (fun v => valAt' (s v) U f) v₀ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h] with v hv
    rw [hv]
  rw [hfd]
  exact hf U f (h0 ▸ hU)

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.W2.ptImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.ExpImm → UpperTheory.Gal.W2.PtImm := by
  intro hComp hPre hPF hExp O _ bar g ρ D X s A _ S k m B P b₀ hB hb₀ hP hu z₀ w hw
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hmem : (b₀, z₀) ∈ B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) := ⟨hb₀, Set.mem_univ _⟩
  have hnhds : B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) ∈ 𝓝 (b₀, z₀) := hBU.mem_nhds hmem
  have hS := S.hol m B P hB hP
  have hw1 : w.1 = 0 := by
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left X (KS.pow A k).hom
      (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.u (P bz.1)) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
    have hfst : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => bz.1)
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)) (b₀, z₀) := hasFDerivAt_fst
    have h3 : Flat (fun b => S.u (P b)) b₀
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ) w) :=
      (hPre (Fin m → ℂ) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X B (fun b => S.u (P b)) hS.1
        (fun bz => bz.1) (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ))
        (b₀, z₀) w hfst hb₀).mp h2
    exact hu _ h3
  have hw2 : ∀ j, w.2 j = 0 := by
    intro j
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left A.left
      (Over.Hom.left (KS.pr A j)) (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) =>
        Over.Hom.left (S.ex (P bz.1) (bz.2 j))) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
    let L : (Fin m → ℂ) × (Fin k → Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
      (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)).prod
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Fin g → ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)))
    have hL : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => (bz.1, bz.2 j)) L (b₀, z₀) :=
      L.hasFDerivAt
    have hmem2 : ((b₀, z₀).1, (b₀, z₀).2 j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h3 : Flat (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => Over.Hom.left (S.ex (P bz.1) bz.2))
        (b₀, z₀ j) (L w) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun bz => (bz.1, bz.2 j)) L (b₀, z₀) w hL hmem2).mp h2
    have hLw : L w = (0, w.2 j) := by
      simp [L, hw1]
    rw [hLw] at h3
    have hι : HasFDerivAt (fun z : Fin g → ℂ => (b₀, z))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) (z₀ j) :=
      (hasFDerivAt_const b₀ (z₀ j)).prodMk (hasFDerivAt_id (z₀ j))
    have hmem3 : (fun z : Fin g → ℂ => (b₀, z)) (z₀ j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h4 : Flat (fun z : Fin g → ℂ => Over.Hom.left (S.ex (P b₀) z)) (z₀ j) (w.2 j) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) (Fin g → ℂ) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun z => (b₀, z)) (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ))
        (z₀ j) (w.2 j) hι hmem3).mpr h3
    exact hExp X A g (S.u (P b₀)) (S.ex (P b₀)) (S.exp _ (hP.1 _ hb₀)) (z₀ j) (w.2 j) h4
  exact Prod.ext hw1 (_root_.funext hw2)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PTanChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.tanChart_of :
    UpperTheory.Gal.W2.TanDeriv → UpperTheory.Gal.W2.FlatAffine → UpperTheory.Gal.W2.ConjCharpoly → UpperTheory.Gal.W2.TanChart := by
  intro hTD hFA hCC E _ _ _ d hd Z Y sZ s' c₁ c₂ h₁ h₂ B s v₀ hB hv hs hs' hflat G G' hG hGv hev y hy0 A hT
  obtain ⟨U, W, hW1, hW2, t, hy, hU, hW, φ, hφ1, hφ2, hφ3, hφ4⟩ := hT
  obtain ⟨ψ, hψ1, hψ2⟩ := hTD E Y s' B s v₀ hB hv hs hs' y hy0 W hy
  let e₁ : Fin d → Sec s' W := fun l => Sec.res s' hW1 (appSec sZ s' c₁ U (t l))
  let e₂ : Fin d → Sec s' W := fun l => Sec.res s' hW2 (appSec sZ s' c₂ U (t l))
  have hφ2' : ∀ l, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) = Pi.single l 1 := hφ2
  have hφ3' : ∀ j, φ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) = fun l => A j l := hφ3
  let N : Set E := {v | v ∈ B ∧ ⊤ ≤ s v ⁻¹ᵁ W}
  have hNo : IsOpen N := (hs W 0).1
  have hv₀N : v₀ ∈ N := by
    refine ⟨hv, ?_⟩
    have := hy
    simp only [CxPts.ptsIn, Set.mem_setOf_eq] at this
    rw [hy0] at this
    exact this
  have hNn : N ∈ 𝓝 v₀ := hNo.mem_nhds hv₀N
  have hK : ∀ ω, ψ ω = ∑ l, (φ ω) l • ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) := by
    intro ω
    set ω' := ω - ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) with hω'
    have hφω' : φ ω' = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hω', map_sub, map_sum]
      simp only [map_smul, hφ2']
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    obtain ⟨m, b, ω'', hb0, hωeq⟩ := hφ4 ω' hφω'
    have hψω' : ψ ω' = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hωeq, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [hψ1, hb0 i, zero_smul]
    have hω : ω = ω' + ∑ l, (φ ω) l • KaehlerDifferential.D ℂ (Sec s' W) (e₁ l) := by
      rw [hω']
      abel
    conv_lhs => rw [hω]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), hψω', zero_add, map_sum]
    simp only [map_smul]
  let τ : E →ₗ[ℂ] Fin d → ℂ :=
    LinearMap.pi (fun l => ((ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) : E →L[ℂ] ℂ) : E →ₗ[ℂ] ℂ))
  have hτ : ∀ w l, τ w l = ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₁ l)) w := fun w l => rfl
  have hinj : Function.Injective τ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    apply hflat
    refine hFA E Y B s v₀ w hB hv hs W hW hv₀N.2 (fun f => ?_)
    have hf : fderiv ℂ (fun v => valAt' (s v) W f) v₀ = ψ (KaehlerDifferential.D ℂ (Sec s' W) f) :=
      (hψ2 f).symm
    rw [hf, hK, ContinuousLinearMap.sum_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    rw [ContinuousLinearMap.smul_apply, ← hτ, hw]
    simp
  have hval : ∀ (c : Y ⟶ Z) (hc : W ≤ c ⁻¹ᵁ U) (f : Sec sZ U) (v : E), ⊤ ≤ s v ⁻¹ᵁ W →
      valAt' (s v) W (Sec.res s' hc (appSec sZ s' c U f)) = valAt' (s v ≫ c) U f := by
    intro c hc f v hvW
    exact (valAt'_res (s v) hc _ hvW).trans (valAt'_comp (s v) c U f)
  have hrel : ∀ w, τ (G' w) = A *ᵥ τ w := by
    intro w
    funext j
    have hd1 : DifferentiableAt ℂ (fun v => valAt' (s v) W (e₁ j)) v₀ :=
      ((hs W (e₁ j)).2).differentiableAt hNn
    have hGN : ∀ᶠ v in 𝓝 v₀, G v ∈ N := by
      have hNn' : N ∈ 𝓝 (G v₀) := by rw [hGv]; exact hNn
      exact hG.continuousAt.preimage_mem_nhds hNn'
    have heq : (fun v => valAt' (s v) W (e₂ j)) =ᶠ[𝓝 v₀]
        (fun v => valAt' (s v) W (e₁ j)) ∘ G := by
      filter_upwards [hNn, hGN, hev] with v hvN hGvN hevv
      simp only [Function.comp_apply]
      rw [hval c₂ hW2 (t j) v hvN.2, hval c₁ hW1 (t j) (G v) hGvN.2, hevv]
    have hd1' : HasFDerivAt (fun v => valAt' (s v) W (e₁ j))
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀) (G v₀) := by
      rw [hGv]; exact hd1.hasFDerivAt
    have hcomp := hd1'.comp v₀ hG
    have hfd : fderiv ℂ (fun v => valAt' (s v) W (e₂ j)) v₀ =
        (fderiv ℂ (fun v => valAt' (s v) W (e₁ j)) v₀).comp G' := by
      rw [heq.fderiv_eq]
      exact hcomp.fderiv
    have h2 : ψ (KaehlerDifferential.D ℂ (Sec s' W) (e₂ j)) w = ∑ l, A j l * τ w l := by
      rw [hK, hφ3', ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hτ]
    rw [Matrix.mulVec, dotProduct, ← h2, hψ2, hfd, hτ, hψ2]
    rfl
  exact hCC E d hd τ (G' : E →ₗ[ℂ] E) A hinj hrel
end

