module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0774
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerRealizeEqZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

noncomputable section

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]

theorem gram_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (v : InfinitePlace K) : N v.embedding 0 = 0 := by
  rw [← (hG v).2 0]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.fcoord_zero]

theorem inner_realize_eq_zero [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {x y : V}
    (h : ∀ v : InfinitePlace K, N v.embedding (x + y) ^ 2 = N v.embedding x ^ 2 + N v.embedding y ^ 2) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  have hs : ∀ z, ‖Formalism.HermitianLatticesTheory.realize b X z‖ ^ 2 = ∑ v : InfinitePlace K, N v.embedding z ^ 2 := fun z => by
    rw [GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2]
  have h1 := hs (x + y)
  rw [map_add (f := _), norm_add_sq_real, hs x, hs y] at h1
  rw [Finset.sum_congr rfl fun v _ => h v, Finset.sum_add_distrib] at h1
  linarith

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem inner_pair [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2)
    {i j : ι} (hij : i ≠ j) {x y : V} (hx : x ∈ M i) (hy : y ∈ M j) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  refine inner_realize_eq_zero hG fun v => ?_
  have hmem : ∀ (k : ι) (z : V) (_ : z ∈ M k) (l : ι),
      (Pi.single k z : ι → V) l ∈ Submodule.span K (M l : Set V) := by
    intro k z hz l
    by_cases hl : l = k
    · subst hl; simpa using Submodule.subset_span hz
    · simp [Pi.single_apply, hl]
  have h := hN v.embedding (Pi.single i x + Pi.single j y) fun l =>
    Submodule.add_mem _ (hmem i x hx l) (hmem j y hy l)
  have hsum : ∑ l, (Pi.single i x + Pi.single j y : ι → V) l = x + y := by
    simp [Finset.sum_add_distrib]
  have hpt : ∀ l, N v.embedding ((Pi.single i x + Pi.single j y : ι → V) l) ^ 2 =
      (Pi.single i (N v.embedding x ^ 2) : ι → ℝ) l + (Pi.single j (N v.embedding y ^ 2) : ι → ℝ) l := by
    intro l
    by_cases hli : l = i
    · subst hli; simp [Pi.single_apply, hij]
    · by_cases hlj : l = j
      · subst hlj; simp [Pi.single_apply, hli]
      · simp [Pi.single_apply, hli, hlj, gram_zero hG v]
  rw [hsum, Finset.sum_congr rfl fun l _ => hpt l, Finset.sum_add_distrib] at h
  simpa using h

theorem deg_eq [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    GlobalTheory.AllWt.deg N L = 1 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * ((-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) / 2) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  rw [GlobalTheory.AllWt.deg, GlobalTheory.AllWt.slope, GlobalTheory.AllWt.slope_sq_eq hG hL]
  by_cases h0 : L = ⊥
  · subst h0
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V (Fin n) b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring

end GlobalTheory.OrthRankDeg

namespace GlobalTheory.OrthRankDeg

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem sum_finset [_root_.NumberField.IsTotallyComplex K] [StarRing K] {n : ℕ} {b : Module.Basis (Fin n) K V}
    {X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ} {N : (K →+* ℂ) → V → ℝ}
    (hG : GlobalTheory.AllWt.IsGram b X N) {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → Submodule (𝓞 K) V)
    (hM : ∀ i, (M i).FG)
    (hN : ∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) →
      N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) (s : Finset ι) :
    (⨆ i ∈ s, M i).FG ∧ Formalism.HN.rkK (⨆ i ∈ s, M i) = ∑ i ∈ s, Formalism.HN.rkK (M i) ∧
      Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⨆ i ∈ s, M i) =
        ∑ i ∈ s, Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (M i) := by
  have hX : ∀ v, IsUnit (X v).det := fun v => (hG v).1
  induction s using Finset.induction_on with
  | empty =>
    simp [Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot b X hX, Submodule.fg_bot]
  | insert a s ha ih =>
    obtain ⟨ihfg, ihrk, ihdeg⟩ := ih
    rw [Finset.iSup_insert]
    set B := ⨆ i ∈ s, M i with hB
    have ho : ∀ x ∈ M a, ∀ y ∈ B,
        inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
      intro x hx y hy
      obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum M y).1 hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hμ, map_sum, inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact inner_pair hG M hN (by rintro rfl; exact ha hi) hx (μ i).2
    have hlA := (Formalism.HN.plLat K V (Fin n) b X hX (M a) (hM a)).1
    have hlB := (Formalism.HN.plLat K V (Fin n) b X hX B ihfg).1
    obtain ⟨hl, hdeg, -⟩ :=
      (Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 (M a) B hlA hlB ho
    have hfg : (M a ⊔ B).FG := (hM a).sup ihfg
    have hinf : M a ⊓ B = ⊥ := by
      refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
      have h1 := ho x hx.1 x hx.2
      rw [inner_self_eq_zero] at h1
      exact Formalism.HN.HeightGram.realize_injective b X hX (by rw [h1, map_zero])
    have hrk := (Formalism.HN.degSupermod (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) (M a ⊔ B) (M a) B hl
      le_sup_left le_sup_right).1
    rw [hinf, (Formalism.HN.plLat K V (Fin n) b X hX _ hfg).2.1, (Formalism.HN.plLat K V (Fin n) b X hX _ (hM a)).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ ihfg).2.1,
      (Formalism.HN.plLat K V (Fin n) b X hX _ Submodule.fg_bot).2.1, Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_bot, mul_zero, add_zero,
      ← mul_add] at hrk
    have hrk' := Nat.eq_of_mul_eq_mul_left (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.finrank_pos' (K := K)) hrk
    refine ⟨hfg, ?_, ?_⟩
    · rw [hrk', Finset.sum_insert ha, ihrk]
    · rw [hdeg, Finset.sum_insert ha, ihdeg]

theorem rkK_deg_iSup : ∀ (K V : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (ι : Type) [Fintype ι] (N : (K →+* ℂ) → V → ℝ)
    (M : ι → Submodule (𝓞 K) V), HasGram N → (∀ i, (M i).FG) →
    (∀ σ, ∀ f : ι → V, (∀ i, f i ∈ Submodule.span K (M i : Set V)) → N σ (∑ i, f i) ^ 2 = ∑ i, N σ (f i) ^ 2) →
    Formalism.HN.rkK (⨆ i, M i) = ∑ i, Formalism.HN.rkK (M i) ∧ deg N (⨆ i, M i) = ∑ i, deg N (M i) := by
  intro K V _ _ _ _ _ _ _ ι _ N M hG hM hN
  classical
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨⟨b, X⟩, hbX⟩⟩⟩ := hG
  obtain ⟨hfg, hrk, hdeg⟩ := sum_finset hbX M hM hN Finset.univ
  have hu : (⨆ i ∈ (Finset.univ : Finset ι), M i) = ⨆ i, M i := by simp
  rw [hu] at hfg hrk hdeg
  refine ⟨hrk, ?_⟩
  rw [deg_eq hbX _ hfg, hdeg, hrk, Finset.mul_sum]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (deg_eq hbX _ (hM i)).symm

end GlobalTheory.OrthRankDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenRowVectorOrbitCompactOpenGL
section
noncomputable section

open Matrix Topology

namespace GlobalTheory.JSW.Orbit

theorem isClopen_orbit : ∀ {F : Type} [NormedField F] {n : ℕ} (B : Subgroup (GL (Fin n) F)),
    IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B : Set (GL (Fin n) F)) → ∀ r₀ : Fin n → F, r₀ ≠ 0 →
    IsClopen {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} := by
  intro F _ n B hBc hBo r₀ hr₀
  classical
  have hset : {r : Fin n → F | ∃ b ∈ B, r = r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)} =
      (fun b : GL (Fin n) F => r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F)) '' (B : Set (GL (Fin n) F)) := by
    ext r
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact (hBc.image (continuous_const.matrix_vecMul Units.continuous_val)).isClosed
  · rw [isOpen_iff_mem_nhds]
    rintro _ ⟨b, hb, rfl⟩
    set r := r₀ ᵥ* (b : Matrix (Fin n) (Fin n) F) with hr
    have hr0 : r ≠ 0 := by
      intro h
      apply hr₀
      have : r ᵥ* ((b⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = r₀ := by
        rw [hr, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one]
      rw [← this, h, zero_vecMul]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hr0
    let c : Fin n → F := Pi.single i (r i)⁻¹
    have hc : r ⬝ᵥ c = 1 := by
      simp only [c, dotProduct_single]
      exact mul_inv_cancel₀ hi
    obtain ⟨O, hO, hOB⟩ := GlobalTheory.JSW.KirFin.isEmbedding_coe.isInducing.isOpen_iff.1 hBo
    let s : (Fin n → F) → Matrix (Fin n) (Fin n) F := fun y => 1 + vecMulVec c (y - r)
    have hs : Continuous s :=
      continuous_const.add (continuous_const.matrix_vecMulVec (continuous_id.sub continuous_const))
    have hs1 : s r = 1 := by simp [s]
    have h1O : (1 : Matrix (Fin n) (Fin n) F) ∈ O := by
      have : (1 : GL (Fin n) F) ∈ (B : Set (GL (Fin n) F)) := B.one_mem
      rw [← hOB] at this
      exact this
    have e1 : ∀ᶠ y in 𝓝 r, s y ∈ O := hs.continuousAt.eventually_mem (hO.mem_nhds (by rw [hs1]; exact h1O))
    have e2 : ∀ᶠ y in 𝓝 r, (s y).det ≠ 0 := hs.matrix_det.continuousAt.eventually_ne (by simp [hs1])
    filter_upwards [e1, e2] with y hy1 hy2
    let u : GL (Fin n) F := GeneralLinearGroup.mkOfDetNeZero _ hy2
    have hu : u ∈ B := by
      have : u ∈ (fun g : GL (Fin n) F => g.val) ⁻¹' O := hy1
      rw [hOB] at this
      exact this
    refine ⟨b * u, B.mul_mem hb hu, ?_⟩
    change y = r₀ ᵥ* ((b : Matrix (Fin n) (Fin n) F) * s y)
    rw [← vecMul_vecMul, ← hr]
    change y = r ᵥ* (1 + vecMulVec c (y - r))
    rw [vecMul_add, vecMul_one, vecMul_vecMulVec, hc]
    simp

end GlobalTheory.JSW.Orbit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactCharAnnihilatorOfMemNhdsZero
section
open Matrix Topology

namespace GlobalTheory.JSW

theorem isCompact_charAnnihilator_of_mem_nhds_zero {F : Type} [NormedField F] [ProperSpace F] (ψ : AddChar F ℂ)
    (hlc : IsLocallyConstant ψ) (hψ : ψ ≠ 1) {ι : Type} [Fintype ι] (L : Set (ι → F))
    (hL : L ∈ nhds (0 : ι → F)) :
    IsCompact {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
  classical
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.1 hψ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hL
  have hcont : Continuous (fun x : F => ψ x) := hlc.continuous
  have hclosed : IsClosed {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} := by
    have : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} = ⋂ y ∈ L, {r : ι → F | ψ (r ⬝ᵥ y) = 1} := by
      ext r; simp
    rw [this]
    refine isClosed_biInter fun y _ => isClosed_eq ?_ continuous_const
    refine hcont.comp ?_
    simp only [dotProduct]
    fun_prop
  have hR : 0 ≤ ‖t‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hsub : {r : ι → F | ∀ y ∈ L, ψ (r ⬝ᵥ y) = 1} ⊆ Metric.closedBall 0 (‖t‖ / ε) := by
    intro r hr
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
    intro i
    by_contra hlt
    push_neg at hlt
    have hri : r i ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hlt; linarith
    have hpos : 0 < ‖r i‖ := norm_pos_iff.2 hri
    have hy : Pi.single i (t / r i) ∈ L := by
      apply hball
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [Pi.single_eq_same, norm_div, div_lt_iff₀ hpos]
        rw [div_lt_iff₀ hε] at hlt
        linarith
      · rw [Pi.single_eq_of_ne hj, norm_zero]; exact hε
    have := hr _ hy
    rw [dotProduct_single, mul_div_cancel₀ _ hri] at this
    exact ht this
  exact (isCompact_closedBall 0 (‖t‖ / ε)).of_isClosed_subset hclosed hsub

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestHomMatrixOfProportionalGeneratingCombinati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixCond

theorem unit_of_proportional {X : Scheme.{0}} {V : X.Opens} {m : ℕ} (B C : Fin m → Γ(X, V))
    (hC : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (C j)))
    (hB : ∀ x ∈ V, ∃ j, IsUnit (gs (𝟙 X) x V (B j)))
    (hP : ∀ x ∈ V, ∀ j j', gs (𝟙 X) x V (B j) * gs (𝟙 X) x V (C j') =
      gs (𝟙 X) x V (B j') * gs (𝟙 X) x V (C j)) :
    ∃ u : Γ(X, V)ˣ, ∀ j, B j = u.val * C j := by
  let W : Fin m → X.Opens := fun j => X.basicOpen (C j)
  have lW : ∀ j, W j ≤ V := fun j => X.basicOpen_le _
  have uC : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (C j)) := fun j y hy =>
    (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V (lW j hy) (C j)).2 hy
  have uB : ∀ j, ∀ y ∈ W j, IsUnit (gs (𝟙 X) y V (B j)) := fun j y hy => by
    obtain ⟨j', hj'⟩ := hB y (lW j hy)
    have e := hP y (lW j hy) j' j
    have h2 := hj'.mul (uC j y hy)
    rw [e] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hu : ∀ j, IsUnit (resG X (lW j) (C j)) := fun j =>
    X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      have := uC j y hy
      rw [← gs_res (𝟙 X) y (lW j) hy, gs_eq _ y _ hy] at this
      exact this
  let w : ∀ j, Γ(X, W j) := fun j => resG X (lW j) (B j) * ((hu j).unit⁻¹).val
  have hw : ∀ j, ∀ y ∈ W j, gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C j) = gs (𝟙 X) y V (B j) := fun j y hy => by
    rw [← gs_res (𝟙 X) y (lW j) hy (C j), ← gs_mul _ y _ hy, _root_.mul_assoc]
    show gs (𝟙 X) y (W j) (resG X (lW j) (B j) * (((hu j).unit⁻¹).val * (hu j).unit.val)) = _
    rw [Units.inv_mul, _root_.mul_one, gs_res _ y _ hy]
  have wu : ∀ j, IsUnit (w j) := fun j => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have e := hw j y hy
    have h1 : IsUnit (gs (𝟙 X) y (W j) (w j)) := by
      have := uB j y hy
      rw [← e] at this
      exact isUnit_of_mul_isUnit_left this
    rw [gs_eq _ y _ hy] at h1
    exact h1
  obtain ⟨s, hs⟩ := glue_unit V W lW (fun y hy => by
      obtain ⟨j, hj⟩ := hC y hy
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C j)).1 hj⟩)
    (fun j => (wu j).unit) (fun i j y hy => by
      apply Units.ext
      rw [← gs_unit _ y _ hy.1, ← gs_unit _ y _ hy.2]
      refine (uC i y hy.1).mul_right_cancel ?_
      refine (uC j y hy.2).mul_right_cancel ?_
      show gs (𝟙 X) y (W i) (w i) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j) =
        gs (𝟙 X) y (W j) (w j) * gs (𝟙 X) y V (C i) * gs (𝟙 X) y V (C j)
      rw [hw i y hy.1, mul_right_comm, hw j y hy.2, hP y (lW i hy.1) i j])
  refine ⟨s, fun j => fn_ext fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := hC y hy
  have yi : y ∈ W i := (GlobalTheory.LBGerm.isUnit_gs_iff (𝟙 X) y V hy (C i)).1 hi
  have es : gs (𝟙 X) y V s.val = gs (𝟙 X) y (W i) (w i) := by
    rw [← gs_res (𝟙 X) y (lW i) yi]
    exact congrArg (fun q : Γ(X, W i)ˣ => gs (𝟙 X) y (W i) q.val) (hs i)
  rw [gs_mul _ y _ hy, es]
  refine hi.mul_right_cancel ?_
  rw [mul_right_comm, hw i y yi, hP y hy i j]

theorem gs_finsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem isMat_of_conditions : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c : Fin mA → Fin mB → Γ(Sp R, ⊤)), L.IsLB → M.IsLB → eA.IsGen → eB.IsGen → (⨆ j, nonzeroLocus (bB j)) = ⊤ → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsTest A B L M t A' B' φA' φB' Φ' → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom (Φ'.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B) c → GlobalTheory.HomFixUniv.Normal t c αA βB → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB R _ t A' B' _ _ φA' φB' Φ' c hL hM heA heB hcov hvA hvB hT hgen
    hprop hnorm
  have key : ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ∃ u : Γ(A'.left, (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)ˣ, ∀ j : Fin mB,
        ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        u.val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p) (by simp)).hom
          (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro p
    set V := (isoLB (L := L) (M := M) k Φ' (φA' ≫ θ A) (φB' ≫ θ B)).U p with hV
    have mB' : ∀ z ∈ V, (Φ'.left ≫ φB' ≫ θ B) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hz.1
    have mA' : ∀ z ∈ V, (φA' ≫ θ A) z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
      fun z hz => GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hz.2
    have gB : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V
        (((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1)) =
        gs (Φ'.left ≫ φB' ≫ θ B) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) :=
      fun z hz j => (gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp])
    have gC : ∀ z ∈ V, ∀ j : Fin mB, gs (𝟙 A'.left) z V (∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) =
        comb bA (φA' ≫ θ A) A'.hom c z p.2 j := fun z hz j => by
      rw [gs_finsum _ z _ hz]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [gs_mul _ z _ hz]
      refine congrArg₂ (· * ·) ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]))
        ((gs_appLE _ _ _ _ (𝟙 A'.left) z hz _).trans (by rw [Category.id_comp]; rfl))
    obtain ⟨u, hu⟩ := unit_of_proportional (V := V)
      (fun j => ((Φ'.left ≫ φB' ≫ θ B).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) V
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1))
      (fun j => ∑ i, (A'.hom.appLE ⊤ V (by simp)).hom (c i j) *
          ((φA' ≫ θ A).appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) V
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2))
      (fun z hz => by
        obtain ⟨j, hj⟩ := hgen z p.2 (mA' z hz)
        exact ⟨j, by rw [gC z hz j]; exact hj⟩)
      (fun z hz => by
        obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge (Set.mem_univ ((Φ'.left ≫ φB' ≫ θ B) z)))
        exact ⟨j, by rw [gB z hz j]; exact (GlobalTheory.mem_nonzeroLocus_iff_pull (bB j) _ z (mB' z hz)).1 hj⟩)
      (fun z hz j j' => by
        rw [gB z hz j, gB z hz j', gC z hz j, gC z hz j']
        exact hprop z p.2 p.1 (mA' z hz) (mB' z hz) j j')
    exact ⟨u, hu⟩
  choose u hu using key
  refine ⟨φA' ≫ θ A, φB' ≫ θ B, ⟨u⟩, by rw [Category.assoc, θ_snd, Category.comp_id],
    by rw [Category.assoc, θ_snd, Category.comp_id], ?_, ?_, fun j p => hu p j⟩
  · exact GlobalTheory.T.isGenerator_isoBundle_of_matrix_relation Rg A B L M k mA mB bA bB R A' B' Φ' (φA' ≫ θ A) (φB' ≫ θ B) c u hgen (fun j p => hu p j)
  · exact GlobalTheory.T.isoNormalisation_at_zeroSection Rg A B L M k mA mB bA bB eA eB αA βB R t A' B' φA' φB' Φ' c u hcov hvA hvB hT hnorm
      (fun j p => hu p j)

end GlobalTheory.HomFixCond
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogMetricGeneratorEqMeanPeriod
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.MeanPeriodGenerator

theorem ellT_eq_span (D : D7) (cD : D.what₂.Tau → ℂ) (h : IsDgen D cD)
    (M : IntermediateField ℚ ℂ) [NumberField M] (hM : ∀ τ x, TaylorLogMetric.embT D τ x ∈ M)
    (τ : D.what₂.Tau) (hc : cD τ ∈ M) :
    TaylorLogMetric.ellT D M τ = Submodule.span (𝓞 M) {(⟨cD τ, hc⟩ : M)} := by
  obtain ⟨M₀, _, hM₀, hs⟩ := h
  obtain ⟨s, hsc, hs⟩ := hs τ
  have hs0 : s ≠ 0 := GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm
  have hc0 : cD τ ≠ 0 := fun h => hs0 (Subtype.ext (hsc.trans h))
  haveI : NumberField (M ⊔ M₀ : IntermediateField ℚ ℂ) := NumberField.mk
  have hM' : ∀ τ x, TaylorLogMetric.embT D τ x ∈ (M ⊔ M₀ : IntermediateField ℚ ℂ) :=
    fun τ x => (le_sup_left : M ≤ M ⊔ M₀) (hM τ x)
  have h' := GlobalTheory.EigenlineBaseChange.ellT_eq_span_of_le D M₀ (M ⊔ M₀) le_sup_right hM₀ τ s hs
  apply le_antisymm
  · intro x hx
    have hx' : (⟨(x : ℂ), (le_sup_left : M ≤ M ⊔ M₀) x.2⟩ : (M ⊔ M₀ : IntermediateField ℚ ℂ)) ∈
        TaylorLogMetric.ellT D (M ⊔ M₀) τ := by
      rw [GlobalTheory.Glob.mem_ellT_iff hM']
      exact (GlobalTheory.Glob.mem_ellT_iff hM τ x).1 hx
    rw [h', Submodule.mem_span_singleton] at hx'
    obtain ⟨c, hcx⟩ := hx'
    have e : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) * (s : ℂ) = (x : ℂ) :=
      congrArg (fun a : (M ⊔ M₀ : IntermediateField ℚ ℂ) => (a : ℂ)) hcx
    have hi : IsIntegral ℤ ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) :=
      (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).2 c.isIntegral_coe
    have e2 : ((c : (M ⊔ M₀ : IntermediateField ℚ ℂ)) : ℂ) = (x : ℂ) * (cD τ)⁻¹ := by
      rw [← e, hsc, mul_inv_cancel_right₀ hc0]
    rw [e2] at hi
    rw [Submodule.mem_span_singleton]
    refine ⟨⟨x * (⟨cD τ, hc⟩ : M)⁻¹, (GlobalTheory.EigenlineBaseChange.isIntegral_coe_iff _).1 hi⟩, ?_⟩
    exact inv_mul_cancel_right₀ (fun h => hc0 (congrArg (fun a : M => (a : ℂ)) h)) x
  · rw [Submodule.span_singleton_le_iff_mem, GlobalTheory.Glob.mem_ellT_iff hM]
    have := (GlobalTheory.Glob.mem_ellT_iff hM₀ τ s).1 (hs ▸ Submodule.mem_span_singleton_self s)
    rw [hsc] at this
    exact this

theorem mean_logMet_eq : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (cD : D.what₂.Tau → ℂ), StandardLatticesGL3.Crv D cc dl → GlobalTheory.IndefiniteRowSideFullHecke.MeanPeriodLogarithms.MeanPeriodAt D cc dl → IsDgen D cD → (∀ τ, cD τ ≠ 0) ∧ ∀ (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D cc dl) M → (∀ τ, cD τ ∈ M) → ∀ τ, (∑ ρ : M →ₐ[ℚ] ℂ, -TaylorLogMetric.logMet M (TaylorLogMetric.lamOf D cc dl) ρ (TaylorLogMetric.liftM M (cD τ))) / (Module.finrank ℚ M : ℝ) = TaylorLogMetric.logOmVal D := by
  intro D cc dl cD hc hmean hgen
  have hne : ∀ τ, cD τ ≠ 0 := by
    intro τ h
    obtain ⟨M₀, _, hM₀, hs⟩ := hgen
    obtain ⟨s, hsc, hs⟩ := hs τ
    exact GlobalTheory.Glob.ne_zero_of_span_eq hM₀ hs.symm (Subtype.ext (hsc.trans h))
  refine ⟨hne, fun M _ hD hcM τ => ?_⟩
  haveI : NumberField M := NumberField.mk
  have hell := ellT_eq_span D cD hgen M hD.1 τ (hcM τ)
  have hl : TaylorLogMetric.liftM M (cD τ) = ⟨cD τ, hcM τ⟩ := dif_pos (hcM τ)
  rw [hl, ← hmean M hD τ, Finset.sum_neg_distrib]
  exact (GlobalTheory.Glob.meanLogOm_eq_of_gen hD.1 (GlobalTheory.Glob.area_lamConj_pos hc hD) hell.symm).symm

end GlobalTheory.MeanPeriodGenerator
end

