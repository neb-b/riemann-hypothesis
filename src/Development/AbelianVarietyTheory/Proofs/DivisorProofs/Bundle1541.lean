module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors
open GlobalTheory.InertSign

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem exists_nat_mul_mem_one (𝔪 : Ideal (𝓞 D.host.E)) : ∃ M : ℕ, 0 < M ∧ ∀ y : D.host.E,
    y ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) →
    (M : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪
  by_cases h : 𝔫 = ⊥
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have h0 : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
      rw [h]; exact FractionalIdeal.coeIdeal_bot
    rw [h0, div_zero, FractionalIdeal.coe_zero, Submodule.mem_bot] at hy
    rw [hy, mul_zero]; exact Submodule.zero_mem _
  · refine ⟨Ideal.absNorm 𝔫, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
    have hM : ((Ideal.absNorm 𝔫 : ℕ) : D.host.E) ∈ ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨(Ideal.absNorm 𝔫 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔫, by simp⟩
    have hne : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hm := FractionalIdeal.mul_mem_mul hy hM
    rw [div_mul_cancel₀ _ hne] at hm
    have h1 := FractionalIdeal.coeIdeal_le_one (I := 𝔪) (P := D.host.E) hm
    rw [mul_comm]
    rwa [FractionalIdeal.mem_one_iff, ← Submodule.mem_one] at h1

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem skewLat_smul (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d := by
  obtain ⟨M, hM, h⟩ := exists_nat_mul_mem_one (D := D) 𝔪
  refine ⟨M, hM, fun v hv => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro i
  have := h _ (hv i)
  simpa [Pi.smul_apply, Algebra.smul_def] using this

theorem homL_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    homL D (stdL D a) (skewLat D 𝔪 d) ≤ (homL D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun A hA => ?_
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  refine Submodule.subset_span fun x hx => ?_
  have e : ((M : 𝓞 D.host.E) • A).mulVec x = (M : 𝓞 D.host.E) • A.mulVec x := by
    funext i; simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
  rw [e]
  exact hM _ (hA x hx)

theorem YYl_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    YYl D (stdL D a) (skewLat D 𝔪 d) ≤ (YYl D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun B hB => ?_
  obtain ⟨c, hc, A, hA, rfl⟩ := hB
  have hA' := homL_smul (a := a) hM hA
  simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  rw [Nat.cast_smul_eq_nsmul] at hA' ⊢
  rw [smul_comm]
  exact Submodule.subset_span ⟨c, hc, _, hA', rfl⟩

theorem la_skew_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d), M • x ∈ La0 D (tor0 D cc δ) a d := by
  obtain ⟨M, hM0, hM⟩ := skewLat_smul (D := D) 𝔪 d
  refine ⟨M, hM0, fun x hx => ?_⟩
  have key : La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d) ≤
      (La0 D (tor0 D cc δ) a d).comap (DistribSMul.toAddMonoidHom (VC D a d) M) := by
    refine (AddSubgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    have hA' := YYl_smul (a := a) hM hA
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
    refine AddSubgroup.subset_closure ⟨w, hw, _, hA', ?_⟩
    funext τ i j
    simp [embV, tor0, Algebra.smul_def, nsmul_eq_mul]
    ring
  exact key hx

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem sd_stdL (n : ℕ) : SD D (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 _).2

theorem wd_mem_TT_of_nsmul {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {x : VC D a d}
    {M : ℕ} (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) a d) {F : VC D a d → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) a d) : Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) a d := by
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) := Or.inr ⟨_, _, sd_stdL a, sd_stdL d, rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  obtain ⟨hd, m, hm, hF⟩ := hF
  refine ⟨GlobalTheory.ThetaLevels.wd_entire D _ _ hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have hmy := AddSubgroup.nsmul_mem _ hy m
  have h1 : bc D (tor0 D cc δ) ((m * M) • y) x = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_left, ← GlobalTheory.ThetaLevels.bc_nsmul_right]
    exact n0.2.1 _ hmy _ hx
  have h2 : bc D (tor0 D cc δ) x ((m * M) • y) = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_right, ← GlobalTheory.ThetaLevels.bc_nsmul_left]
    exact n0.2.1 _ hx _ hmy
  have h3 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hy M)
  have h4 := Wd_Wd D (tor0 D cc δ) x ((m * M) • y) F
  rw [h3, h2, add_comm] at h4
  rw [Wd_Wd, h1, h4]

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    (B : AddSubgroup (VC D a d)) (hB : ∀ x ∈ B, ∃ M : ℕ, 0 < M ∧ M • x ∈ La0 D (tor0 D cc δ) a d)
    {F : VC D a d → ℂ} (hF : F ∈ TT D (tor0 D cc δ) a d) :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) B F ∈ TT D (tor0 D cc δ) a d := by
  set T := tor0 D cc δ
  set A := La0 D T a d
  by_cases hn : (A.addSubgroupOf B).index = 0
  · have h0 : Iop D T A B F = 0 := by funext z; simp [Iop, hn]
    rw [h0]; exact (GlobalTheory.FinWeil.TTs D T a d).zero_mem
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hn
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    have hI : Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
        ∑ q : B ⧸ A.addSubgroupOf B, (al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) F := by
      funext z
      simp only [Iop, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have h0 : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := Complex.exp_ne_zero _
      simp only [Wd]
      rw [mul_assoc, inv_mul_cancel_left₀ h0]
    rw [hI]
    refine (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ (Submodule.sum_mem _ fun q _ => (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ ?_)
    obtain ⟨M, hM, hx⟩ := hB _ (Quotient.out q : B).2
    exact wd_mem_TT_of_nsmul hc hM hx hF

theorem cosetV_mem_TT : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ →
    ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
      cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ hc 𝔪 _ o a d e0 he
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D (tor0 D ⊤ δ) a d := hT.1 _ _ (sd_stdL a) (sd_stdL d) e0 he
  obtain ⟨M, hM, hx⟩ := la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hI := iop_mem_TT hc (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (fun x hx' => ⟨M, hM, hx x hx'⟩) he'
  exact hT.2.2.2 _ _ (hT.2.1 _ _ hI)

end GlobalTheory.FunObj.CosetTT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BlockHeight

open scoped NNReal
open GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation Formalism.UG

section Generic

variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem htOf_blk_le {R : Type} [CommRing R] {N₁ : Matrix (Fin p) (Fin p) R → ℝ≥0} {N₂ : Matrix (Fin q) (Fin q) R → ℝ≥0}
    {N : Matrix (Fin d) (Fin d) R → ℝ≥0} (hN : ∀ a b, N (blk e a b) ≤ max (N₁ a) (N₂ b))
    (X : GL (Fin d) R) (x : GL (Fin p) R) (y : GL (Fin q) R)
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R))
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    htOf N X ≤ htOf N₁ x * htOf N₂ y := by
  have hx := one_le_htOf N₁ x
  have hy := one_le_htOf N₂ y
  refine max_le (one_le_mul_of_one_le_of_one_le hx hy) (max_le ?_ ?_)
  · rw [h1]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)
  · rw [h2]
    refine (hN _ _).trans (max_le ?_ ?_)
    · exact (inv_le_htOf N₁ x).trans (le_mul_of_one_le_right' hy)
    · exact (inv_le_htOf N₂ y).trans (le_mul_of_one_le_left' hx)

theorem bc_val_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h1 : (X : Matrix (Fin d) (Fin d) R) = blk e (x : Matrix (Fin p) (Fin p) R) (y : Matrix (Fin q) (Fin q) R)) :
    ((bc φ X : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e ((bc φ x : GL (Fin p) R') : Matrix (Fin p) (Fin p) R') ((bc φ y : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  show (X : Matrix (Fin d) (Fin d) R).map φ = _
  rw [h1, blk_map _ _ _ (map_zero φ)]
  rfl

theorem bc_inv_blk {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X : GL (Fin d) R} {x : GL (Fin p) R}
    {y : GL (Fin q) R}
    (h2 : ((X⁻¹ : GL (Fin d) R) : Matrix (Fin d) (Fin d) R) =
      blk e ((x⁻¹ : GL (Fin p) R) : Matrix (Fin p) (Fin p) R) ((y⁻¹ : GL (Fin q) R) : Matrix (Fin q) (Fin q) R)) :
    (((bc φ X)⁻¹ : GL (Fin d) R') : Matrix (Fin d) (Fin d) R') =
      blk e (((bc φ x)⁻¹ : GL (Fin p) R') : Matrix (Fin p) (Fin p) R')
        (((bc φ y)⁻¹ : GL (Fin q) R') : Matrix (Fin q) (Fin q) R') := by
  simp only [← map_inv]
  exact bc_val_blk e φ h2

theorem opNorm_blk_le (a : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin q) (Fin q) ℂ) :
    opNorm (blk e a b) ≤ max (opNorm a) (opNorm b) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
  obtain ⟨v, rfl⟩ : ∃ v : Fin d → ℂ, x = WithLp.toLp 2 v := ⟨x.ofLp, rfl⟩
  set c : ℝ := ((max (opNorm a) (opNorm b) : ℝ≥0) : ℝ) with hcdef
  have hc : 0 ≤ c := NNReal.coe_nonneg _
  have ha : ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm a : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_left _ _
    exact this
  have hb : ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ≤
      c * ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ := by
    rw [← Matrix.toEuclideanCLM_toLp]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : ((opNorm b : ℝ≥0) : ℝ) ≤ c := by rw [hcdef]; exact_mod_cast le_max_right _ _
    exact this
  have key : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (blk e a b) (WithLp.toLp 2 v)‖ ^ 2 =
      ‖(WithLp.toLp 2 (a *ᵥ fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (b *ᵥ fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [Matrix.toEuclideanCLM_toLp, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← e.sum_comp, Fintype.sum_sum_type]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;>
      simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, mulVec, dotProduct, ← e.sum_comp, Fintype.sum_sum_type]
  have knorm : ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin d))‖ ^ 2 =
      ‖(WithLp.toLp 2 (fun i => v (e (.inl i))) : EuclideanSpace ℂ (Fin p))‖ ^ 2 +
      ‖(WithLp.toLp 2 (fun i => v (e (.inr i))) : EuclideanSpace ℂ (Fin q))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← e.sum_comp,
      Fintype.sum_sum_type]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc (norm_nonneg _)) two_ne_zero).1 ?_
  rw [key, mul_pow, knorm, mul_add, ← mul_pow, ← mul_pow]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ha 2) (pow_le_pow_left₀ (norm_nonneg _) hb 2)

end Generic

variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
variable {p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)

theorem normFin_blk_le (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (a : Matrix (Fin p) (Fin p) (Fv F v ⊗[F] E)) (b : Matrix (Fin q) (Fin q) (Fv F v ⊗[F] E)) :
    normFin F v (blk e a b) ≤ max (normFin F v a) (normFin F v b) := by
  refine (normFin_le_iff F v).2 fun i j => ?_
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, reindex_apply, submatrix_apply]
  rcases e.symm i with i | i <;> rcases e.symm j with j | j
  · rw [fromBlocks_apply₁₁]; exact (absFin_le_normFin F v a i j).trans (le_max_left _ _)
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, absFin_zero]; exact zero_le
  · rw [fromBlocks_apply₂₂]; exact (absFin_le_normFin F v b i j).trans (le_max_right _ _)

theorem normInf_blk_le (w : InfinitePlace F) (a : Matrix (Fin p) (Fin p) (w.Completion ⊗[F] E))
    (b : Matrix (Fin q) (Fin q) (w.Completion ⊗[F] E)) :
    normInf F w (blk e a b) ≤ max (normInf F w a) (normInf F w b) :=
  (normInf_le_iff F w).2 fun τ => by
    rw [blk_map _ _ _ (map_zero (infEmb τ))]
    exact (opNorm_blk_le e _ _).trans
      (max_le_max ((normInf_le_iff F w).1 le_rfl τ) ((normInf_le_iff F w).1 le_rfl τ))

theorem heightGL_blk_le (X : GL (Fin d) (AF F ⊗[F] E)) (x : GL (Fin p) (AF F ⊗[F] E)) (y : GL (Fin q) (AF F ⊗[F] E))
    (h1 : (X : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e (x : Matrix (Fin p) (Fin p) (AF F ⊗[F] E)) (y : Matrix (Fin q) (Fin q) (AF F ⊗[F] E)))
    (h2 : ((X⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) =
      blk e ((x⁻¹ : GL (Fin p) (AF F ⊗[F] E)) : Matrix (Fin p) (Fin p) (AF F ⊗[F] E))
        ((y⁻¹ : GL (Fin q) (AF F ⊗[F] E)) : Matrix (Fin q) (Fin q) (AF F ⊗[F] E))) :
    heightGL F X ≤ heightGL F x * heightGL F y := by
  unfold heightGL
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib,
    ← finprod_mul_distrib (finite_mulSupport_htFin F x) (finite_mulSupport_htFin F y)]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_)
    (finprod_le_finprod' (finite_mulSupport_htFin F _) ?_ fun v => ?_)
  · exact htOf_blk_le e (normInf_blk_le F e w) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)
  · exact ((finite_mulSupport_htFin F x).union (finite_mulSupport_htFin F y)).subset (Function.mulSupport_mul _ _)
  · exact htOf_blk_le e (normFin_blk_le F e v) _ _ _ (bc_val_blk e _ h1) (bc_inv_blk e _ h2)

theorem ht_blkU_le : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  intro D A B d e J hJ g g₁
  have h := heightGL_blk_le D.host.F e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)).1 (Formalism.L2.Theta.matHom A g)
    (Formalism.L2.Theta.matHom B g₁) rfl (by
      show blk e (Formalism.L2.Theta.mt A g⁻¹) (Formalism.L2.Theta.mt B g₁⁻¹) = _
      simp only [Formalism.L2.Theta.mt, map_inv])
  show ((heightGL D.host.F _ : ℝ≥0) : ℝ) ≤ ((heightGL D.host.F _ : ℝ≥0) : ℝ) * ((heightGL D.host.F _ : ℝ≥0) : ℝ)
  exact_mod_cast h

end GlobalTheory.BlockHeight

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddLeftComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.WeilAddLeft

theorem pow_comp_hom {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul (Units.map _) u v

theorem weilEq_mul_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm
  haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm
  have tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1) := fun f hf => by
    rw [← pow_comp_hom, hx, one_comp]
  have tory : (y ≫ g) ^ n = 1 := by rw [← pow_comp_hom, hy, one_comp]
  obtain ⟨c₁, hc₁⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory
  obtain ⟨c₂, hc₂⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory
  have a₁ := (h₁ n x y c₁ hn hx hy).1 hc₁
  have a₂ := (h₂ n x y c₂ hn hx hy).1 hc₂
  have hB := weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂
  have hA := weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂
  rw [← MonObj.comp_mul] at hB hA
  rw [← A.t.act.add] at hA
  rw [← unitOn_mul] at hB hA
  constructor
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory.CM.WeilAddLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingAddRightComplex
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.WeilEqAdd

theorem weilIs_mul_right {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} (x y y' : T ⟶ P.A)
    (c c' : Γ(T.left, ⊤)ˣ) (h : Out.WeilIs P.A P.L k x y c) (h' : Out.WeilIs P.A P.L k x y' c') :
    Out.WeilIs P.A P.L k x (y * y') (c * c') := by
  have h₁ := GlobalTheory.CommPairing.weilIs_symm P.isLB h
  have h₂ := GlobalTheory.CommPairing.weilIs_symm P.isLB h'
  have h₃ := GlobalTheory.CommPairing.weilIs_symm P.isLB
    (GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds S P k T y y' x _ _ h₁ h₂)
  have e : (c⁻¹ * c'⁻¹)⁻¹ = c * c' := by rw [mul_inv, inv_inv, inv_inv, mul_comm]
  rwa [e] at h₃

end GlobalTheory.WeilEqAdd

namespace GlobalTheory


open WeilEqAdd in
theorem weilEq_mul_right_add : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f g₁ g₂ : A.t.G ⟶ B.t.G), IsMonHom f → IsMonHom g₁ →
    IsMonHom g₂ → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f g₁ A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f g₂ A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f (g₁ * g₂) A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f g₁ g₂ _ _ _ r₁ r₂ h₁ h₂ n x y c hn hx hy
  haveI : IsCommMonObj A.pol.A := A.ab.comm
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have ex : ∀ r : 𝓞 E, ∃ u : ℂˣ,
      Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act r) (y ≫ 𝟙 _) (unitOn u) := by
    intro r
    haveI := A.t.act.hom r
    have hxr : (x ≫ A.t.act.act r) ^ n = 1 := by
      rw [← MonObj.pow_comp, hx, MonObj.one_comp]
    have hy' : (y ≫ 𝟙 _) ^ n = 1 := by rw [Category.comp_id]; exact hy
    exact GlobalTheory.TorsionGenerators.exists_weilIs hL A.pol (σ₁.comp (algebraMap (𝓞 K) K)) hxr hy'
  have um : ∀ a b : ℂˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  obtain ⟨c₁, e₁⟩ := ex r₁
  obtain ⟨c₂, e₂⟩ := ex r₂
  have hA : Out.WeilIs A.t.G A.t.PP.L n (x ≫ A.t.act.act (r₁ + r₂)) (y ≫ 𝟙 _) (unitOn (c₁ * c₂)) := by
    rw [A.t.act.add, MonObj.comp_mul, um]
    exact GlobalTheory.weilIs_mul_left GlobalTheory.globalFns_holds _ A.pol n _ _ _ _ _ _ e₁ e₂
  have hB : Out.WeilIs B.t.G B.t.PP.L n (x ≫ f) (y ≫ (g₁ * g₂)) (unitOn (c₁ * c₂)) := by
    rw [MonObj.comp_mul, um]
    exact weilIs_mul_right B.pol n _ _ _ _ _ ((h₁ n x y c₁ hn hx hy).2 e₁) ((h₂ n x y c₂ hn hx hy).2 e₂)
  constructor
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory
end
end

