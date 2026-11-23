module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
public import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0778
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0786
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KroneckerProductFamilyMulOneDet
section
namespace GlobalTheory.DefPt

open scoped Matrix

section

variable {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
  {R : Type} [CommRing R]

theorem kronFamily_mul (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron (fun t => M t * M' t) := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun K _ => (Finset.prod_mul_distrib).symm

theorem kronFamily_one : kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  ext I I'
  simp only [kron, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

theorem kronFamily_det_single (t : T) (A : Matrix (J t) (J t) R) :
    (kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)).det
      = A.det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have h : kron (Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A)
      = (Matrix.blockDiagonal (fun _ : (∀ j : {j // j ≠ t}, J j) => A)).submatrix
          (Equiv.piSplitAt t J) (Equiv.piSplitAt t J) := by
    ext I I'
    simp only [kron, Matrix.of_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
      Equiv.piSplitAt_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t), Function.update_self]
    have h2 : ∏ s ∈ Finset.univ.erase t,
        Function.update (fun s => (1 : Matrix (J s) (J s) R)) t A s (I s) (I' s)
        = ∏ s ∈ Finset.univ.erase t, (if I s = I' s then (1 : R) else 0) := by
      refine Finset.prod_congr rfl fun s hs => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hs), Matrix.one_apply]
    rw [h2, Finset.prod_ite_zero]
    simp [funext_iff]
  rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal, Finset.prod_const,
    Finset.card_univ, Fintype.card_pi]
  congr 1
  exact (Finset.prod_subtype (Finset.univ.erase t) (p := fun j => j ≠ t) (by simp)
    (fun s => Fintype.card (J s))).symm

theorem kronFamily_det (M : ∀ t, Matrix (J t) (J t) R) :
    (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
  have key : ∀ S : Finset T, (kron (fun t => if t ∈ S then M t else 1)).det
      = ∏ t ∈ S, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [kronFamily_one]
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, ← ih, ← kronFamily_det_single, ← Matrix.det_mul, kronFamily_mul]
      congr 2
      funext s
      by_cases hs : s = a
      · subst hs
        simp [ha]
      · simp [hs]
  simpa using key Finset.univ

end

theorem kronFamily_mul_one_det :
    ∀ (T : Type) [Fintype T] [DecidableEq T] (J : T → Type) [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
      (R : Type) [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R),
      kron M * kron M' = kron (fun t => M t * M' t) ∧
      kron (fun t => (1 : Matrix (J t) (J t) R)) = 1 ∧
      (kron M).det = ∏ t, (M t).det ^ (∏ s ∈ Finset.univ.erase t, Fintype.card (J s)) :=
  fun _ _ _ _ _ _ _ _ M M' => ⟨kronFamily_mul M M', kronFamily_one, kronFamily_det M⟩

end GlobalTheory.DefPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastRowTopComponentDualWeylEqMonomialMul
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

theorem monomial_eq_zmon_mul_emb {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (μ : Fin (n + 1) × Fin n →₀ ℕ)
    (hμ : ∀ s, μ (Fin.last n, s) = b s) (c : K) :
    ∃ f, (monomial μ c : BP K n) = zmon K n b * emb K n f := by
  refine ⟨C c * ∏ a : Fin n, ∏ s : Fin n, X (a, s) ^ μ (a.castSucc, s), ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_castSucc]
  simp only [hμ, zmon, emb, map_mul, map_prod, map_pow, rename_X, rename_C]
  ring

theorem eq_zmon_mul_emb_of_homogeneous {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) (H : BP K n)
    (hH : IsWeightedHomogeneous (zW n) H (fun s => (b s : ℤ))) : ∃ f, H = zmon K n b * emb K n f := by
  have h : ∀ μ ∈ H.support, ∃ f, (monomial μ (AddMonoidAlgebra.coeff H μ) : BP K n) = zmon K n b * emb K n f := by
    intro μ hμ
    refine monomial_eq_zmon_mul_emb b μ (fun s => ?_) _
    have h1 := congrFun (hH (mem_support_iff.1 hμ)) s
    rw [bm_weight_zW] at h1
    exact_mod_cast h1
  choose! g hg using h
  refine ⟨∑ μ ∈ H.support, g μ, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, ← Finset.sum_congr rfl hg]
  exact H.as_sum

theorem zmon_mul_emb_injective {K : Type} [Field K] {n : ℕ} (b : Fin n → ℕ) {f g : MvPolynomial (Fin n × Fin n) K}
    (h : zmon K n b * emb K n f = zmon K n b * emb K n g) : f = g := by
  have hz : zmon K n b ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => pow_ne_zero _ (X_ne_zero _)
  refine rename_injective (fun v : Fin n × Fin n => ((v.1.castSucc, v.2) : Fin (n + 1) × Fin n)) ?_
    (mul_left_cancel₀ hz h)
  exact (Fin.castSucc_injective n).prodMap Function.injective_id

theorem zcomp_top_eq_zmon_mul_emb (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : Fin n → ℕ) (G : BP K n)
    (hG : G ∈ dualWeyl K (n + 1) n lam) (b : Fin n → ℕ) (hb : ∀ s, b s ≤ lam s)
    (hmax : ∀ β', zcomp K n β' G ≠ 0 → omg β' ≤ omg fun s => (b s : ℤ)) :
    ∃ f ∈ dualWeyl K n n (fun s => lam s - b s), zcomp K n (fun s => (b s : ℤ)) G = zmon K n b * emb K n f := by
  obtain ⟨f, hf⟩ := eq_zmon_mul_emb_of_homogeneous b _ (bmD_zcomp_isWH (fun s => (b s : ℤ)) G)
  refine ⟨f, bm_mem_dualWeyl_iff.2 ⟨fun s => ?_, fun l j hlj => ?_⟩, hf⟩
  · have h := bmD_weight lam G hG (fun s => (b s : ℤ)) s
    rw [hf, bmE_lead, bm_ndE_self] at h
    apply zmon_mul_emb_injective b
    rw [h, map_smul, mul_smul_comm, Nat.cast_sub (hb s)]
    push_cast
    rfl
  · have h := bmD_raise lam G hG (fun s => (b s : ℤ)) hmax l j hlj
    rw [hf, bmE_lead] at h
    apply zmon_mul_emb_injective b
    rw [h, map_zero, mul_zero]

end GlobalTheory.BrCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerComapLinearIsometry
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical

namespace GlobalTheory

theorem inter_comap_isom : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (Φ : V ≃ₗ[ℂ] W), (∀ x y, H x y = H' (Φ x) (Φ y)) → IsHerm H' → ∀ (Λ₁ Λ₂ : AddSubgroup W) (α : W → ℂ) (F : W → ℂ), IsSemiChar H' Λ₂ α → F ∈ fixedBy H' α Λ₁ → relIdx Λ₁ Λ₂ ≠ 0 → ∀ z, inter H (fun v => α (Φ v)) (Λ₁.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (Λ₂.comap (Φ : V →ₗ[ℂ] W).toAddMonoidHom) (fun v => F (Φ v)) z = inter H' α Λ₁ Λ₂ F (Φ z) := by
  intro V W _ _ _ _ H H' Φ hΦ hH' Λ₁ Λ₂ α F hα hF hn z
  set f : V →+ W := (Φ : V →ₗ[ℂ] W).toAddMonoidHom with hf
  have hfs : Function.Surjective f := Φ.surjective
  have hfx : ∀ v, f v = Φ v := fun v => rfl
  have hH : IsHerm H := by
    intro x y; rw [hΦ, hΦ, hH']
  have hα' : IsSemiChar H (Λ₂.comap f) (fun v => α (Φ v)) := by
    refine ⟨fun x hx => hα.1 (Φ x) hx, fun x hx y hy => ?_⟩
    have := hα.2 (Φ x) hx (Φ y) hy
    simp only [map_add (f := _), altE] at this ⊢
    rw [this, hΦ]
  have hopU : ∀ x (G : W → ℂ) v, opU H x (fun w => G (Φ w)) v = opU H' (Φ x) G (Φ v) := by
    intro x G v
    simp only [opU, map_add (f := _), hΦ]
  have hF' : (fun v => F (Φ v)) ∈ fixedBy H (fun v => α (Φ v)) (Λ₁.comap f) := by
    intro x hx v
    rw [hopU]
    exact hF (Φ x) hx (Φ v)
  have hidx : relIdx (Λ₁.comap f) (Λ₂.comap f) = relIdx Λ₁ Λ₂ := by
    unfold relIdx
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hfs]
  obtain ⟨S, hS⟩ := (cosetRepsExist W Λ₁ Λ₂ hn).1
  have hS' : IsReps (Λ₁.comap f) (Λ₂.comap f) (S.image Φ.symm) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
      show f (Φ.symm x) ∈ Λ₂
      rw [hfx, LinearEquiv.apply_symm_apply]; exact hS.1 x hx
    · intro w hw w' hw' hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hw'
      have hd' : x - x' ∈ Λ₁ := by
        have : f (Φ.symm x - Φ.symm x') ∈ Λ₁ := hd
        rwa [hfx, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      rw [hS.2.1 x hx x' hx' hd']
    · intro y hy
      obtain ⟨x, hx, hd⟩ := hS.2.2 (Φ y) hy
      refine ⟨Φ.symm x, Finset.mem_image.2 ⟨x, hx, rfl⟩, ?_⟩
      show f (y - Φ.symm x) ∈ Λ₁
      rw [hfx, map_sub, LinearEquiv.apply_symm_apply]; exact hd
  rw [InterReps_of semicharacterHom V H hH _ _ _ hα' _ hF' _ hS' z,
    InterReps_of semicharacterHom W H' hH' _ _ _ hα _ hF _ hS (Φ z), hidx]
  congr 1
  unfold sumU
  rw [Finset.sum_image (fun a _ b _ hab => Φ.symm.injective hab)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hopU, LinearEquiv.apply_symm_apply]
  simp only [LinearEquiv.apply_symm_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerProdOrthogonalBlocks
section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
open scoped BigOperators

namespace GlobalTheory.BaseVacuum.ProductTheta

variable (L : PeriodPair) {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

theorem stdH_prod (x y : ι × m → ℂ) :
    stdH L (ι × m) x y = ∑ k, stdH L m (fun v => x (k, v)) (fun v => y (k, v)) := by
  rw [(stdHBasic L (ι × m)).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(stdHBasic L m).1]

theorem alphaQ_prod (c : ℝ) (y : ι × m → ℂ) :
    alphaQ c (stdH L (ι × m)) y = ∏ k, alphaQ c (stdH L m) (fun v => y (k, v)) := by
  unfold alphaQ qOf
  rw [← Complex.exp_sum]
  congr 1
  rw [stdH_prod, Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]

theorem altE_prod (x y : ι × m → ℂ) :
    altE (stdH L (ι × m)) x y = ∑ k, altE (stdH L m) (fun v => x (k, v)) (fun v => y (k, v)) := by
  unfold altE
  rw [stdH_prod, Complex.im_sum]

theorem mem_stdLat_prod (x : ι × m → ℂ) :
    x ∈ stdLat L (ι × m) ↔ ∀ k, (fun v => x (k, v)) ∈ stdLat L m := by
  simp only [stdLat, AddSubgroup.mem_pi, Set.mem_univ, true_implies, Prod.forall]

theorem heisenbergOperator_gaussianVacuum_prod_blocks (ω₀ : ℂ) (x z : ι × m → ℂ) :
    opU (stdH L (ι × m)) x (F0 L ω₀ (ι × m)) z
      = ∏ k, opU (stdH L m) (fun v => x (k, v)) (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold F0
  rw [opUStd L (ι × m), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [opUStd L m]

theorem gaussianVacuum_prod_blocks (ω₀ : ℂ) (z : ι × m → ℂ) : F0 L ω₀ (ι × m) z = ∏ k, F0 L ω₀ m (fun v => z (k, v)) := by
  unfold F0 prodFn
  rw [Fintype.prod_prod_type]

theorem semiChar_prod (c : ℝ) (Λ : AddSubgroup (m → ℂ)) (h : IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m))) :
    IsSemiChar (stdH L (ι × m)) (blkLat (ι := ι) Λ) (alphaQ c (stdH L (ι × m))) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [alphaQ_prod]
    exact Finset.prod_induction _ (fun a : ℂ => a = 1 ∨ a = -1)
      (fun a b ha hb => by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
      (Or.inl rfl) (fun k _ => h.1 _ (hx k))
  · rw [alphaQ_prod, alphaQ_prod, alphaQ_prod, altE_prod, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    exact h.2 _ (hx k) _ (hy k)

theorem fixed_prod (ω₀ : ℂ) (c' : ℝ)
    (hF : F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c' (stdH L m)) (stdLat L m)) :
    F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c' (stdH L (ι × m))) (stdLat L (ι × m)) := by
  change ∀ x ∈ stdLat L (ι × m), ∀ z, _ = _
  intro x hx z
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib, gaussianVacuum_prod_blocks]
  have hx' := (mem_stdLat_prod L x).1 hx
  exact Finset.prod_congr rfl fun k _ => hF _ (hx' k) _

def prodReps (S : Finset (m → ℂ)) : Finset (ι × m → ℂ) :=
  (Fintype.piFinset fun _ : ι => S).map (Equiv.curry ι m ℂ).symm.toEmbedding

theorem card_prodReps (S : Finset (m → ℂ)) : (prodReps (ι := ι) S).card = S.card ^ Fintype.card ι := by
  rw [prodReps, Finset.card_map, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]

theorem prodReps_isReps {Λ : AddSubgroup (m → ℂ)} {S : Finset (m → ℂ)} (hS : IsReps (stdLat L m) Λ S) :
    IsReps (stdLat L (ι × m)) (blkLat (ι := ι) Λ) (prodReps S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf
    intro k
    exact hS.1 _ (hf k)
  · intro x hx y hy hd
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_map.1 hy
    rw [Fintype.mem_piFinset] at hf hg
    have hd' := (mem_stdLat_prod L _).1 hd
    have : f = g := funext fun k => hS.2.1 _ (hf k) _ (hg k) (hd' k)
    rw [this]
  · intro y hy
    have : ∀ k, ∃ x ∈ S, (fun v => y (k, v)) - x ∈ stdLat L m := fun k => hS.2.2 _ (hy k)
    choose f hf hfy using this
    refine ⟨(Equiv.curry ι m ℂ).symm f, Finset.mem_map_of_mem _ (Fintype.mem_piFinset.2 hf), ?_⟩
    rw [mem_stdLat_prod]
    intro k
    exact hfy k

theorem relIdx_eq_card {V : Type} [AddCommGroup V] [Module ℂ V] {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V}
    (hS : IsReps Λ₁ Λ₂ S) : relIdx Λ₁ Λ₂ = S.card := by
  have h1 := Nat.card_eq_of_bijective _ (repClass_bijective hS)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at h1
  rw [h1]
  rfl

theorem sumU_prod (c : ℝ) (ω₀ : ℂ) (S : Finset (m → ℂ)) (z : ι × m → ℂ) :
    sumU (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (prodReps S) (F0 L ω₀ (ι × m)) z
      = ∏ k, sumU (stdH L m) (alphaQ c (stdH L m)) S (F0 L ω₀ m) (fun v => z (k, v)) := by
  unfold sumU prodReps
  rw [Finset.sum_map, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [alphaQ_prod, heisenbergOperator_gaussianVacuum_prod_blocks, ← Finset.prod_mul_distrib]
  rfl

theorem sqrt_pow' (r : ℝ) (hr : 0 ≤ r) (n : ℕ) : Real.sqrt (r ^ n) = Real.sqrt r ^ n := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg r) n), pow_right_comm, Real.sq_sqrt hr]

end GlobalTheory.BaseVacuum.ProductTheta

namespace GlobalTheory.BaseVacuum


open ProductTheta in
theorem prod_blk_inter : ∀ (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) (ι m : Type) [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m] (Λ : AddSubgroup (m → ℂ)), IsSemiChar (stdH L m) Λ (alphaQ c (stdH L m)) → F0 L ω₀ m ∈ fixedBy (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) → relIdx (stdLat L m) Λ ≠ 0 → IsSemiChar (stdH L (ι × m)) (blkLat Λ) (alphaQ c (stdH L (ι × m))) ∧ F0 L ω₀ (ι × m) ∈ fixedBy (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) ∧ relIdx (stdLat L (ι × m)) (blkLat Λ) ≠ 0 ∧ ∀ w, inter (stdH L (ι × m)) (alphaQ c (stdH L (ι × m))) (stdLat L (ι × m)) (blkLat Λ) (F0 L ω₀ (ι × m)) w = ∏ k, inter (stdH L m) (alphaQ c (stdH L m)) (stdLat L m) Λ (F0 L ω₀ m) (fun v => w (k, v)) := by
  intro L ω₀ c ι m _ _ _ _ Λ hα hF hn
  have hα' := semiChar_prod L (ι := ι) c Λ hα
  have hF' := fixed_prod L (ι := ι) ω₀ c hF
  obtain ⟨⟨S, hS⟩, hcard⟩ := repsExist _ (stdLat L m) Λ hn
  have hS' := prodReps_isReps L (ι := ι) hS
  have hr : relIdx (stdLat L (ι × m)) (blkLat (ι := ι) Λ) = relIdx (stdLat L m) Λ ^ Fintype.card ι := by
    rw [relIdx_eq_card hS', card_prodReps, hcard S hS]
  refine ⟨hα', hF', by rw [hr]; exact pow_ne_zero _ hn, fun w => ?_⟩
  rw [interReps _ _ (stdHBasic L _).2.1 _ _ _ hα' _ hF' _ hS' w, sumU_prod]
  rw [Finset.prod_congr rfl fun k _ => interReps _ _ (stdHBasic L m).2.1 _ _ _ hα _ hF _ hS (fun v => w (k, v))]
  rw [hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Nat.cast_pow,
    sqrt_pow' _ (Nat.cast_nonneg _), Complex.ofReal_pow, inv_pow]

end GlobalTheory.BaseVacuum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.LevelSchwartz

theorem mem_schA_of_level : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (Φ : (Fin N → AF F) → ℂ),
    (∃ U : AddSubgroup (Fin N → AF F), IsOpen (U : Set (Fin N → AF F)) ∧ ∀ u ∈ U, inf u = 0 → ∀ x, Φ (x + u) = Φ x) →
    (∃ K : Set (Fin N → Af F), IsCompact K ∧ ∀ x, Φ x ≠ 0 → fin x ∈ K) →
    (∀ x, ∃ g : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ, ∀ t, g t = Φ (x + embR t)) →
    Φ ∈ GlobalTheory.WeilM.schA F (Fin N) := by
  intro F _ _ N Φ ⟨U, hUo, hU⟩ ⟨K, hK, hKs⟩ hS
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let ι : (Fin N → Af F) →+ (Fin N → AF F) :=
    { toFun := fun v i => pairA F 0 (v i)
      map_zero' := rfl
      map_add' := fun a b => by
        funext i
        show (((0 : Ainf F), a i + b i) : Ainf F × Af F) = ((0 : Ainf F), a i) + ((0 : Ainf F), b i)
        simp }
  have hιc : Continuous ι := continuous_pi fun i =>
    (show Continuous fun v : Fin N → Af F => (((0 : Ainf F), v i) : Ainf F × Af F) from
      continuous_const.prodMk (continuous_apply i))
  have hιinf : ∀ v, inf (ι v) = 0 := fun v => rfl
  have hfin : ∀ a t, fin (ι a + embR t) = a := fun a t => by
    funext i
    show (a i + 0 : Af F) = a i
    exact add_zero _
  have hdec : ∀ y : Fin N → AF F, y = ι (fin y) + embR (fun i => e (y i).1) := fun y => by
    funext i
    show (y i : Ainf F × Af F) = (((0 : Ainf F), (y i).2) : Ainf F × Af F) + ((e.symm (e (y i).1), (0 : Af F)))
    rw [RingEquiv.symm_apply_apply]
    refine Prod.ext ?_ ?_ <;> simp
  let W : AddSubgroup (Fin N → Af F) := U.comap ι
  have hWo : IsOpen (W : Set (Fin N → Af F)) := hUo.preimage hιc
  have hWcl : IsClosed (W : Set (Fin N → Af F)) := AddSubgroup.isClosed_of_isOpen W hWo
  have hinv : ∀ a b, -a + b ∈ W → ∀ z, Φ (ι b + z) = Φ (ι a + z) := by
    intro a b hab z
    rw [← hU (ι (-a + b)) hab (hιinf _) (ι a + z)]
    congr 1
    rw [map_add (f := _), map_neg]
    abel
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun a : Fin N → Af F => {b | -a + b ∈ W})
    (fun a => hWo.preimage (continuous_const.add continuous_id))
    (fun b _ => Set.mem_iUnion.2 ⟨b, show -b + b ∈ W by rw [neg_add_cancel]; exact W.zero_mem⟩)
  let T : Finset ((Fin N → Af F) ⧸ W) := t.image QuotientAddGroup.mk
  choose g hg using fun q : (Fin N → Af F) ⧸ W => hS (ι q.out)
  let ind : ((Fin N → Af F) ⧸ W) → (Fin N → Af F) → ℂ := fun q a =>
    if (QuotientAddGroup.mk a : (Fin N → Af F) ⧸ W) = q then 1 else 0
  have key : Φ = ∑ q ∈ T, GlobalTheory.WeilM.pureA F (g q) (ind q) := by
    funext y
    rw [Finset.sum_apply]
    show Φ y = ∑ q ∈ T, g q (fun i => e (y i).1) *
      (if (QuotientAddGroup.mk (fin y) : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hT
    · rw [hg]
      conv_lhs => rw [hdec y]
      exact hinv _ _ (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)) _
    · by_contra hne
      obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.1 (ht (hKs y hne))
      exact hT (Finset.mem_image.2 ⟨b, hb, QuotientAddGroup.eq.2 hab⟩)
  rw [key]
  refine Submodule.sum_mem _ fun q _ => ?_
  by_cases h0 : ∀ s, g q s = 0
  · have : GlobalTheory.WeilM.pureA F (g q) (ind q) = 0 := by
      funext y
      simp [GlobalTheory.WeilM.pureA, h0]
    rw [this]
    exact zero_mem _
  push_neg at h0
  obtain ⟨s0, hs0⟩ := h0
  refine Submodule.subset_span ⟨g q, ind q, ?_, rfl⟩
  let C : Set (Fin N → Af F) := {a | -q.out + a ∈ W}
  have hCcl : IsClosed C := hWcl.preimage (continuous_const.add continuous_id)
  have hCK : C ⊆ K := by
    intro a ha
    have h1 : Φ (ι a + embR s0) ≠ 0 := by
      rw [hinv _ _ ha, ← hg]
      exact hs0
    simpa [hfin] using hKs _ h1
  have hmk : IsLocallyConstant (fun a : Fin N → Af F => (a : (Fin N → Af F) ⧸ W)) :=
    (IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{b | -b + x ∈ W},
      hWo.preimage (continuous_neg.add continuous_const), by simp, fun b hb => QuotientAddGroup.eq.2 hb⟩
  refine ⟨hmk.comp fun q' => if q' = q then (1 : ℂ) else 0, ?_⟩
  refine HasCompactSupport.intro' (hK.of_isClosed_subset hCcl hCK) hCcl fun x hx => ?_
  show (if (QuotientAddGroup.mk x : (Fin N → Af F) ⧸ W) = q then (1 : ℂ) else 0) = 0
  rw [if_neg]
  intro hq
  apply hx
  show -q.out + x ∈ W
  exact QuotientAddGroup.eq.1 (by rw [hq, QuotientAddGroup.out_eq'])

end GlobalTheory.LevelSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormulaStatement
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_alt : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  first | exact @GlobalTheory.JSW.shintani_formula | exact GlobalTheory.JSW.shintani_formula | (intros; apply GlobalTheory.JSW.shintani_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLieAlgebraEntriesOrthonormalFrameStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialUnitaryLieAlgebra_entries_orthonormal_frame : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∀ (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r)), fromFrame x Y ∈ realLie X.Ψ X.Gm → (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧ ∀ τ, ∑ a, Y (τ, a, a) = 0 := by
  first | exact @GlobalTheory.SUVol.FrameSkew.entries_of_mem | exact GlobalTheory.SUVol.FrameSkew.entries_of_mem | (intros; apply GlobalTheory.SUVol.FrameSkew.entries_of_mem <;> assumption)
end

