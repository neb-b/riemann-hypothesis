module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0011

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticePointsBelowFinite
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

noncomputable section

theorem exists_coercive_of_posDef {ι : Type*} [Fintype ι] {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ (z : ι → ℂ) (j : ι), c * ‖z j‖ ^ 2 ≤ (star z ⬝ᵥ (P *ᵥ z)).re :=
  _root_.UpperTheory.Reformulated.B.CoerciveOfPositiveDefinite.exists_coercive_of_posDef hP

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_coord_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by
  choose c hc hcoer using fun w => exists_coercive_of_posDef (M.posDef w)
  set G : InfinitePlace E → Matrix ι ι ℂ := fun w =>
    (((g : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) with hG
  refine ⟨∑ w, ∑ i, ∑ j, ‖G w i j‖ / Real.sqrt (c w), by positivity, fun y w i => ?_⟩
  set z := invApply g y with hz
  have hre : ∀ w', 0 ≤ (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re := fun w' =>
    (Complex.nonneg_iff.mp ((M.posDef w').posSemidef.dotProduct_mulVec_nonneg (z w'))).1
  have hinv : G w * (((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) = 1 := by
    simp [hG]
  have hy : y w = G w *ᵥ z w := by
    rw [hz, invApply, mulVec_mulVec, hinv, one_mulVec]
  have hzj : ∀ j, ‖z w j‖ ≤ M.len z / Real.sqrt (c w) := by
    intro j
    have hsq : 0 < Real.sqrt (c w) := Real.sqrt_pos.2 (hc w)
    rw [le_div_iff₀ hsq]
    have h1 : c w * ‖z w j‖ ^ 2 ≤ ∑ w', (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re :=
      (hcoer w (z w) j).trans (Finset.single_le_sum (fun w' _ => hre w') (Finset.mem_univ w))
    have h2 := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_mul (hc w).le, Real.sqrt_sq (norm_nonneg _)] at h2
    unfold Majorant.len
    linarith
  have hlen : 0 ≤ M.len z := Real.sqrt_nonneg _
  calc ‖y w i‖ = ‖∑ j, G w i j * z w j‖ := by rw [hy]; rfl
    _ ≤ ∑ j, ‖G w i j‖ * ‖z w j‖ := (norm_sum_le _ _).trans (by simp)
    _ ≤ ∑ j, ‖G w i j‖ / Real.sqrt (c w) * M.len z := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [div_mul_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (hzj j) (norm_nonneg _)
    _ = (∑ j, ‖G w i j‖ / Real.sqrt (c w)) * M.len z := by rw [Finset.sum_mul]
    _ ≤ (∑ w', ∑ i', ∑ j, ‖G w' i' j‖ / Real.sqrt (c w')) * M.len z := by
        refine mul_le_mul_of_nonneg_right ?_ hlen
        refine le_trans ?_ (Finset.single_le_sum (f := fun w' => ∑ i', ∑ j,
          ‖G w' i' j‖ / Real.sqrt (c w')) (fun _ _ => by positivity) (Finset.mem_univ w))
        exact Finset.single_le_sum (f := fun i' => ∑ j, ‖G w i' j‖ / Real.sqrt (c w))
          (fun _ _ => by positivity) (Finset.mem_univ i)


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LatticePointsBelowFinite.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LatticePointsBelowFinite.Statement h v := by
  classical
  intro M La g t hLa
  obtain ⟨S, hS⟩ := hLa.fg

  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun s => Finset.univ.image fun i => v.repr s i)
  let T : AddSubgroup W :=
    { carrier := {y | ∀ i, IsIntegral ℤ (d • v.repr y i)}
      add_mem' := fun {a b} ha hb i => by
        simpa only [map_add (f := _), Finsupp.add_apply, smul_add] using (ha i).add (hb i)
      zero_mem' := fun i => by
        simpa only [map_zero, Finsupp.zero_apply, smul_zero] using isIntegral_zero
      neg_mem' := fun {a} ha i => by
        simpa only [map_neg, Finsupp.neg_apply, smul_neg] using (ha i).neg }
  have hLaT : La ≤ T := by
    have hall : ∀ s : La, (s : W) ∈ T := by
      intro s
      have hmem : s ∈ AddSubsemigroup.closure (S : Set La) := by
        rw [hS]
        trivial
      induction hmem using AddSubsemigroup.closure_induction with
      | mem s hs =>
        intro i
        exact hd _ (Finset.mem_biUnion.2 ⟨s, hs, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
      | add a b _ _ ha hb => exact T.add_mem ha hb
    intro x hx
    exact hall ⟨x, hx⟩
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.2 hd0

  obtain ⟨K, hK0, hK⟩ := exists_coord_le_len M g
  set B : ℝ := |(d : ℝ)| * (K * t) with hB
  set A : Set E := {a | IsIntegral ℤ a ∧ ∀ φ : E →+* ℂ, ‖φ a‖ ≤ B} with hA
  have hAfin : A.Finite := NumberField.Embeddings.finite_of_norm_le E ℂ B
  set φ : W → ι → E := fun x i => d • v.repr x i with hφ
  have hinj : Function.Injective φ := by
    intro x y hxy
    refine v.repr.injective (Finsupp.ext fun i => ?_)
    have := congrFun hxy i
    simp only [hφ, zsmul_eq_mul] at this
    exact mul_left_cancel₀ hdE this
  refine ((Set.Finite.pi (t := fun _ : ι => A) fun _ => hAfin).preimage hinj.injOn).subset ?_
  rintro x ⟨hx, hxt⟩ i -
  refine ⟨hLaT hx i, fun ψ => ?_⟩
  have hw : ‖ψ (v.repr x i)‖ = ‖(InfinitePlace.mk ψ).embedding (v.repr x i)‖ := by
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
  have hb := hK (vecAt v x) (InfinitePlace.mk ψ) i
  change ‖ψ (d • v.repr x i)‖ ≤ B
  rw [zsmul_eq_mul, map_mul, map_intCast, norm_mul, Complex.norm_intCast, hw, hB]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hxt.le hK0)

end Spaces

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenCauchySchwarz
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder

theorem majorant_cauchySchwarz {ι : Type*} [Fintype ι] [DecidableEq ι] {H P : Matrix ι ι ℂ}
    (hM : IsMajorantOf H P) (a b : ι → ℂ) :
    ‖star a ⬝ᵥ (H *ᵥ b)‖ ≤
      Real.sqrt (star a ⬝ᵥ (P *ᵥ a)).re * Real.sqrt (star b ⬝ᵥ (P *ᵥ b)).re := by
  have key := majorant_mul_inv_mul hM
  obtain ⟨hP, hH, hdet, hPHP⟩ := hM
  have hPdet : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  set c := P⁻¹ *ᵥ (H *ᵥ b) with hc
  have h1 : P *ᵥ c = H *ᵥ b := by
    rw [hc, mulVec_mulVec, Matrix.mul_nonsing_inv _ hPdet, one_mulVec]
  have hPinv : (P⁻¹)ᴴ = P⁻¹ := by rw [conjTranspose_nonsing_inv, hP.1.eq]
  have h2 : star c ⬝ᵥ (P *ᵥ c) = star b ⬝ᵥ (P *ᵥ b) := by
    rw [h1, hc, star_mulVec, star_mulVec, hPinv, hH.eq, vecMul_vecMul, ← dotProduct_mulVec,
      mulVec_mulVec, key]
  let _ := P.toSeminormedAddCommGroup hP.posSemidef
  let _ := P.toInnerProductSpace hP.posSemidef
  have cs := inner_mul_inner_self_le (𝕜 := ℂ) a c
  have e1 : (inner ℂ a c : ℂ) = star a ⬝ᵥ (H *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star a = _
    rw [dotProduct_comm, h1]
  have e2 : (inner ℂ c a : ℂ) = star (star a ⬝ᵥ (H *ᵥ b)) := by
    rw [← e1]; exact (inner_conj_symm (𝕜 := ℂ) c a).symm
  have e3 : (inner ℂ a a : ℂ) = star a ⬝ᵥ (P *ᵥ a) := by
    change (P *ᵥ a) ⬝ᵥ star a = _
    rw [dotProduct_comm]
  have e4 : (inner ℂ c c : ℂ) = star b ⬝ᵥ (P *ᵥ b) := by
    change (P *ᵥ c) ⬝ᵥ star c = _
    rw [dotProduct_comm, h2]
  rw [e1, e2, e3, e4, norm_star] at cs
  simp only [RCLike.re_to_complex] at cs
  have ha : 0 ≤ (star a ⬝ᵥ (P *ᵥ a)).re := hP.posSemidef.re_dotProduct_nonneg a
  have hb : 0 ≤ (star b ⬝ᵥ (P *ᵥ b)).re := hP.posSemidef.re_dotProduct_nonneg b
  rw [← Real.sqrt_mul ha]
  exact Real.le_sqrt_of_sq_le (by nlinarith)

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Majorant.isMajorantOf {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (w : InfinitePlace E) : IsMajorantOf (gramAt h v w) (M.P w) :=
  ⟨M.posDef w, (GramAtData.proof h v w).1, (GramAtData.proof h v w).2, M.siegel w⟩


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem Majorant.sqrt_le_len {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) (w : InfinitePlace E) :
    Real.sqrt (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re ≤ M.len y := by
  unfold Majorant.len
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun w => (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re)
    (fun u _ => LenSq.re_nonneg (M.posDef u) (y u)) (Finset.mem_univ w))

theorem LenCauchySchwarz.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    LenCauchySchwarz.Statement h v := by
  intro M g x y w
  rw [HermAtPlace.proof h v w x y, ← ArchInvariant.proof h v g (vecAt v x) (vecAt v y) w]
  refine (majorant_cauchySchwarz (M.isMajorantOf w) _ _).trans ?_
  exact mul_le_mul (M.sqrt_le_len _ w) (M.sqrt_le_len _ w) (Real.sqrt_nonneg _)
    ((Real.sqrt_nonneg _).trans (M.sqrt_le_len _ w))

end Places

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem vecAt_unitary (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup) (x : W)
    (w : InfinitePlace E) :
    vecAt v ((γ : W ≃ₗ[E] W) x) w =
      (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
        vecAt v x w := by
  have h1 : (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
    rw [← unitaryGroupEquivMatrix_apply]
    rfl
  have h2 := LinearMap.toMatrix_mulVec_repr v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W) x
  rw [LinearEquiv.coe_coe] at h2
  rw [h1]
  ext i
  simp only [vecAt]
  rw [← h2, RingHom.map_mulVec]
  rfl

theorem invApply_archEmbed_mul (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (g : archUnitary h v) (x : W) :
    invApply (archEmbed h v γ * g) (vecAt v ((γ : W ≃ₗ[E] W) x)) = invApply g (vecAt v x) := by
  funext w
  simp only [invApply, vecAt_unitary, Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply,
    Matrix.mulVec_mulVec]
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem MahlerCompactness.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hB : BoundedGenerators.Statement h v) (hCS : LenCauchySchwarz.Statement h v)
    (hG : GramDetermines.Statement h) (hK : BoundedInverseCompact.Statement h v) :
    MahlerCompactness.Statement h v := by
  intro M D t ht
  obtain ⟨n, C, hC⟩ := hB M D t ht

  let P : Set (AddSubgroup W × (Fin n → W)) := {p | IsDIntegral h D p.1 ∧
    AddSubgroup.closure (Set.range p.2) = p.1 ∧
      ∃ g : archUnitary h v, ∀ a, M.len (invApply g (vecAt v (p.2 a))) ≤ C}
  let gr : (Fin n → W) → Matrix (Fin n) (Fin n) E := fun e a b => h.toSesq (e a) (e b)
  let T : Set (Matrix (Fin n) (Fin n) E) := (fun p => gr p.2) '' P
  have hT : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ C * C})
      fun _ => Set.Finite.pi fun _ => Embeddings.finite_of_norm_le E ℂ (C * C)).subset ?_
    rintro _ ⟨p, ⟨hD, hcl, g, hg⟩, rfl⟩
    intro a _ b _
    have hmem : ∀ c, p.2 c ∈ p.1 := fun c => hcl ▸ AddSubgroup.subset_closure ⟨c, rfl⟩
    refine Set.mem_ofPred.2 ⟨(mem_integralClosure_iff ℤ E).1 (hD.integral _ (hmem a) _ (hmem b)), fun φ => ?_⟩
    have h1 := hCS M g (p.2 a) (p.2 b) (InfinitePlace.mk φ)
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply] at h1
    exact h1.trans (mul_le_mul (hg a) (hg b) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hg a)))
  have hrep : ∀ H ∈ T, ∃ p ∈ P, gr p.2 = H := fun H ⟨p, hp, hH⟩ => ⟨p, hp, hH⟩
  choose! rep hrepP hrepG using hrep
  let Kset : (Fin n → W) → Set (archUnitary h v) :=
    fun e => {g | ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C}
  refine ⟨(fun H => (rep H).1) '' T, hT.image _, ⋃ H ∈ T, Kset (rep H).2,
    hT.isCompact_biUnion fun H hH => hK M n (rep H).2 ?_ C, ?_⟩
  · obtain ⟨hD, hcl, -⟩ := hrepP H hH
    have hsp := hD.isLattice.span_eq_top
    rw [← hcl] at hsp
    rw [eq_top_iff, ← hsp]
    refine Submodule.span_le.2 fun x hx => ?_
    exact (AddSubgroup.closure_le (Submodule.span E (Set.range (rep H).2)).toAddSubgroup).2
      Submodule.subset_span hx
  · intro La g hLa hmin
    obtain ⟨e, he, heC⟩ := hC La g hLa hmin
    have hH : gr e ∈ T := ⟨(La, e), ⟨hLa, he, g, heC⟩, rfl⟩
    obtain ⟨hD', hcl', -⟩ := hrepP _ hH
    have hgr := hrepG _ hH
    obtain ⟨γ, hγ⟩ := hG n e (rep (gr e)).2 (he ▸ hLa.isLattice) (hcl' ▸ hD'.isLattice)
      fun a b => (congrFun (congrFun hgr a) b).symm
    refine ⟨γ, ⟨gr e, hH, ?_⟩, Set.mem_biUnion hH fun a => ?_⟩
    · show (rep (gr e)).1 = γ • La
      rw [← hcl', ← he, Subgroup.smul_def, AddSubgroup.pointwise_smul_def]
      erw [AddMonoidHom.map_closure]
      rw [← Set.range_comp]
      exact congrArg (fun s => AddSubgroup.closure (Set.range s)) (funext fun a => (hγ a).symm)
    · show M.len (invApply (archEmbed h v γ * g) (vecAt v ((rep (gr e)).2 a))) ≤ C
      rw [← hγ a, invApply_archEmbed_mul]
      exact heC a

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantTransport
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped MatrixOrder ComplexOrder

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MajorantTransport

theorem exists_conjTranspose_mul_self {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ X : Matrix ι ι ℂ, Xᴴ * X = P := by
  refine ⟨CFC.sqrt P, ?_⟩
  rw [(CFC.sqrt_nonneg P).posSemidef.isHermitian.eq]
  exact CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg

theorem measurePreserving_mulVec {A : Matrix ι ι ℂ} (hA : Complex.normSq A.det = 1) :
    MeasurePreserving (fun z : ι → ℂ => A *ᵥ z) volume volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := (Matrix.toLin' A).restrictScalars ℝ
  have hdet : LinearMap.det f = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hA]
  have hcoe : (⇑f) = fun z : ι → ℂ => A *ᵥ z := by
    funext z; simp [f]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (ι → ℂ)))
    (f := f) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, hcoe] at hmap
  have hm := (LinearMap.continuous_of_finiteDimensional f).measurable
  rw [hcoe] at hm
  refine ⟨hm, ?_⟩
  simpa using hmap


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem normSq_det (h : HermitianForm F E W) (v : Basis ι E W) (g : archUnitary h v)
    (w : InfinitePlace E) : Complex.normSq ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ).det = 1 := by
  have hg := mem_archUnitary.mp g.2 w
  have hH : (gramAt h v w).det ≠ 0 := by
    simp only [gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact ((isUnit_det_gram h v).map w.embedding).ne_zero
  set G : Matrix ι ι ℂ := ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
  rw [show (G.map ⇑(starRingEnd ℂ))ᵀ = Gᴴ from rfl] at hg
  have h1 := congrArg Matrix.det hg
  rw [det_mul, det_mul, det_conjTranspose, show star G.det = starRingEnd ℂ G.det from rfl] at h1
  have h2 : starRingEnd ℂ G.det * G.det = 1 := by
    apply mul_right_cancel₀ hH
    linear_combination h1
  have h3 : (Complex.normSq G.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, h2]
  exact_mod_cast h3

def sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) :
    (InfinitePlace E → ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) where
  toFun y := WithLp.toLp 2 (fun p => (Q p.1 *ᵥ y p.1) p.2)
  map_add' y z := by ext p; simp [mulVec_add]
  map_smul' c y := by ext p; simp [mulVec_smul]


omit [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem norm_sq_sqrtMap (Q : InfinitePlace E → Matrix ι ι ℂ) (y : InfinitePlace E → ι → ℂ) :
    ‖sqrtMap Q y‖ ^ 2 = ∑ w, (star (y w) ⬝ᵥ (((Q w)ᴴ * Q w) *ᵥ y w)).re := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
  simp only [sqrtMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, dotProduct, Pi.star_apply,
    Complex.re_sum, Complex.star_def, Complex.conj_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_cast


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem exists_isometry {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v) :
    ∃ (d : ℕ) (S : (InfinitePlace E → ι → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)),
      ∀ y, ‖S y‖ = M.len y := by
  choose Q hQ using fun w => exists_conjTranspose_mul_self (M.posDef w)
  have hnorm : ∀ y, ‖sqrtMap Q y‖ = M.len y := by
    intro y
    rw [Majorant.len, ← Real.sqrt_sq (norm_nonneg (sqrtMap Q y)), norm_sq_sqrtMap]
    simp only [hQ]
  have hinj : Function.Injective (sqrtMap Q) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∑ w, (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re = 0 := by
      have := norm_sq_sqrtMap Q y
      simp only [hQ, hy, norm_zero] at this
      linarith
    have hnn : ∀ w, 0 ≤ (star (y w) ⬝ᵥ (M.P w *ᵥ y w)).re := fun w =>
      (Complex.nonneg_iff.mp ((M.posDef w).posSemidef.dotProduct_mulVec_nonneg (y w))).1
    funext w
    by_contra hw
    have hpos := (Complex.lt_def.mp ((M.posDef w).dotProduct_mulVec_pos hw)).1
    have := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hnn w).mp h0 w (Finset.mem_univ _)
    simp only [Complex.zero_re] at hpos
    linarith
  have hdim : finrank ℂ (InfinitePlace E → ι → ℂ) =
      finrank ℂ (EuclideanSpace ℂ (InfinitePlace E × ι)) := by
    simp [Module.finrank_pi_fintype, finrank_euclideanSpace, Fintype.card_prod]
  let e : (InfinitePlace E → ι → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (InfinitePlace E × ι) :=
    LinearEquiv.ofBijective (sqrtMap Q)
      ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℂ (InfinitePlace E × ι))
  refine ⟨_, (e.restrictScalars ℝ).toContinuousLinearEquiv.trans b.repr.toContinuousLinearEquiv,
    fun y => ?_⟩
  simp only [ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map]
  exact hnorm y

def invApplyEquiv {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) :
    (InfinitePlace E → ι → ℂ) ≃L[ℝ] (InfinitePlace E → ι → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := invApply g
      invFun := invApply g⁻¹
      map_add' := fun y z => by funext w; simp [invApply, mulVec_add]
      map_smul' := fun c y => by funext w; simp [invApply, mulVec_smul]
      left_inv := fun y => by funext w; simp [invApply, mulVec_mulVec]
      right_inv := fun y => by funext w; simp [invApply, mulVec_mulVec] }


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem measurePreserving_invApply {h : HermitianForm F E W} {v : Basis ι E W}
    (g : archUnitary h v) : MeasurePreserving (invApply g) volume volume :=
  measurePreserving_pi (fun _ => volume) (fun _ => volume)
    (fun w => measurePreserving_mulVec (normSq_det h v g⁻¹ w))

end MajorantTransport


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem MajorantTransport.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantTransport.Statement h v := by
  intro M
  have : (volume : Measure (InfinitePlace E → ι → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨d, S, hS⟩ := MajorantTransport.exists_isometry M
  set c := Measure.addHaarScalarFactor (Measure.map S.symm volume)
    (volume : Measure (InfinitePlace E → ι → ℂ))
  have hc : Measure.map S.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul (Measure.map S.symm volume) volume
  refine ⟨d, c, fun g => ⟨(MajorantTransport.invApplyEquiv g).trans S, fun y => hS _,
    fun L _ _ => ?_⟩⟩
  set T := (MajorantTransport.invApplyEquiv g).trans S
  have hT : MeasurePreserving T.symm volume (Measure.map T.symm volume) :=
    T.symm.continuous.measurable.measurePreserving _
  rw [ZLattice.covolume_comap L (Measure.map T.symm volume) volume hT]
  have hsymm : ⇑(MajorantTransport.invApplyEquiv g).symm = invApply g⁻¹ := rfl
  have hmap : Measure.map T.symm volume = c • (volume : Measure (InfinitePlace E → ι → ℂ)) := by
    have hcomp : ⇑T.symm = (MajorantTransport.invApplyEquiv g).symm ∘ S.symm := rfl
    rw [hcomp, ← Measure.map_map (MajorantTransport.invApplyEquiv g).symm.continuous.measurable
      S.symm.continuous.measurable, hc,
      Measure.map_smul c (MajorantTransport.invApplyEquiv g).symm.continuous.measurable.aemeasurable, hsymm,
      (MajorantTransport.measurePreserving_invApply g⁻¹).map_eq]
  let b := Module.Free.chooseBasis ℤ L
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L _ (ZLattice.isAddFundamentalDomain b _),
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume), hmap, measureReal_nnreal_smul_apply]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

