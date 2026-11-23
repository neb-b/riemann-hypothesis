module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviMatrices
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0021
public import GroundTheory.AutomorphicForms.HermitianOrthogonal
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviPlaces
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def colMat (v : Basis ι E W) {κ : Type*} (u : κ → W) (w : InfinitePlace E) : Matrix ι κ ℂ :=
  Matrix.of fun i k => vecAt v (u k) w i

theorem vecAt_add (v : Basis ι E W) (x y : W) (w : InfinitePlace E) :
    vecAt v (x + y) w = vecAt v x w + vecAt v y w := by
  funext i; simp [vecAt]

theorem vecAt_smul (v : Basis ι E W) (a : E) (x : W) (w : InfinitePlace E) :
    vecAt v (a • x) w = w.embedding a • vecAt v x w := by
  funext i; simp [vecAt]

theorem vecAt_basis (v : Basis ι E W) (i : ι) (w : InfinitePlace E) :
    vecAt v (v i) w = Pi.single i 1 := by
  funext j; simp [vecAt, Finsupp.single_apply, Pi.single_apply, eq_comm]

theorem vecAt_sum_smul (v : Basis ι E W) {κ : Type*} [Fintype κ] (c : κ → E) (u : κ → W)
    (w : InfinitePlace E) :
    vecAt v (∑ k, c k • u k) w = colMat v u w *ᵥ fun k => w.embedding (c k) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [vecAt, colMat, mulVec, dotProduct, map_sum, mul_comm]

theorem vecAt_coe {W' : Submodule E W} {n : ℕ} (v : Basis ι E W) (v' : Basis (Fin n) E W') (x : W')
    (w : InfinitePlace E) :
    vecAt v (x : W) w = colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' x w := by
  conv_lhs => rw [← v'.sum_repr x]
  rw [Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  exact vecAt_sum_smul v _ _ w

theorem conjTranspose_mulVec_colMat (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := rfl

theorem conjT_eq {m n : Type*} (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ))ᵀ = Mᴴ := by
  ext i j
  simp [conjTranspose_apply]

theorem archEmbed_apply (h : HermitianForm F E W) (v : Basis ι E W) (γ : h.unitaryGroup)
    (w : InfinitePlace E) :
    (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
      (LinearMap.toMatrix v v ((γ : W ≃ₗ[E] W) : W →ₗ[E] W)).map w.embedding := by
  rw [← unitaryGroupEquivMatrix_apply]
  rfl

theorem map_toMatrix_mulVec_vecAt (v : Basis ι E W) (f : W →ₗ[E] W) (x : W)
    (w : InfinitePlace E) :
    (LinearMap.toMatrix v v f).map w.embedding *ᵥ vecAt v x w = vecAt v (f x) w := by
  funext i
  change _ = w.embedding (v.repr (f x) i)
  rw [← LinearMap.toMatrix_mulVec_repr v v, RingHom.map_mulVec]
  rfl

variable {h : HermitianForm F E W} {x₀ w₀ : W} {n : ℕ}

theorem gramAt_complement (v : Basis ι E W) (h' : HermitianForm F E (hypComplement h x₀ w₀))
    (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) (v' : Basis (Fin n) E (hypComplement h x₀ w₀))
    (w : InfinitePlace E) :
    gramAt h' v' w = (colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w := by
  ext k l
  have e := sesq_mul (gramAt h v w) (colMat v (fun k => (v' k : W)) w)
    (colMat v (fun k => (v' k : W)) w) (Pi.single k 1) (Pi.single l 1)
  rw [← vecAt_basis v' k w, ← vecAt_basis v' l w, ← vecAt_coe, ← vecAt_coe,
    ← HermAtPlace.proof, ← hh', vecAt_basis, vecAt_basis] at e
  change w.embedding (h'.toSesq (v' k) (v' l)) = _
  rw [← e]
  simp [dotProduct, Pi.single_apply]

theorem frame (v : Basis ι E W) (hp : IsHyperbolicPair h x₀ w₀)
    (h' : HermitianForm F E (hypComplement h x₀ w₀)) (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y)
    (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    (gramAt h v w)ᴴ = gramAt h v w ∧
    IsUnit ((colMat v (fun k => (v' k : W)) w)ᴴ * gramAt h v w *
      colMat v (fun k => (v' k : W)) w).det ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    (colMat v (fun k => (v' k : W)) w)ᴴ *ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v x₀ w) = 0 ∧
    star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 0 ∧
    star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ vecAt v w₀ w) = 1 ∧
    ∀ z, ∃ (a b : ℂ) (c : Fin n → ℂ), z = a • vecAt v x₀ w + b • vecAt v w₀ w +
      colMat v (fun k => (v' k : W)) w *ᵥ c := by
  refine ⟨(GramAtData.proof h v w).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← gramAt_complement v h' hh' v' w]
    exact (GramAtData.proof h' v' w).2
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).1, map_zero]
  · funext k
    rw [conjTranspose_mulVec_colMat, ← HermAtPlace.proof, Pi.zero_apply,
      ComplementExtension.toSesq_swap_eq_zero (mem_hypComplement.1 (v' k).2).2, map_zero]
  · rw [← HermAtPlace.proof, hp.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.1, map_zero]
  · rw [← HermAtPlace.proof, hp.2.2, map_one]
  · have hx : ∀ x : W, vecAt v x w = w.embedding (h.toSesq w₀ x) • vecAt v x₀ w +
        w.embedding (h.toSesq x₀ x) • vecAt v w₀ w +
        colMat v (fun k => (v' k : W)) w *ᵥ vecAt v' (ComplementExtension.proj hp x) w := by
      intro x
      conv_lhs => rw [← ComplementExtension.split hp x]
      rw [vecAt_add, vecAt_add, vecAt_smul, vecAt_smul, vecAt_coe v v']
      abel
    intro z
    have hz : z = ∑ i, z i • vecAt v (v i) w := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, vecAt_basis, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    refine ⟨∑ i, z i * w.embedding (h.toSesq w₀ (v i)), ∑ i, z i * w.embedding (h.toSesq x₀ (v i)),
      ∑ i, z i • vecAt v' (ComplementExtension.proj hp (v i)) w, ?_⟩
    have hx' : ∀ i, vecAt v (v i) w = _ := fun i => hx (v i)
    conv_lhs => rw [hz]
    simp only [hx', smul_add, Finset.sum_add_distrib, Finset.sum_smul, smul_smul, mulVec_sum,
      mulVec_smul]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusEmbedding
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

namespace TorusEmbedding

section Linear

variable {ι : Type*} [Fintype ι]

def pair (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)

variable {H : Matrix ι ι ℂ} {X Y : ι → ℂ}

theorem pair_add (u z z' : ι → ℂ) : pair H u (z + z') = pair H u z + pair H u z' := by
  simp [pair, mulVec_add, dotProduct_add]

theorem pair_smul (u z : ι → ℂ) (c : ℂ) : pair H u (c • z) = c * pair H u z := by
  simp [pair, mulVec_smul, dotProduct_smul]

theorem add_pair (u u' z : ι → ℂ) : pair H (u + u') z = pair H u z + pair H u' z := by
  simp [pair, add_dotProduct]

theorem smul_pair (u z : ι → ℂ) (c : ℂ) : pair H (c • u) z = starRingEnd ℂ c * pair H u z := by
  simp [pair, star_smul, smul_dotProduct]

theorem pair_swap (hH : H.IsHermitian) (u z : ι → ℂ) :
    pair H u z = starRingEnd ℂ (pair H z u) := by
  rw [pair, pair, dotProduct_mulVec, ← RCLike.star_def, ← star_dotProduct_star, star_star,
    star_mulVec, hH.eq]

variable [DecidableEq ι]

def torusMat (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (s t : ℂ) : Matrix ι ι ℂ :=
  1 + (s - 1) • vecMulVec X (star Y ᵥ* H) + (t - 1) • vecMulVec Y (star X ᵥ* H)

theorem torusMat_mulVec (s t : ℂ) (z : ι → ℂ) :
    torusMat H X Y s t *ᵥ z = z + ((s - 1) * pair H Y z) • X + ((t - 1) * pair H X z) • Y := by
  simp only [torusMat, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, pair,
    dotProduct_mulVec, op_smul_eq_smul, smul_smul]

theorem torusMat_one_one : torusMat H X Y 1 1 = 1 := by
  simp [torusMat]

theorem pair_Y_torusMat (hYY : pair H Y Y = 0) (hYX : pair H Y X = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H Y (torusMat H X Y s t *ᵥ z) = s * pair H Y z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hYX, hYY]; ring

theorem pair_X_torusMat (hXX : pair H X X = 0) (hXY : pair H X Y = 1) (s t : ℂ) (z : ι → ℂ) :
    pair H X (torusMat H X Y s t *ᵥ z) = t * pair H X z := by
  rw [torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul, hXX, hXY]; ring

theorem torusMat_mul (hXX : pair H X X = 0) (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1)
    (hYX : pair H Y X = 1) (s t s' t' : ℂ) :
    torusMat H X Y s t * torusMat H X Y s' t' = torusMat H X Y (s * s') (t * t') := by
  refine mulVec_injective (funext fun z => ?_)
  rw [← mulVec_mulVec, torusMat_mulVec s t, pair_Y_torusMat hYY hYX, pair_X_torusMat hXX hXY,
    torusMat_mulVec s' t', torusMat_mulVec]
  module

theorem torusMat_mulVec_X (hXX : pair H X X = 0) (hYX : pair H Y X = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ X = s • X := by
  rw [torusMat_mulVec, hYX, hXX]; module

theorem torusMat_mulVec_Y (hYY : pair H Y Y = 0) (hXY : pair H X Y = 1) (s t : ℂ) :
    torusMat H X Y s t *ᵥ Y = t • Y := by
  rw [torusMat_mulVec, hYY, hXY]; module

theorem torusMat_mulVec_orth (s t : ℂ) (z : ι → ℂ) (hX : pair H X z = 0) (hY : pair H Y z = 0) :
    torusMat H X Y s t *ᵥ z = z := by
  rw [torusMat_mulVec, hX, hY]; simp

theorem torusMat_unitary (hH : H.IsHermitian) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (s t : ℂ) (hst : starRingEnd ℂ s * t = 1) :
    (torusMat H X Y s t)ᴴ * H * torusMat H X Y s t = H := by
  have hts : starRingEnd ℂ t * s = 1 := by
    have := congrArg (starRingEnd ℂ) hst
    simpa [mul_comm] using this
  have key : ∀ u z : ι → ℂ, pair H (torusMat H X Y s t *ᵥ u) (torusMat H X Y s t *ᵥ z) =
      pair H u z := by
    intro u z
    conv_lhs => rw [torusMat_mulVec s t u]
    rw [add_pair, add_pair, smul_pair, smul_pair, pair_Y_torusMat hYY hYX,
      pair_X_torusMat hXX hXY, torusMat_mulVec, pair_add, pair_add, pair_smul, pair_smul,
      pair_swap hH u X, pair_swap hH u Y]
    simp only [map_mul, map_sub, map_one]
    linear_combination (pair H X z * starRingEnd ℂ (pair H Y u)) * hst +
      (pair H Y z * starRingEnd ℂ (pair H X u)) * hts
  refine mulVec_injective (funext fun z => ?_)
  refine dotProduct_eq _ _ fun u => ?_
  rw [dotProduct_comm, dotProduct_comm (H *ᵥ z)]
  have := key (star u) z
  simp only [pair, star_star] at this
  rw [← this, star_mulVec, star_star]
  simp only [dotProduct_mulVec, vecMul_vecMul]

def torusGL (H : Matrix ι ι ℂ) (X Y : ι → ℂ) (hXX : pair H X X = 0) (hYY : pair H Y Y = 0)
    (hXY : pair H X Y = 1) (hYX : pair H Y X = 1) (a : ℂˣ) : GL ι ℂ where
  val := torusMat H X Y a (starRingEnd ℂ ↑a⁻¹)
  inv := torusMat H X Y ↑a⁻¹ (starRingEnd ℂ a)
  val_inv := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.mul_inv, ← map_mul, Units.inv_mul, map_one,
      torusMat_one_one]
  inv_val := by
    rw [torusMat_mul hXX hYY hXY hYX, Units.inv_mul, ← map_mul, Units.mul_inv, map_one,
      torusMat_one_one]

end Linear

section Places

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W}


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem place_pairs (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
    (hp : IsHyperbolicPair h x₀ w₀) (w : InfinitePlace E) :
    pair (gramAt h v w) (vecAt v x₀ w) (vecAt v x₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v w₀ w) = 0 ∧
      pair (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) = 1 ∧
      pair (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
  obtain ⟨hxx, hww, hxw⟩ := hp
  have e : ∀ x y, pair (gramAt h v w) (vecAt v x w) (vecAt v y w) = w.embedding (h.toSesq x y) :=
    fun x y => (h1 w x y).symm
  refine ⟨by rw [e, hxx, map_zero], by rw [e, hww, map_zero], by rw [e, hxw, map_one], ?_⟩
  rw [pair_swap (h2 w).1, e, hxw, map_one, map_one]

variable (h1 : HermAtPlace.Statement h v) (h2 : GramAtData.Statement h v) {x₀ w₀ : W}
  (hp : IsHyperbolicPair h x₀ w₀)

def torusAt (w : InfinitePlace E) (a : ℂˣ) : GL ι ℂ :=
  torusGL (gramAt h v w) (vecAt v x₀ w) (vecAt v w₀ w) (place_pairs h1 h2 hp w).1
    (place_pairs h1 h2 hp w).2.1 (place_pairs h1 h2 hp w).2.2.1 (place_pairs h1 h2 hp w).2.2.2 a

omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem torusAt_mem (a : InfinitePlace E → ℂˣ) :
    (fun w => torusAt h1 h2 hp w (a w)) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  have hc : ∀ M : Matrix ι ι ℂ, (M.map (starRingEnd ℂ))ᵀ = Mᴴ := fun M => by
    ext i j; simp [conjTranspose_apply]
  rw [hc]
  refine torusMat_unitary (h2 w).1 hXX hYY hXY hYX _ _ ?_
  rw [← map_mul, Units.mul_inv, map_one]

def torusHom : (InfinitePlace E → ℂˣ) →* archUnitary h v where
  toFun a := ⟨fun w => torusAt h1 h2 hp w (a w), torusAt_mem h1 h2 hp a⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (by
    simp [torusAt, torusGL, torusMat_one_one]))
  map_mul' a b := Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
    simp only [torusAt, torusGL, Subgroup.coe_mul, Pi.mul_apply, Units.val_mul]
    rw [torusMat_mul hXX hYY hXY hYX, ← map_mul, ← Units.val_mul, ← Units.val_mul,
      ← _root_.mul_inv_rev, mul_comm (b w)]))

theorem continuous_torusHom : Continuous (torusHom h1 h2 hp) := by
  refine Continuous.subtype_mk (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) (a w : ℂ) (starRingEnd ℂ ↑(a w)⁻¹)
    unfold torusMat
    fun_prop
  · change Continuous fun a : InfinitePlace E → ℂˣ => torusMat (gramAt h v w) (vecAt v x₀ w)
      (vecAt v w₀ w) ↑(a w)⁻¹ (starRingEnd ℂ (a w : ℂ))
    unfold torusMat
    fun_prop

end Places

section Main

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem proof (h : HermitianForm F E W) (v : Basis ι E W) (h1 : HermAtPlace.Statement h v)
    (h2 : GramAtData.Statement h v) : TorusEmbedding.Statement h v := by
  intro x₀ w₀ hp
  refine ⟨torusHom h1 h2 hp, continuous_torusHom h1 h2 hp, fun a w => ?_⟩
  obtain ⟨hXX, hYY, hXY, hYX⟩ := place_pairs h1 h2 hp w
  refine ⟨torusMat_mulVec_X hXX hYX _ _, ?_, fun z hX hY => torusMat_mulVec_orth _ _ z hX hY⟩
  change torusMat _ _ _ _ _ *ᵥ _ = _
  rw [torusMat_mulVec_Y hYY hXY, Units.val_inv_eq_inv_val, map_inv₀]

end Main

end TorusEmbedding

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentCoordProper
section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

namespace UnipotentCoordProper

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unipVec (H : Matrix ι ι ℂ) (X W₀ u e : ι → ℂ) : ι → ℂ :=
  e + (star X ⬝ᵥ (H *ᵥ e)) • u - (star u ⬝ᵥ (H *ᵥ (e - (star X ⬝ᵥ (H *ᵥ e)) • W₀))) • X

def unipMat (H : Matrix ι ι ℂ) (X W₀ u : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => unipVec H X W₀ u (Pi.single j 1) i

theorem continuous_unipMat (H : Matrix ι ι ℂ) (X W₀ : ι → ℂ) :
    Continuous (unipMat H X W₀) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hc : Continuous fun u => unipVec H X W₀ u (Pi.single j 1) := by
    unfold unipVec
    apply Continuous.sub
    · exact continuous_const.add (continuous_const_smul _)
    · exact (continuous_star.dotProduct continuous_const).smul continuous_const
  exact (continuous_apply i).comp hc

theorem eq_unipMat {H G : Matrix ι ι ℂ} {X W₀ : ι → ℂ} (hU : Gᴴ * H * G = H)
    (hX : G *ᵥ X = X) (hz : ∀ z, star X ⬝ᵥ (H *ᵥ z) = 0 → ∃ c : ℂ, G *ᵥ z = z + c • X)
    (hXW : star X ⬝ᵥ (H *ᵥ W₀) = 1) (hWX : star W₀ ⬝ᵥ (H *ᵥ X) = 1) :
    G = unipMat H X W₀ (G *ᵥ W₀ - W₀) := by
  have ip : ∀ a b, star (G *ᵥ a) ⬝ᵥ (H *ᵥ (G *ᵥ b)) = star a ⬝ᵥ (H *ᵥ b) := by
    intro a b
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hU]
  set u := G *ᵥ W₀ - W₀ with hu
  have huX : star u ⬝ᵥ (H *ᵥ X) = 0 := by
    have := ip W₀ X
    rw [hX] at this
    simp only [hu, star_sub, sub_dotProduct, this, sub_self]
  have key : ∀ e, G *ᵥ e = unipVec H X W₀ u e := by
    intro e
    set b := star X ⬝ᵥ (H *ᵥ e) with hb
    set z := e - b • W₀ with hzdef
    have hXz : star X ⬝ᵥ (H *ᵥ z) = 0 := by
      simp only [hzdef, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hXW, smul_eq_mul,
        mul_one, b, sub_self]
    obtain ⟨c, hc⟩ := hz z hXz
    have hGW : G *ᵥ W₀ = W₀ + u := by rw [hu]; abel
    have hc' : c = -(star u ⬝ᵥ (H *ᵥ z)) := by
      have := ip W₀ z
      rw [hc, hGW] at this
      simp only [star_add, add_dotProduct, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
        hWX, huX, smul_eq_mul] at this
      linear_combination this
    have he : e = z + b • W₀ := by rw [hzdef]; abel
    have : G *ᵥ e = z + c • X + b • (W₀ + u) := by
      rw [he, mulVec_add, mulVec_smul, hc, hGW]
    rw [this, hc']
    simp only [unipVec, ← hb, ← hzdef]
    rw [he]
    simp only [smul_add, neg_smul]
    abel
  ext i j
  rw [unipMat, of_apply, ← key, mulVec_single_one, col_apply]

end UnipotentCoordProper

open UnipotentCoordProper

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipotentCoordProper.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentCoordProper.Statement h v := by
  intro x₀ w₀ hp K hK
  have hherm := HermAtPlace.proof h v
  set H := gramAt h v
  set X := vecAt v x₀
  set W0 := vecAt v w₀
  have hXW : ∀ w, star (X w) ⬝ᵥ (H w *ᵥ W0 w) = 1 := fun w => by
    rw [← hherm, hp.2.2, map_one]
  have hWX : ∀ w, star (W0 w) ⬝ᵥ (H w *ᵥ X w) = 1 := fun w => by
    rw [← hherm, ← h.conj_toSesq, hp.2.2, map_one, map_one]
  have hHdet : ∀ w, IsUnit (H w).det := fun w => by
    simp only [H, gramAt]
    rw [show ((gram h.toSesq v).map w.embedding).det = w.embedding (gram h.toSesq v).det from
      (RingHom.map_det w.embedding _).symm]
    exact (isUnit_det_gram h v).map w.embedding
  set Φ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w => unipMat (H w) (X w) (W0 w)
  set Ψ : InfinitePlace E → (ι → ℂ) → Matrix ι ι ℂ := fun w u => (H w)⁻¹ * (Φ w u)ᴴ * H w
  have hΦc : ∀ w, Continuous (Φ w) := fun w => continuous_unipMat _ _ _
  have hΨc : ∀ w, Continuous (Ψ w) := fun w =>
    (continuous_const.matrix_mul (hΦc w).matrix_conjTranspose).matrix_mul continuous_const
  have key : ∀ (n : unipRadical h v x₀) (w : InfinitePlace E),
      (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) =
        Φ w (unipCoord h v x₀ w₀ n w) ∧
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) =
        Ψ w (unipCoord h v x₀ w₀ n w) := by
    intro n w
    set G : Matrix ι ι ℂ := (((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
    have hU : Gᴴ * H w * G = H w := (mem_archUnitary.mp (n : archUnitary h v).2) w
    have hG : G = Φ w (unipCoord h v x₀ w₀ n w) :=
      eq_unipMat hU ((n.2 w).1) ((n.2 w).2) (hXW w) (hWX w)
    refine ⟨hG, ?_⟩
    set Gi : Matrix ι ι ℂ :=
      (((((n : archUnitary h v) : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ)
    have hGGi : G * Gi = 1 := Units.mul_inv _
    show Gi = (H w)⁻¹ * (Φ w (unipCoord h v x₀ w₀ n w))ᴴ * H w
    rw [← hG]
    calc Gi = (H w)⁻¹ * (Gᴴ * H w * G) * Gi := by
          rw [hU, Matrix.nonsing_inv_mul _ (hHdet w), Matrix.one_mul]
      _ = (H w)⁻¹ * Gᴴ * H w * (G * Gi) := by simp only [Matrix.mul_assoc]
      _ = (H w)⁻¹ * Gᴴ * H w := by rw [hGGi, Matrix.mul_one]
  set Kw : InfinitePlace E → Set (ι → ℂ) := fun w => (fun y => y w) '' K
  have hKw : ∀ w, IsCompact (Kw w) := fun w => hK.image (continuous_apply w)
  set C : InfinitePlace E → Set (GL ι ℂ) := fun w => Units.embedProduct (Matrix ι ι ℂ) ⁻¹'
    ((Φ w '' Kw w) ×ˢ (MulOpposite.unop ⁻¹' (Ψ w '' Kw w)))
  have hC : ∀ w, IsCompact (C w) := fun w =>
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (((hKw w).image (hΦc w)).prod
        (MulOpposite.opHomeomorph.isCompact_preimage.mp ((hKw w).image (hΨc w))))
  have hS : IsClosed {n : unipRadical h v x₀ | unipCoord h v x₀ w₀ n ∈ K} :=
    hK.isClosed.preimage (continuous_unipCoord h v x₀ w₀)
  rw [Subtype.isCompact_iff, Subtype.isCompact_iff, Set.image_image]
  refine (isCompact_univ_pi hC).of_isClosed_subset ?_ ?_
  · rw [← Set.image_image]
    exact (isClosed_archUnitary h v).isClosedEmbedding_subtypeVal.isClosedMap _
      ((isClosed_unipRadical h v x₀).isClosedEmbedding_subtypeVal.isClosedMap _ hS)
  · rintro _ ⟨n, hn, rfl⟩ w -
    exact ⟨⟨_, ⟨_, hn, rfl⟩, (key n w).1.symm⟩, ⟨_, ⟨_, hn, rfl⟩, (key n w).2.symm⟩⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

