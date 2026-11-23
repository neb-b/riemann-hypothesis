module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointMajorantFramesGiveMajorants
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.Count.FrameMajorant

theorem signed_cs {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ Formalism.HermitianLatticesTheory.cnorm a * Formalism.HermitianLatticesTheory.cnorm b := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have h1 : ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    simp only [Jm, Matrix.mulVec_diagonal, norm_mul, Pi.star_apply, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem cnorm_unitary {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm a := by
  have key : ∀ c : Fin n → ℂ, ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ c := by
    intro c
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have : star (u *ᵥ a) ⬝ᵥ (u *ᵥ a) = star a ⬝ᵥ a := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (this.trans (key _).symm)

theorem cnorm_inv_mul_unitary {n : ℕ} (X u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((X * u)⁻¹ *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ a) := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu, ← Matrix.mulVec_mulVec]
  apply cnorm_unitary
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hu

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  refine ⟨fun w w' h => ?_, ?_⟩
  · have hw : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases Test.embedding_cases I w with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h' : w.comap (algebraMap I.F I.E) = w'.comap (algebraMap I.F I.E) := h
    rw [hw w, hw w', h']
  · intro v
    refine ⟨InfinitePlace.mk (I.φ v), ?_⟩
    have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
    show (InfinitePlace.mk (I.φ v)).comap _ = v
    rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem frm_unit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h := congrArg (fun M => (Jm (I.ε (w.comap (algebraMap I.F I.E))) * M).det) (Test.frm_frame I x w)
  simp only [Jm_mul_self, Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at h

theorem hform_le (x : I.GA) (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤
      Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z := by
  have hc := I.cm.cmUnram.2.1
  have hX := frm_unit I x w
  have hback : ∀ y, frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => w.embedding (y i) := by
    intro y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [h1, ← hback y, ← hback z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Test.frm_frame I x w]
  exact signed_cs _ _ _

theorem normAt_mul (x : I.GA) (w : InfinitePlace I.E) (k : I.GA) (hk : ∀ v, uMat (k.1 v) ∈ Kset (I.ε v))
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  set v := w.comap (algebraMap I.F I.E) with hv
  have hu : (uMat (k.1 v))ᴴ * uMat (k.1 v) = 1 := (hk v).1.1
  have hm : uMat ((x * k).1 v) = uMat (x.1 v) * uMat (k.1 v) := rfl
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord frm
  simp only [← hv]
  split_ifs with h
  · rw [hm, ← Matrix.mul_assoc]
    exact cnorm_inv_mul_unitary _ _ hu _
  · rw [hm, ← Matrix.mul_assoc, Matrix.map_mul]
    apply cnorm_inv_mul_unitary
    have hT : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
      intro M; ext i j; simp
    rw [hT, ← Matrix.map_mul, hu]
    simp

theorem frames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  intro I x
  refine ⟨I.cm.cmUnram.1, ?_, card_places I, comap_bijective I, fun w =>
    ⟨frm_unit I x w, Test.frm_frame I x w, hform_le I x w, normAt_mul I x w⟩⟩
  rw [nPl, Fintype.card_of_bijective (comap_bijective I), card_places]

end GlobalTheory.Count.FrameMajorant
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivarianceStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autPoint_rational_equivariance : ∀ (I : AutInst) (x : I.GA) (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → lamX I (a * x) = (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ (∀ w y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (a * x)) w ((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y) ∧ least I (a * x) = least I x ∧ (∀ t, stepLe I (a * x) t = (stepLe I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) ∧ stepLt I (a * x) t = (stepLt I x t).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E))) ∧ (∀ (m : ℕ) (j : Fin m → ℕ) (τ : Fin m → ℝ), HasType I (a * x) j τ ↔ HasType I x j τ) ∧ ((x⁻¹ * a * x).2 ∈ I.Kset ↔ (lamX I x).map ((Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E)).restrictScalars (𝓞 I.E)) = lamX I x) ∧ ∀ w, (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E))) ∨ (frm I x w)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map w.embedding * frm I x w = (uMat ((x⁻¹ * a * x).1 (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.PointEquivariance.equivariance | exact GlobalTheory.PointEquivariance.equivariance | (intros; apply GlobalTheory.PointEquivariance.equivariance <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSum
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.DerFormula

variable {g : ℕ} [Fact g.Prime]

theorem isUnit_of_isUniUp {N : ℕ} {M : Mt g N} (hM : IsUniUp M) : IsUnit M := by
  have htri : M.BlockTriangular id := fun i j hij => (hM i j).1 hij
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular htri]
  simp [(hM _ _).2 rfl]

theorem card_lt_pairs (N : ℕ) : Fintype.card {p : Fin N × Fin N // p.1 < p.2} = N * (N - 1) / 2 := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have hb : ∀ b : Fin N, (∑ a : Fin N, if a < b then 1 else 0) = (b : ℕ) := by
    intro b
    rw [← Finset.card_filter, ← Fin.card_Iio b]
    congr 1
    ext a
    simp
  simp only [hb]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) N, Finset.sum_range_id]

def ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : Mt g N :=
  fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0

theorem isUniUp_ofUpper {N : ℕ} (f : {p : Fin N × Fin N // p.1 < p.2} → ZMod g) : IsUniUp (ofUpper f) := by
  intro a b
  refine ⟨fun hba => ?_, fun hab => ?_⟩
  · simp only [ofUpper, dif_neg (not_lt.mpr hba.le), if_neg hba.ne']
  · subst hab
    simp [ofUpper]

theorem card_uniUp (N : ℕ) :
    (Finset.univ.filter fun u : Gn g N => IsUniUp (u : Mt g N)).card = g ^ (N * (N - 1) / 2) := by
  rw [← Fintype.card_subtype]
  have e : {u : Gn g N // IsUniUp (u : Mt g N)} ≃ ({p : Fin N × Fin N // p.1 < p.2} → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(isUnit_of_isUniUp (isUniUp_ofUpper f)).unit, isUniUp_ofUpper f⟩
      left_inv := by
        rintro ⟨u, hu⟩
        apply Subtype.ext
        apply Units.ext
        dsimp only
        rw [IsUnit.unit_spec]
        funext a b
        show ofUpper _ a b = (u : Mt g N) a b
        rcases lt_trichotomy a b with hab | rfl | hab
        · simp only [ofUpper, dif_pos hab]
        · simp only [ofUpper, dif_neg (lt_irrefl a)]
          exact ((hu a a).2 rfl).symm
        · simp only [ofUpper, dif_neg (not_lt.mpr hab.le), if_neg hab.ne']
          exact ((hu a b).1 hab).symm
      right_inv := by
        intro f
        funext p
        dsimp only
        rw [IsUnit.unit_spec]
        show ofUpper f p.1.1 p.1.2 = f p
        simp only [ofUpper, dif_pos p.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, card_lt_pairs]

theorem eU_coeff (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (u : Gn g N) :
    (eU g N ψ).coeff u = if IsUniUp (u : Mt g N) then
      ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ * (ψ (∑ i ∈ Finset.range (N - 1), entN (u : Mt g N) i (i + 1)))⁻¹ else 0 := by
  unfold eU eDat
  rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and, card_uniUp, Nat.cast_pow, smul_eq_mul]
  split_ifs <;> simp

theorem sum_br (i n : ℕ) (M : Mt g n) :
    ∑ j ∈ Finset.range (n - i - 1), entN (br i (n - i) M) j (j + 1) = supFrom i M := by
  unfold supFrom
  rw [Finset.sum_Ico_eq_sum_range, show n - 1 - i = n - i - 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have h1 : j < n - i := by omega
  have h2 : j + 1 < n - i := by omega
  have hbr : entN (br i (n - i) M) j (j + 1) = entN M (i + j) (i + (j + 1)) := by
    conv_lhs => unfold entN
    rw [dif_pos ⟨h1, h2⟩]
    rfl
  rw [hbr, add_assoc]

end GlobalTheory.GLm.DerFormula

namespace GlobalTheory.GLm

open DerFormula

theorem der_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ) (h : Gn g i), i ≤ n → der ψ i F h = ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * ∑ x : Gn g n, if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
  intro g _ ψ i n F h _
  have key : ∀ x : Gn g n, (∑ v : Gn g (n - i),
      (if IsUniUp (v : Mt g (n - i)) then
        (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
      (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
          br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0)) =
      if InR i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) then
        F x * (ψ (supFrom i (x : Mt g n)))⁻¹ else 0 := by
    intro x
    unfold InR
    by_cases hx : (InPar i (x : Mt g n) ∧ IsUniUp (br i (n - i) (x : Mt g n))) ∧
        tl i (x : Mt g n) = (h : Mt g i)
    · obtain ⟨⟨hP, hU⟩, ht⟩ := hx
      have hv0 : ((isUnit_of_isUniUp hU).unit : Mt g (n - i)) = br i (n - i) (x : Mt g n) :=
        IsUnit.unit_spec _
      rw [Finset.sum_eq_single (isUnit_of_isUniUp hU).unit]
      · rw [if_pos (by rw [hv0]; exact hU), if_pos ⟨hP, ht, hv0.symm⟩, if_pos ⟨⟨hP, hU⟩, ht⟩, hv0, sum_br,
          mul_comm]
      · intro v _ hv
        refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨-, -, hb⟩
        exact hv (Units.ext (hb.symm.trans hv0.symm))
      · intro hv
        exact absurd (Finset.mem_univ _) hv
    · rw [if_neg hx]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : IsUniUp (v : Mt g (n - i))
      · refine mul_eq_zero_of_right _ (if_neg ?_)
        rintro ⟨hP, ht, hb⟩
        exact hx ⟨⟨hP, by rw [hb]; exact hv⟩, ht⟩
      · rw [if_neg hv, zero_mul]
  simp only [der, wh, tr, res, eU_coeff]
  calc _ = ∑ v : Gn g (n - i), ((g : ℂ) ^ (i * (n - i)))⁻¹ * ((g : ℂ) ^ ((n - i) * (n - i - 1) / 2))⁻¹ *
        ∑ x : Gn g n, (if IsUniUp (v : Mt g (n - i)) then
          (ψ (∑ j ∈ Finset.range (n - i - 1), entN (v : Mt g (n - i)) j (j + 1)))⁻¹ else 0) *
          (if InPar i (x : Mt g n) ∧ tl i (x : Mt g n) = (h : Mt g i) ∧
            br i (n - i) (x : Mt g n) = (v : Mt g (n - i)) then F x else 0) := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum]
        split_ifs <;> ring
    _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [key]
        rw [pow_add, mul_inv]

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonalityStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelEqOnOfContinuousOnAeEqStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq : ∀ (k r : ℕ) {B : Type} [NormedAddCommGroup B] (μG : Measure (Mt k r)) (f g : Mat k r → B), IsHaarOn (GG k r) μG → ContinuousOn f (GG k r) → ContinuousOn g (GG k r) → (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] (fun x => g (Matrix.of x)) → ∀ x ∈ GG k r, f x = g x := by
  first | exact @GlobalTheory.SgInf.AeqCont.eqOn_of_ae | exact GlobalTheory.SgInf.AeqCont.eqOn_of_ae | (intros; apply GlobalTheory.SgInf.AeqCont.eqOn_of_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselZhatInvAndRegularIffStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselZhat_inv_and_regular_iff : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r), γ ∈ GG k r → Zhat k r z' z γ⁻¹ = (Zhat k r z z' γ)ᴴ ∧ (γ ∈ Greg k r z z' ↔ γ⁻¹ ∈ Greg k r z' z) := by
  first | exact @GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | exact GlobalTheory.SgInf.RegInv.zhat_inv_and_reg | (intros; apply GlobalTheory.SgInf.RegInv.zhat_inv_and_reg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParBasic

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem tl_apply (M : Mt g (a + b)) (i j : Fin a) : tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply (M : Mt g (a + b)) (i j : Fin b) : br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

def blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def ur (a b : ℕ) (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

theorem tl_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : tl a (blkM A B D) = A := by
  ext i j; simp [tl_apply, blkM]

theorem br_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : br a b (blkM A B D) = D := by
  ext i j; simp [br_apply, blkM]

theorem ur_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : ur a b (blkM A B D) = B := by
  ext i j; simp [ur, blkM]

theorem inPar_iff (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have := h ⟨i - a, by omega⟩ ⟨j, hj⟩
    convert this using 2 <;> ext <;> simp
    omega

theorem inPar_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : InPar a (blkM A B D) := by
  rw [inPar_iff]
  intro i j; simp [blkM]

theorem blkM_eq {M : Mt g (a + b)} (h : InPar a M) : blkM (tl a M) (ur a b M) (br a b M) = M := by
  rw [inPar_iff] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkM, tl_apply, br_apply, ur, h]

theorem det_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (blkM A B D).det = A.det * D.det := by
  rw [blkM, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem isUnit_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    IsUnit (blkM A B D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [Matrix.isUnit_iff_isUnit_det, det_blkM, IsUnit.mul_iff]

theorem blkM_mul (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    blkM A B D * blkM A' B' D' = blkM (A * A') (A * B' + B * D') (D * D') := by
  rw [blkM, blkM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [blkM]

theorem isUnit_blocks (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    IsUnit (tl a (x : Mt g (a + b))) ∧ IsUnit (br a b (x : Mt g (a + b))) := by
  rw [← isUnit_blkM _ (ur a b x.val), blkM_eq h]
  exact x.isUnit

theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := blkM_mul (tl a x) (tl a y) (ur a b x) (ur a b y) (br a b x) (br a b y)
  rw [blkM_eq hx, blkM_eq hy] at e
  rw [e]
  exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩

theorem exists_subgroup {G : Type} [Group G] [Finite G] (p : G → Prop) (h1 : p 1)
    (hm : ∀ x y, p x → p y → p (x * y)) : ∃ P : Subgroup G, ∀ x, x ∈ P ↔ p x := by
  have hp : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := fun x hx k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hm _ _ ih hx
  refine ⟨{ carrier := {x | p x}, mul_mem' := fun {x y} => hm x y, one_mem' := h1, inv_mem' := fun {x} hx => ?_ },
    fun x => Iff.rfl⟩
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    have h0 := orderOf_pos x
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  change p x⁻¹
  rw [this]
  exact hp x hx _

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j hj hi =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem card_fibre (h₁ : Gn g a) (h₂ : Gn g b) :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b)) ∧
      tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)).card = g ^ (a * b) := by
  have hc : (Finset.univ : Finset (Matrix (Fin a) (Fin b) (ZMod g))).card = g ^ (a * b) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin b → ZMod g) = _
    simp [pow_mul']
  rw [← hc]
  refine Finset.card_bij (fun x _ => ur a b x.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x hx y hy h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply Units.ext
    rw [← blkM_eq hx.1, ← blkM_eq hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, h]
  · intro B _
    have hu := (isUnit_blkM h₁.val B h₂.val).2 ⟨h₁.isUnit, h₂.isUnit⟩
    refine ⟨hu.unit, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsUnit.unit_spec]
      exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩
    · simp only [IsUnit.unit_spec, ur_blkM]

theorem toG_val {n : ℕ} {M : Mt g n} (h : IsUnit M) : (toG M).val = M := by
  rw [toG, dif_pos h, IsUnit.unit_spec]

theorem card_par :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b))).card =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Gn g a × Gn g b)))
    (f := fun x : Gn g (a + b) => (toG (tl a x.val), toG (br a b x.val))) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (g := fun _ => g ^ (a * b))]
  · simp
  · rintro ⟨h₁, h₂⟩ _
    rw [← card_fibre h₁ h₂, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => and_congr_right fun hx => ?_
    have hu := isUnit_blocks x hx
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := fun _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem isUniUp_mul {n : ℕ} (x y : Mt g n) (hx : IsUniUp x) (hy : IsUniUp y) : IsUniUp (x * y) := by
  intro i j
  refine ⟨fun h => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hx i k).1 hk, zero_mul]
    · rw [(hy k j).1 (h.trans_le (not_lt.1 hk)), mul_zero]
  · rintro rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single i, (hx i i).2 rfl, (hy i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hx i k).1 h, zero_mul]
      · rw [(hy k i).1 h, mul_zero]
    · simp

theorem par_basic : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  intro g _ a b n hn
  subst hn
  exact ⟨exists_subgroup _ (inPar_one _ _) fun x y hx hy => (blocks_mul _ _ hx hy).1,
    exists_subgroup _ (isUniUp_one _) fun x y hx hy => isUniUp_mul _ _ hx hy,
    isUnit_blocks, fun x y hx hy => (blocks_mul x y hx hy).2, card_fibre, card_par⟩

end GlobalTheory.GLm.ParBasic
end

