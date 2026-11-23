module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliser
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColRootsExistsPrimitiveRoots
section
open Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory

theorem colRoots_mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A}
    {P : HeightOneSpectrum A} (h : P ∈ divs a) : a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hfin
  · exact (Set.Finite.mem_toFinset hfin).mp h
  · exact absurd h (Finset.notMem_empty P)

theorem colRoots_exists_primitiveRoots (X : Fields) (Pr : Primes X) (m : ℕ) (Ch : Chars X Pr m)
    (hf : 0 < X.f) (hP : Pr.Ok) (hC : Ch.Ok) (i : Fin 2) :
    (∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i)) ∧ ∃ ζ : X.K, IsPrimitiveRoot ζ (Pr.g i - 1) := by
  refine ⟨?_, ?_⟩
  · have hcard : 0 < (Pr.vG i).card := by rw [hP.vG_card i]; exact hf
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hcard
    have hwG : w ∈ Pr.vGs := by
      classical
      rw [Primes.vGs, Finset.mem_union]
      fin_cases i
      · exact Or.inl hw
      · exact Or.inr hw
    have hconj : X.conjO (Pr.piG i) ∈ w.asIdeal := colRoots_mem_of_mem_divs hw
    have hg : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
      rw [← hP.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hconj
    have hzero : ((Pr.g i : ℕ) : 𝓞 X.E ⧸ w.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk w.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hg
    exact exists_isPrimitiveRoot_of_addChar_ne_one (𝓞 X.E ⧸ w.asIdeal) X.K (Pr.g i)
      (hP.g_prime i) hzero (Ch.psi0 ⟨w, hwG⟩) (hC.psi_zero_nontrivial_character _)
  · obtain ⟨om, hom, -⟩ := hC.chi_om i
    exact exists_isPrimitiveRoot_of_injective_character X.K (Pr.g i) (hP.g_prime i) om hom

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsTangentBorelSectionQuadric
section
noncomputable section

namespace GlobalTheory.TangentSection

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
  GlobalTheory.CompactDualQuot GlobalTheory.QuadricSection

variable {P Q P' Q' : ℕ}

theorem jpq_eq_diagonal (P Q : ℕ) :
    Formalism.UG.Jpq P Q = diagonal fun i : Fin P ⊕ Fin Q => ((sg i : ℝ) : ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Formalism.UG.Jpq, sg, diagonal_apply, Matrix.one_apply]
  all_goals split_ifs <;> simp

theorem norm_sg (i : Fin P ⊕ Fin Q) : ‖((sg i : ℝ) : ℂ)‖ = 1 := by
  rcases sg_eq i with h | h <;> rw [h] <;> simp

def flipAt (k : Fin P ⊕ Fin Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  diagonal fun i => if i = k then 1 else -1

theorem flipAt_unitary (k : Fin P ⊕ Fin Q) :
    (flipAt k)ᴴ * Formalism.UG.Jpq P Q * flipAt k = Formalism.UG.Jpq P Q := by
  rw [jpq_eq_diagonal, flipAt, diagonal_conjTranspose, diagonal_mul_diagonal,
    diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = k <;> simp [h]

theorem flipAt_mulVec (k : Fin P ⊕ Fin Q) :
    flipAt k *ᵥ (Pi.single k 1 : Sp P Q) = Pi.single k 1 := by
  funext i
  rw [flipAt, mulVec_diagonal]
  by_cases h : i = k <;> simp [h]

theorem coef_single (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) = star (1 + y k) * (sg k : ℂ) := by
  rw [coef, jpq_eq_diagonal, dotProduct, Finset.sum_eq_single k]
  · simp [mulVec_diagonal]
  · intro b _ hb; simp [mulVec_diagonal, hb]
  · simp

theorem coef_single_ne (k : Fin P ⊕ Fin Q) (y : Sp P Q) (hy : y k ≠ -1) :
    coef (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) ≠ 0 := by
  rw [coef_single]
  refine mul_ne_zero (star_ne_zero.2 fun h => hy ?_) (by exact_mod_cast sg_ne_zero k)
  linear_combination h

theorem qf_single (k : Fin P ⊕ Fin Q) : qf (Pi.single k 1 : Sp P Q) = sg k := by
  rw [qf_eq_sum, Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · simp


open Classical in
def tanMat (k : Fin P ⊕ Fin Q) (y : Sp P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ :=
  if qf y = sg k ∧ y k ≠ -1 then -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) * flipAt k
  else sectMat (sg k) (Pi.single k 1) y

theorem tanMat_spec (k : Fin P ⊕ Fin Q) (y : Sp P Q) :
    (tanMat k y)ᴴ * Formalism.UG.Jpq P Q * tanMat k y = Formalism.UG.Jpq P Q ∧
      (qf y = sg k → tanMat k y *ᵥ (Pi.single k 1 : Sp P Q) = y) := by
  unfold tanMat
  split_ifs with h
  · have hc := coef_single_ne k y h.2
    have hu := qrefl_unitary _ (jpq_conjTranspose P Q) (Pi.single k 1) (-y)
      (by rw [form_self, form_self, qf_neg, qf_single, h.1]) hc
    refine ⟨?_, fun _ => ?_⟩
    · rw [neg_mul, conjTranspose_neg, neg_mul, neg_mul_neg, conjTranspose_mul]
      calc _ = (flipAt k)ᴴ * ((qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y))ᴴ * Formalism.UG.Jpq P Q *
            qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y)) * flipAt k := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu, flipAt_unitary]
    · rw [← mulVec_mulVec, flipAt_mulVec, neg_mulVec, qrefl_mulVec _ _ _ hc, neg_neg]
  · exact sectMat_spec (sg_ne_zero k) (qf_single k) y

theorem measurable_tanMat (k i j : Fin P ⊕ Fin Q) : Measurable fun y => tanMat k y i j := by
  classical
  have : (fun y => tanMat k y i j) = fun y => if qf y = sg k ∧ y k ≠ -1 then
      -qrefl (Formalism.UG.Jpq P Q) (Pi.single k 1) (-y) i j * (if j = k then 1 else -1)
      else sectMat (sg k) (Pi.single k 1) y i j := by
    funext y
    unfold tanMat
    by_cases h : qf y = sg k ∧ y k ≠ -1
    · rw [if_pos h, if_pos h, flipAt, mul_diagonal]; rfl
    · rw [if_neg h, if_neg h]
  rw [this]
  refine Measurable.ite ?_
    (((measurable_qrefl _ _ i j).comp measurable_neg).neg.mul measurable_const)
    (measurable_sectMat _ _ i j)
  have h2 : MeasurableSet ((fun y : Sp P Q => y k) ⁻¹' ({-1} : Set ℂ)ᶜ) :=
    (measurable_pi_apply k) (measurableSet_singleton (-1 : ℂ)).compl
  exact (measurable_qf (measurableSet_singleton (sg k))).inter h2

theorem tanMat_sub_one (k i b : Fin P ⊕ Fin Q) (y : Sp P Q) (h1 : qf y = sg k) (h2 : y k ≠ -1)
    (hb : b ≠ k) :
    ‖(tanMat k y - 1) i b‖ = ‖(Pi.single k 1 : Sp P Q) i + y i‖ * ‖y b‖ / ‖1 + y k‖ := by
  have : (tanMat k y - 1) i b = -((star (1 + y k) * (sg k : ℂ))⁻¹ *
      (((Pi.single k 1 : Sp P Q) i + y i) * (star (y b) * (sg b : ℂ)))) := by
    rw [tanMat, if_pos ⟨h1, h2⟩, Matrix.sub_apply, flipAt, mul_diagonal, if_neg hb, qrefl,
      coef_single]
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      smul_eq_mul, jpq_eq_diagonal, vecMul_diagonal, Pi.star_apply, Pi.add_apply,
      Pi.single_eq_of_ne hb, sub_neg_eq_add, zero_add]
    ring
  rw [this]
  simp only [norm_neg, norm_mul, norm_inv, norm_star, norm_sg, mul_one]
  ring

theorem exists_tangent_section : ∀ (P Q P' Q' : ℕ)
    (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), ∃ σ : Sp P Q → UpqT P Q,
    IsSection (sg (e none)) (baseVec e) σ ∧ ∀ y : Sp P Q, qf y = sg (e none) → y (e none) ≠ -1 →
      (∀ b, ‖UpqT.mat (σ y) (e none) (e (some b))‖ = ‖y (e (some b))‖) ∧
      ∀ a b, ‖(UpqT.mat (σ y) - 1) (e (some a)) (e (some b))‖ =
        ‖y (e (some a))‖ * ‖y (e (some b))‖ / ‖1 + y (e none)‖ := by
  intro P Q P' Q' e
  have hex : ∀ y, ∃ g : UpqT P Q, UpqT.mat g = tanMat (e none) y := fun y => by
    have : tanMat (e none) y ∈ Set.range (UpqT.mat (P := P) (Q := Q)) := by
      rw [GlobalTheory.UpqTopology.range_mat]; exact (tanMat_spec _ y).1
    exact this
  choose s hs using hex
  have hne : ∀ b, e (some b) ≠ e none := fun b h => by simpa using e.injective h
  refine ⟨s, ⟨?_, fun y hy => ?_⟩, fun y h1 h2 => ⟨fun b => ?_, fun a b => ?_⟩⟩
  · have : BorelSpace (UpqT P Q) := (GlobalTheory.UpqTopology.upq_lcsc P Q).2.2.2.2.1
    have he : MeasurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) (UpqT.mat (P := P) (Q := Q)) :=
      Topology.IsClosedEmbedding.measurableEmbedding
        (β := (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) GlobalTheory.UpqTopology.isClosedEmbedding_mat
    refine he.measurable_comp_iff.1 ?_
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Function.comp, hs] using measurable_tanMat (e none) i j
  · rw [act, hs]; exact (tanMat_spec _ y).2 hy
  · have h := tanMat_sub_one (e none) (e none) (e (some b)) y h1 h2 (hne b)
    rw [Matrix.sub_apply, Matrix.one_apply_ne (hne b).symm, sub_zero, Pi.single_eq_same] at h
    have h0 : ‖1 + y (e none)‖ ≠ 0 := norm_ne_zero_iff.2 fun h => h2 (by linear_combination h)
    rw [hs, h]
    field_simp
  · rw [hs, tanMat_sub_one (e none) _ _ y h1 h2 (hne b), Pi.single_eq_of_ne (hne a), zero_add]

end GlobalTheory.TangentSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliserStatement
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryBlockEmbedding_onto_stabiliser : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∃ j : UpqT P' Q' →* UpqT P Q, IsBlockEmb e j ∧ Topology.IsClosedEmbedding j ∧ Set.range j = {g | act g (baseVec e) = baseVec e} := by
  first | exact @GlobalTheory.BlockEmbedding.exists_blockEmb | exact GlobalTheory.BlockEmbedding.exists_blockEmb | (intros; apply GlobalTheory.BlockEmbedding.exists_blockEmb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianNormFibreMeasureFiniteInvariant
section
noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding
open scoped ENNReal NNReal

namespace GlobalTheory.FibreInvariance

variable {P Q : ℕ}

theorem qf_continuous : Continuous (qf : Sp P Q → ℝ) := by
  unfold qf
  fun_prop

theorem qf_act (g : UpqT P Q) (x : Sp P Q) : qf (act g x) = qf x := by
  have hu := GlobalTheory.UpqTopology.mat_unitary g
  apply Complex.ofReal_injective
  rw [← GlobalTheory.QuadricSection.form_self, ← GlobalTheory.QuadricSection.form_self]
  show star (UpqT.mat g *ᵥ x) ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ (UpqT.mat g *ᵥ x)) = _
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hu]

theorem normSq_det (g : UpqT P Q) : Complex.normSq (UpqT.mat g).det = 1 := by
  have h := congrArg Matrix.det (GlobalTheory.UpqTopology.mat_unitary g)
  have hJ : (Formalism.UG.Jpq P Q).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (GlobalTheory.UpqTopology.jpq_sq (P := P) (Q := Q))
    rw [det_mul, h0, zero_mul, det_one] at h1
    exact zero_ne_one h1
  rw [det_mul, det_mul, det_conjTranspose] at h
  have h2 : star (UpqT.mat g).det * (UpqT.mat g).det = 1 := by
    apply mul_right_cancel₀ hJ
    linear_combination h
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, h2, Complex.ofReal_one]

theorem map_volume_act (g : UpqT P Q) :
    (volume : Measure (Sp P Q)).map (act g) = volume := by
  have hdetC : LinearMap.det (Matrix.mulVecLin (UpqT.mat g)) = (UpqT.mat g).det :=
    LinearMap.det_toLin' _
  have hdet : LinearMap.det ((Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, hdetC, normSq_det]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Sp P Q))
    (f := (Matrix.mulVecLin (UpqT.mat g)).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] at hmap
  exact hmap

theorem continuous_act (g : UpqT P Q) : Continuous (act g : Sp P Q → Sp P Q) :=
  continuous_const.matrix_mulVec continuous_id

private lemma UpqT_mat_mul' (a b : UpqT P Q) : UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b := rfl

private lemma UpqT_mat_one' : UpqT.mat (1 : UpqT P Q) = 1 := rfl

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  show UpqT.mat g⁻¹ *ᵥ (UpqT.mat g *ᵥ x) = x
  rw [mulVec_mulVec, ← UpqT_mat_mul', inv_mul_cancel, UpqT_mat_one', one_mulVec]

def actHomeo (g : UpqT P Q) : Sp P Q ≃ₜ Sp P Q where
  toFun := act g
  invFun := act g⁻¹
  left_inv := act_inv_act g
  right_inv x := by simpa using act_inv_act g⁻¹ x
  continuous_toFun := continuous_act g
  continuous_invFun := continuous_act g⁻¹

theorem act_ne_zero_iff (g : UpqT P Q) (x : Sp P Q) : act g x ≠ 0 ↔ x ≠ 0 := by
  constructor
  · rintro h rfl
    exact h (mulVec_zero _)
  · intro hx h
    apply hx
    rw [← act_inv_act g x, h]
    exact mulVec_zero _

theorem isDxDq_map {fib : ℝ → Measure (Sp P Q)} (h : IsDxDq fib) (g : UpqT P Q) :
    IsDxDq fun t => (fib t).map (act g) := by
  have hm : Measurable (act g) := (continuous_act g).measurable
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hU : act g ⁻¹' {x : Sp P Q | x ≠ 0} = {x | x ≠ 0} := by
    ext x
    exact act_ne_zero_iff g x
  have hpre : ∀ t : ℝ, act g ⁻¹' (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) =
      qf ⁻¹' {id t} ∩ {x | x ≠ 0} := by
    intro t
    rw [Set.preimage_inter, hU, ← Set.preimage_comp]
    congr 1
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, qf_act]
  have hS : ∀ t : ℝ, MeasurableSet (qf ⁻¹' {id t} ∩ {x : Sp P Q | x ≠ 0}) := fun t =>
    (qf_continuous.measurable (measurableSet_singleton _)).inter hO.measurableSet
  have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
  obtain ⟨h1, h2, h3⟩ := h'
  show IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fun t => (fib t).map (act g)
  refine ⟨fun t => ?_, fun φ hφ => ?_, fun φ hφc hφs hφU => ?_⟩
  · dsimp only
    rw [Measure.map_apply hm (hS t).compl, Set.preimage_compl, hpre t]
    exact h1 t
  · dsimp only
    simp_rw [lintegral_map hφ hm]
    rw [← h2 (fun v => φ (act g v)) (hφ.comp hm)]
    have hdx : (dx P Q).map (act g) = dx P Q := by
      unfold dx
      rw [Measure.map_smul, map_volume_act]
      exact hm.aemeasurable
    conv_lhs => rw [← hdx]
    rw [setLIntegral_map hO.measurableSet hφ hm, hU]
  · have hc : Continuous (φ ∘ act g) := hφc.comp (continuous_act g)
    have hs : HasCompactSupport (φ ∘ act g) := hφs.comp_homeomorph (actHomeo g)
    have hU' : tsupport (φ ∘ act g) ⊆ {x | x ≠ 0} := by
      intro x hx
      exact (act_ne_zero_iff g x).1 (hφU (tsupport_comp_subset_preimage φ (continuous_act g) hx))
    obtain ⟨hi, hcont⟩ := h3 _ hc hs hU'
    refine ⟨fun b hb => ?_, ?_⟩
    · exact (integrable_map_measure hφc.aestronglyMeasurable hm.aemeasurable).2 (hi b hb)
    · have he : (fun b => ∫ v, φ v ∂((fib b).map (act g))) = fun b => ∫ v, (φ ∘ act g) v ∂(fib b) := by
        funext b
        exact integral_map hm.aemeasurable hφc.aestronglyMeasurable
      dsimp only
      rw [he]
      exact hcont

theorem fibre_finite_invariant : ∀ (P Q : ℕ) (fib : ℝ → Measure (Sp P Q)) (β : ℝ), IsDxDq fib →
    β ≠ 0 → IsFiniteMeasureOnCompacts (fib β) ∧
      ∀ g : UpqT P Q, (fib β).map (act g) = fib β := by
  intro P Q fib β h hβ
  have hq : Continuous (qf : Sp P Q → ℝ) := qf_continuous
  have hO : IsOpen {x : Sp P Q | x ≠ 0} := isOpen_ne
  have hz : qf (0 : Sp P Q) = 0 := by simp [qf]
  have hqO : qf ⁻¹' {β} ⊆ {x : Sp P Q | x ≠ 0} := by
    rintro x hx rfl
    apply hβ
    rw [← (hx : qf (0 : Sp P Q) = β), hz]
  refine ⟨⟨fun K hK => ?_⟩, fun g => ?_⟩
  · have h' : IsFibreFamily (dx P Q) qf id {x | x ≠ 0} volume Set.univ fib := h
    obtain ⟨h1, -, h3⟩ := h'
    have hb : 0 < |β| := abs_pos.mpr hβ
    have hK' : IsCompact (K ∩ qf ⁻¹' {β}) := hK.inter_right (isClosed_singleton.preimage hq)
    have hT : IsClosed {x : Sp P Q | |qf x| ≤ |β| / 2} :=
      isClosed_le (continuous_abs.comp hq) continuous_const
    have hdisj : Disjoint (K ∩ qf ⁻¹' {β}) {x : Sp P Q | |qf x| ≤ |β| / 2} := by
      rw [Set.disjoint_left]
      rintro x ⟨-, hx⟩ hx2
      have hx' : qf x = β := hx
      rw [Set.mem_ofPred_eq, hx'] at hx2
      linarith
    obtain ⟨φ, hφ1, hφ0, hφs, -⟩ := exists_continuous_one_zero_of_isCompact hK' hT hdisj
    have hsupp : tsupport φ ⊆ {x : Sp P Q | x ≠ 0} := by
      have hcl : tsupport φ ⊆ {x : Sp P Q | |β| / 2 ≤ |qf x|} := by
        apply closure_minimal _ (isClosed_le continuous_const (continuous_abs.comp hq))
        intro x hx
        by_contra hc
        have hc' : ¬ (|β| / 2 ≤ |qf x|) := hc
        exact hx (hφ0 (show |qf x| ≤ |β| / 2 from le_of_lt (not_le.mp hc')))
      intro x hx hx0
      have hx2 := hcl hx
      rw [Set.mem_ofPred_eq, hx0, hz, abs_zero] at hx2
      linarith
    obtain ⟨hint, -⟩ := h3 φ φ.continuous hφs hsupp
    have hfin := (hint β (Set.mem_univ β)).lintegral_lt_top
    have hnull : fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ = 0 := h1 β
    have hmeas : Measurable fun x => ENNReal.ofReal (φ x) :=
      ENNReal.measurable_ofReal.comp φ.continuous.measurable
    calc fib β K ≤ fib β ((K ∩ qf ⁻¹' {β}) ∪ (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ) := by
          apply measure_mono
          intro x hx
          by_cases hxS : qf x = β
          · exact Or.inl ⟨hx, hxS⟩
          · exact Or.inr fun hx' => hxS hx'.1
      _ ≤ fib β (K ∩ qf ⁻¹' {β}) + fib β (qf ⁻¹' {β} ∩ {x | x ≠ 0})ᶜ := measure_union_le _ _
      _ = ∫⁻ _ in K ∩ qf ⁻¹' {β}, 1 ∂(fib β) := by rw [hnull, add_zero, setLIntegral_one]
      _ ≤ ∫⁻ x in K ∩ qf ⁻¹' {β}, ENNReal.ofReal (φ x) ∂(fib β) :=
          setLIntegral_mono hmeas fun x hx => by rw [hφ1 hx]; simp
      _ ≤ ∫⁻ x, ENNReal.ofReal (φ x) ∂(fib β) := setLIntegral_le_lintegral _ _
      _ < ⊤ := hfin
  · exact GlobalTheory.IsFibreFamily_eq_at (dx P Q) qf {x | x ≠ 0} {x | x ≠ 0} {x | x ≠ 0} Set.univ
      Set.univ _ fib β hq.measurable hO subset_rfl subset_rfl hqO isOpen_univ isOpen_univ
      (Set.mem_univ β) (Set.mem_univ β) (isDxDq_map h g) h

end GlobalTheory.FibreInvariance
end
end

