module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.WhittakerZeroStatement

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ExistsOrthogonalProjectionInner
section
noncomputable section

open Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem unitary_matrix_mul (ε : Fin n → Bool) (x y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (x * y) = Formalism.MainNotions.S.umat x * Formalism.MainNotions.S.umat y := rfl

theorem unitary_matrix_inv_alt (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat y⁻¹ = (Formalism.MainNotions.S.umat y)⁻¹ := by
  show ((y⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = _
  rw [Matrix.coe_units_inv]

theorem unitary_matrix_one (ε : Fin n → Bool) : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem right_regular_mul (ε : Fin n → Bool) (x y : Formalism.REAL.UJ ε) (v : L2 ε) :
    rreg ε (Formalism.MainNotions.S.umat (x * y)) v = rreg ε (Formalism.MainNotions.S.umat x) (rreg ε (Formalism.MainNotions.S.umat y) v) := by
  rw [rightRegular_unitary_eq, rightRegular_unitary_eq, rightRegular_unitary_eq, rregRep_mul]; rfl

theorem right_regular_one (ε : Fin n → Bool) (v : L2 ε) : rreg ε (Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)) v = v := by
  rw [unitary_matrix_one, rregRep_one]; rfl

theorem right_regular_inner_preserving (ε : Fin n → Bool) (y : Formalism.REAL.UJ ε) (u v : L2 ε) :
    ⟪rreg ε (Formalism.MainNotions.S.umat y) u, rreg ε (Formalism.MainNotions.S.umat y) v⟫_ℂ = ⟪u, v⟫_ℂ := by
  have hn : ∀ w : L2 ε, ‖rreg ε (Formalism.MainNotions.S.umat y) w‖ = ‖w‖ :=
    (rreg_isURepOn ε).2.1 _ (unitary_matrix_mem_set ε y)
  let T : L2 ε →ₗᵢ[ℂ] L2 ε := ⟨(rreg ε (Formalism.MainNotions.S.umat y)).toLinearMap, hn⟩
  exact T.inner_map_map u v

theorem matrix_coefficient_translate (ε : Fin n → Bool) (x y : Formalism.REAL.UJ ε) (f : L2 ε) :
    ⟪f, rreg ε (Formalism.MainNotions.S.umat (y⁻¹ * x)) f⟫_ℂ =
      ⟪rreg ε (Formalism.MainNotions.S.umat y) f, rreg ε (Formalism.MainNotions.S.umat x) f⟫_ℂ := by
  rw [right_regular_mul, ← right_regular_inner_preserving ε y, ← right_regular_mul, mul_inv_cancel, right_regular_one]

theorem right_regular_continuous (ε : Fin n → Bool) (v : L2 ε) :
    Continuous (fun y : Formalism.REAL.UJ ε => rreg ε (Formalism.MainNotions.S.umat y) v) := by
  simp_rw [rightRegular_unitary_eq]
  exact rregRep_cont ε v

theorem right_regular_toL2_ae_eq (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) (y : Formalism.REAL.UJ ε) :
    (rreg ε (Formalism.MainNotions.S.umat y) (toL2 ε F) : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε]
      fun z => F (Formalism.MainNotions.S.umat z * Formalism.MainNotions.S.umat y) := by
  have hm := measurePreserving_mul_right ε y
  have e : rreg ε (Formalism.MainNotions.S.umat y) (toL2 ε F) = toL2 ε (fun x => F (x * Formalism.MainNotions.S.umat y)) :=
    rightRegular_toL2 ε F (unitary_matrix_mem_set ε y)
  have h1 := hF2.comp_measurePreserving hm
  have hfun : ((fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) ∘ fun x => x * y) =
      fun g : Formalism.REAL.UJ ε => (fun x => F (x * Formalism.MainNotions.S.umat y)) (Formalism.MainNotions.S.umat g) := by
    funext g; simp only [Function.comp_apply, unitary_matrix_mul]
  rw [hfun] at h1
  rw [e, toL2_eq_memLp_toLp ε (F := fun x => F (x * Formalism.MainNotions.S.umat y)) h1]
  exact MemLp.coeFn_toLp (f := fun z : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat z * Formalism.MainNotions.S.umat y)) h1

theorem toL2_ae_eq_function (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    (toL2 ε F : Formalism.REAL.UJ ε → ℂ) =ᵐ[Formalism.REAL.muG ε] fun z => F (Formalism.MainNotions.S.umat z) := by
  rw [toL2_eq_memLp_toLp ε hF2]; exact hF2.coeFn_toLp

theorem inner_indicator_right_regular (ε : Fin n → Bool) {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε))
    {N : Set (Formalism.REAL.UJ ε)} (hN : MeasurableSet N) (hNf : Formalism.REAL.muG ε N ≠ ∞) (y : Formalism.REAL.UJ ε) :
    ⟪(indicatorConstLp 2 hN hNf (1 : ℂ) : L2 ε), rreg ε (Formalism.MainNotions.S.umat y) (toL2 ε F)⟫_ℂ =
      ∫ z in N, F (Formalism.MainNotions.S.umat z * Formalism.MainNotions.S.umat y) ∂(Formalism.REAL.muG ε) := by
  rw [L2.inner_indicatorConstLp_one]
  exact setIntegral_congr_ae hN ((right_regular_toL2_ae_eq ε hF2 y).mono fun z hz _ => hz)

theorem matrix_coefficient_memLp (ε : Fin n → Bool) {K : Submodule ℂ (L2 ε)} {d : ℝ}
    (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ))
    {a b : L2 ε} (ha : a ∈ K) (hb : b ∈ K) :
    MemLp (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ) 2 (Formalism.REAL.muG ε) := by
  have hc : Continuous (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ) :=
    continuous_const.inner (right_regular_continuous ε b)
  rw [memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable]
  have hi := ((hS a ha b hb a ha b hb).1).re
  refine hi.congr (ae_of_all _ fun y => ?_)
  simp only [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

def fGam (ε : Fin n → Bool) (f : L2 ε) (g : Formalism.REAL.UJ ε) : ℂ := ⟪f, rreg ε (Formalism.MainNotions.S.umat g) f⟫_ℂ

def fPhi (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (f : L2 ε) (w : Formalism.REAL.UJ ε) : ℂ :=
  ∫ y, F (Formalism.MainNotions.S.umat y) * fGam ε f (y⁻¹ * w) ∂(Formalism.REAL.muG ε)

theorem matrix_coefficient_continuous (ε : Fin n → Bool) (f : L2 ε) : Continuous (fGam ε f) :=
  continuous_const.inner (right_regular_continuous ε f)

theorem exists_orthogonal_projection_inner (ε : Fin n → Bool) {K : Submodule ℂ (L2 ε)} (hKc : IsClosed (K : Set (L2 ε))) (β : L2 ε) :
    ∃ β' ∈ K, ∀ u ∈ K, ⟪β, u⟫_ℂ = ⟪β', u⟫_ℂ := by
  have : CompleteSpace K := hKc.completeSpace_coe
  refine ⟨(K.orthogonalProjectionOnto β : L2 ε), (K.orthogonalProjectionOnto β).2, fun u hu => ?_⟩
  have := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (K := K) ⟨u, hu⟩ β
  rw [Submodule.coe_inner] at this
  exact this.symm

variable {ε : Fin n → Bool} {K : Submodule ℂ (L2 ε)} {d : ℝ}

theorem schur_orthogonality_integral (hKc : IsClosed (K : Set (L2 ε)))
    (hKs : ∀ g ∈ UJset ε, ∀ u ∈ K, rreg ε g u ∈ K)
    (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ))
    {f : L2 ε} (hf : f ∈ K) (β : L2 ε) (x : Formalism.REAL.UJ ε) :
    ∫ y, ⟪β, rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ * fGam ε f (y⁻¹ * x) ∂(Formalism.REAL.muG ε) =
      ⟪f, f⟫_ℂ * ⟪β, rreg ε (Formalism.MainNotions.S.umat x) f⟫_ℂ / (d : ℂ) := by
  obtain ⟨β', hβ', hβ⟩ := exists_orthogonal_projection_inner ε hKc β
  have hmem : ∀ y : Formalism.REAL.UJ ε, rreg ε (Formalism.MainNotions.S.umat y) f ∈ K :=
    fun y => hKs _ (unitary_matrix_mem_set ε y) f hf
  have e : (fun y : Formalism.REAL.UJ ε => ⟪β, rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ * fGam ε f (y⁻¹ * x)) =
      fun y => ⟪β', rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ * star ⟪rreg ε (Formalism.MainNotions.S.umat x) f, rreg ε (Formalism.MainNotions.S.umat y) f⟫_ℂ := by
    funext y
    rw [hβ _ (hmem y), fGam, matrix_coefficient_translate, RCLike.star_def, inner_conj_symm]
  rw [e, (hS β' hβ' f hf _ (hmem x) f hf).2, hβ _ (hmem x)]

theorem convolution_eq_integral {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (f : L2 ε) (w : Formalism.REAL.UJ ε) :
    fPhi ε F f w = ∫ z, F (Formalism.MainNotions.S.umat (w * z)) * fGam ε f z⁻¹ ∂(Formalism.REAL.muG ε) := by
  unfold fPhi
  rw [← integral_mul_left_eq_self (fun y => F (Formalism.MainNotions.S.umat y) * fGam ε f (y⁻¹ * w)) w]
  congr 1
  funext z
  congr 2
  group

theorem convolution_coefficient_continuous (hS : ∀ a ∈ K, ∀ b ∈ K, ∀ a' ∈ K, ∀ b' ∈ K,
      Integrable (fun y : Formalism.REAL.UJ ε => ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ *
        star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ) (Formalism.REAL.muG ε) ∧
      ∫ y, ⟪a, rreg ε (Formalism.MainNotions.S.umat y) b⟫_ℂ * star ⟪a', rreg ε (Formalism.MainNotions.S.umat y) b'⟫_ℂ
        ∂(Formalism.REAL.muG ε) = ⟪b', b⟫_ℂ * ⟪a, a'⟫_ℂ / (d : ℂ))
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) (hfK : toL2 ε F ∈ K) :
    Continuous (fPhi ε F (toL2 ε F)) := by
  set f := toL2 ε F with hfdef
  have hγ : MemLp (fGam ε f) 2 (Formalism.REAL.muG ε) := matrix_coefficient_memLp ε hS hfK hfK
  have hγi : MemLp (fun z : Formalism.REAL.UJ ε => star (fGam ε f z⁻¹)) 2 (Formalism.REAL.muG ε) :=
    (hγ.comp_measurePreserving (Measure.measurePreserving_inv (Formalism.REAL.muG ε))).star
  let Fm : C(Formalism.REAL.UJ ε × Formalism.REAL.UJ ε, Formalism.REAL.UJ ε) := ⟨fun p => p.1 * p.2, by fun_prop⟩
  have hL := Continuous.compMeasurePreservingLp (μ := Formalism.REAL.muG ε) (ν := Formalism.REAL.muG ε)
    (f := fun _ : Formalism.REAL.UJ ε => f) (g := fun w => Fm.curry w) continuous_const Fm.curry.continuous
    (fun w => measurePreserving_mul_left (Formalism.REAL.muG ε) w) (by norm_num)
  have key : ∀ w, fPhi ε F f w = ⟪hγi.toLp _, Lp.compMeasurePreserving (Fm.curry w)
      (measurePreserving_mul_left (Formalism.REAL.muG ε) w) f⟫_ℂ := by
    intro w
    rw [convolution_eq_integral, MeasureTheory.L2.inner_def]
    have h1 := hγi.coeFn_toLp
    have h2 := Lp.coeFn_compMeasurePreserving f (measurePreserving_mul_left (Formalism.REAL.muG ε) w)
    have h3 := (measurePreserving_mul_left (Formalism.REAL.muG ε) w).quasiMeasurePreserving.ae_eq_comp
        (toL2_ae_eq_function ε hF2)
    apply integral_congr_ae
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    rw [RCLike.inner_apply', hz1]
    have hz2' : (Lp.compMeasurePreserving (Fm.curry w) (measurePreserving_mul_left (Formalism.REAL.muG ε) w) f :
        Formalism.REAL.UJ ε → ℂ) z = (f : Formalism.REAL.UJ ε → ℂ) (w * z) := hz2
    simp only [Function.comp_apply] at hz3
    rw [hz2', hz3]
    simp only [RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
    ring
  have : fPhi ε F f = fun w => ⟪hγi.toLp _, Lp.compMeasurePreserving (Fm.curry w)
      (measurePreserving_mul_left (Formalism.REAL.muG ε) w) f⟫_ℂ := funext key
  rw [this]
  exact continuous_const.inner hL

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ListProdMemOfForall
section
namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorMembership

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem list_prod_mem_of_forall {S : Submodule ℂ M} :
    ∀ (l : List (Module.End ℂ M)), (∀ f ∈ l, ∀ x ∈ S, f x ∈ S) → ∀ x ∈ S, l.prod x ∈ S
  | [], _, x, hx => by simpa using hx
  | f :: l, h, x, hx => by
    rw [List.prod_cons, Module.End.mul_apply]
    exact h f List.mem_cons_self _
      (list_prod_mem_of_forall l (fun g hg => h g (List.mem_cons_of_mem _ hg)) x hx)

theorem capEntry_mem {n : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    ∀ x ∈ S, Capelli.capEntry E t a b x ∈ S := by
  intro x hx
  unfold Capelli.capEntry
  rw [LinearMap.add_apply]
  refine S.add_mem (hS a b x hx) ?_
  split_ifs
  · simpa using S.smul_mem t hx
  · simp

theorem cminor_mem {n p : ℕ} {E : Fin n → Fin n → Module.End ℂ M} {S : Submodule ℂ M}
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (t : ℂ) :
    ∀ x ∈ S, Capelli.cminor E R C t x ∈ S := by
  intro x hx
  unfold Capelli.cminor
  rw [LinearMap.sum_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [LinearMap.smul_apply]
  refine S.smul_of_tower_mem _ ?_
  refine list_prod_mem_of_forall _ ?_ x hx
  intro f hf
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
  exact capEntry_mem hS _ _ _

end CapelliMinorMembership

open CapelliMinorMembership

theorem eig : EigStatement := by
  intro M _ _ m E S ω y β v hE hS hC hv
  have h0 : Capelli.capelliC E (ω : ℂ) v = 0 := hC v hv
  have eV : Capelli.eeV E = LemK.eeV E := by
    ext f d; simp [Capelli.eeV, LemK.eeV, LemK.prj]
  have eVd : Capelli.eeVd E = LemK.eeVd E := by
    ext f d; simp [Capelli.eeVd, LemK.eeVd, LemK.prj]
  constructor
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnPlus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eV,
        Capelli.capelliAPlus M m E y (ω : ℂ) v hE h0]
      simp
  · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Submodule.mem_pi]
      intro d _
      unfold Capelli.nnMinus
      exact S.sum_mem fun c _ => S.smul_mem _ (cminor_mem hS _ _ _ v hv)
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, ← eVd,
        Capelli.capelliAMinus M m E β (ω : ℂ) v hE h0]
      simp

end ReciprocityTheory.ChartRestriction.DS.Lap
end

