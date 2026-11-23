module

public import Formalism.HermitianCurvature.StatementTL
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0117
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0104
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0046
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0042
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0095
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.VanishingOfL2Equivariant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0154
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0092
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0041
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0152
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0032
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0033
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointLeibnizExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0153

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
section
namespace Formalism.FourierDecayAlt.P.TLB

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
  Formalism.YangianSpanCharacter.T

noncomputable section

section gen

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}

theorem tprod_take_all (L : LevelData A r) (Y : ℂ) :
    L.Tprod Y = ((List.ofFn (L.Tl Y)).take r).reverse.prod := by
  unfold LevelData.Tprod
  rw [List.take_of_length_le (by simp)]

variable [StarRing A] [StarModule ℂ A]

theorem star_algMap (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (starRingEnd ℂ z) := by
  rw [← algebraMap_star_comm]; rfl

theorem star_Tl_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) (l : Fin r) :
    (L.Tl y l)ᴴ = (L.Tvl (starRingEnd ℂ y) l)ᵀ := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [LevelData.Tl, LevelData.Tvl, conjTranspose_apply, star_add, star_neg, hp, hc, hci, star_algMap,
      sub_eq_add_neg]

theorem star_Tprod_gen (L : LevelData A r) (hp : ∀ l, star (L.p l) = -L.pb l) (hc : ∀ l, star (L.c l) = L.cb l)
    (hci : ∀ l, star (L.ci l) = L.cbi l) (y : ℂ) :
    (L.Tprod y)ᴴ = (L.Tvprod (starRingEnd ℂ y))ᵀ := by
  rw [Formalism.FourierDecayAlt.P.MAx3.Q.Tvprod_transpose]
  unfold LevelData.Tprod
  rw [conjTranspose_list_prod, List.map_reverse, List.reverse_reverse, List.map_ofFn]
  congr 1
  exact congrArg List.ofFn (funext fun l => star_Tl_gen L hp hc hci y l)

end gen

section actual

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rma_pref_take (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) :
    ∀ n, Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y n = ((List.ofFn (L.Tl Y)).take n).reverse.prod
  | 0 => by simp [Formalism.FourierDecayAlt.P.JCx2.rma_pref]
  | n + 1 => by
    by_cases h : n < r
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dite_eq_left h, rma_pref_take L Y n, List.take_add_one, List.reverse_append,
        List.prod_append]
      have e : (List.ofFn (L.Tl Y))[n]? = some (L.Tl Y ⟨n, h⟩) := by simp [h]
      rw [e]
      simp only [Option.toList_some, List.reverse_cons, List.reverse_nil, List.nil_append, List.prod_cons,
        List.prod_nil, mul_one]
      congr 1
    · rw [Formalism.FourierDecayAlt.P.JCx2.rma_pref, dite_eq_right h, rma_pref_take L Y n, List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by simp; omega)]

theorem tprod_zero_eq (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) : tprod L Y 0 = L.Tprod Y := by
  have h : tprod L Y 0 = Formalism.FourierDecayAlt.P.JCx2.rma_pref L Y r := by
    have := Formalism.FourierDecayAlt.P.JCx2.rma_tprod_pref L Y r 0 (by omega)
    simpa [Formalism.FourierDecayAlt.P.JCx2.rma_pref] using this
  rw [h, rma_pref_take, tprod_take_all]

end actual

end

end Formalism.FourierDecayAlt.P.TLB

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

noncomputable section

theorem actual_algebra_facts : TL.ActualAlg := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  have hD' := hD
  obtain ⟨hpl, -, hL, hQQ, -, -, hSL, hst⟩ := hD
  obtain ⟨sp, sc, sci⟩ := P5.HerA.star_site_ops hL
  have hcent : ∀ (l : Fin P.r) (Y : ℂ) (a b : Fin 2),
      st.QQ Y a b ∈ StarSubalgebra.centralizer ℂ (hol (site L l)) := by
    intro l Y a b
    obtain ⟨hp, -, hc, hci, -⟩ := hL
    have ht : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b :=
      fun i => (Formalism.FourierDecayAlt.P.level_coordinates_commute Wp Wq P z z' π π' hpl X l i).1
    have htn : ∀ (i : Fin 6) (Y : ℂ) (a b : Fin 2), X.t Y a b * -X.op l i = -X.op l i * X.t Y a b := by
      intro i Y a b; rw [mul_neg, neg_mul, ht]
    rw [hQQ Y, Matrix.smul_apply]
    refine SMulMemClass.smul_mem _ ?_
    simp only [ActualOps.QQ, Matrix.of_apply]
    rw [StarSubalgebra.mem_centralizer_iff]
    intro g hg
    simp only [hol, site, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hp l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (htn _ _ _ _), P5.HerA.pair_operator_commute (htn _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hc l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
    · rw [hci l]
      exact ⟨P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _), P5.HerA.pair_operator_commute (ht _ _ _ _).symm (ht _ _ _ _)⟩
  have hqq : ∀ Y i j, ∀ x ∈ siteOps L, Commute (st.QQ Y i j) x := by
    intro Y i j x hx
    have key := fun l => (StarSubalgebra.mem_centralizer_iff ℂ).1 (hcent l Y i j)
    simp only [siteOps, Set.mem_union, Set.mem_range] at hx
    rcases hx with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
    · have h := key l
      exact (h (L.p l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.p l) (by simp [hol, site])).2
      rw [sp l] at h2
      exact Commute.neg_right_iff.1 (show Commute (st.QQ Y i j) (-L.pb l) from h2.symm)
    · exact (key l (L.c l) (by simp [hol, site])).1.symm
    · exact (key l (L.ci l) (by simp [hol, site])).1.symm
    · have h2 := (key l (L.c l) (by simp [hol, site])).2
      rw [sc l] at h2
      exact h2.symm
    · have h2 := (key l (L.ci l) (by simp [hol, site])).2
      rw [sci l] at h2
      exact h2.symm
  refine ⟨⟨hSL, hst, sp, sc, sci, hqq⟩, fun Y hY => ?_, fun Y hY => ?_⟩
  · have hY' : starRingEnd ℂ Y = Y := hY
    unfold P5.QQi
    simp only [Fin.val_zero]
    rw [hY, TLB.tprod_zero_eq, TLB.star_Tprod_gen L sp sc sci, hY']
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, cst, nP, LevelData.Ar, LevelData.Br,
      LevelData.Avr, LevelData.Bvr]
    simp only [add_mul, mul_add, mul_assoc]
    abel
  · obtain ⟨κ, hx, hxi, -⟩ :=
      P5.xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual P5.kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD'
    classical
    set f : M.Ty P → ℂ := fun ρ => M.x0 P l0 ρ Y with hf
    set N : Finset ℂ := Finset.univ.image f
    set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
    have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
      intro ρ
      have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
      have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
      simpa only [id] using h
    have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
      funext ρ
      rw [← hp ρ]
      have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : M.Ty P => ℂ) ρ) f p
      rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
      rw [this]
      rfl
    refine ⟨p, ?_⟩
    rw [hxi Y hY, hx Y, Polynomial.aeval_algHom_apply]
    exact congrArg κ he

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselFunctionalOfSigmaContinuity
section
noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.ThreeDimData

theorem shape_true : Shape :=
  DDSmoothness.shape_of psi_constant schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound

theorem k_finite_form : KFinForm :=
  DDSmoothness.kFinForm_of psi_constant bessel_convergence bessel_function_bound

theorem zeroCase_true : ZeroCase :=
  UnipotentHaarMeasurability.zeroCase_of bessel_convergence norm_identity_smooth schur_hermitian

theorem zero_case_discrete_series : ZeroCaseDD :=
  UnipotentHaarMeasurability.zeroCaseDD_of bessel_convergence norm_identity_smooth schur_hermitian

theorem discrete_series_form_one : DDFormOne :=
  discrete_series_form_one_reduction psi_constant schur_hermitian norm_inverse_bound growth_spherical_bound
    growth_group_bound double_coset_decomposition bessel_convergence norm_identity_smooth bessel_function_bound shape_true

theorem admissible_atomic_form_one : AtFormAdmOne :=
  admissible_atomic_form_one_reduction schur_hermitian bessel_convergence norm_identity_smooth bessel_function_bound
    shape_true k_finite_form zeroCase_true zero_case_discrete_series

theorem orbit_convergence_discrete_series : OrbConvDD :=
  S3dx4.orbConvDD_of_decDD double_coset_decomposition

theorem bessel_nonzero_l2 : BesselNonvanishingL2 :=
  MatrixMultiplicationContinuity.bessel_nonzero_l2_reduction schur_hermitian norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence

theorem regularity_and_convergence_bundle : More.PhiReg ∧ More.OOConv ∧ More.QuadConv :=
  regularity_bundle_from_hypotheses schur_hermitian norm_identity_smooth norm_inverse_bound growth_spherical_bound growth_group_bound
    double_coset_decomposition bessel_convergence orbit_convergence_discrete_series

theorem orbit_integral_convergence : More.OOConv := regularity_and_convergence_bundle.2.1

theorem quadratic_convergence : More.QuadConv := regularity_and_convergence_bundle.2.2

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactSupportFacts
section
namespace Formalism.FourierDecayAlt.P

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt

noncomputable section

theorem compact_support_facts : TL.CptFacts := by
  intro k r Wp Wq _ _ _ _ _ Bs F hF
  obtain ⟨hFs, ⟨R, hR⟩, ε, hε, hεF⟩ := hF
  refine ⟨⟨ε, hε, ?_⟩, fun Dop hDop => ?_⟩
  · set R' : ℝ := |R| + 1 with hR'
    have hR0 : 0 < R' := by positivity
    obtain ⟨h1, h2⟩ := JCx2.pd_cut_nice (E := Wq →L[ℂ] Wp) hR0 hFs
    have hN : JC.NiceCoef Bs ε (fun g => JCx2.pdPhi (R'⁻¹ • g) • F g) :=
      ⟨h1, fun A m => h2 A m, fun g hg hne => by
        refine hεF g hg ?_
        intro h0; apply hne; simp [h0]⟩
    refine JCx2.mn_nice_congr (fun g hg => ?_) hN
    by_cases h0 : F g = 0
    · simp [h0]
    · have hgR : gN g ≤ R := hR g hg h0
      have hg0 : 0 ≤ gN g := Real.sqrt_nonneg _
      have hsq : JCx2.pdSq (R'⁻¹ • g) ≤ 1 := by
        rw [JCx2.pd_sq_smul, JCx2.pd_sq_eq, inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
        have : gN g ≤ R' := by rw [hR']; linarith [le_abs_self R]
        nlinarith
      simp [JCx2.pdPhi, JCx2.pd_chi_one hsq]
  · have hGc : Continuous (Gf k r Bs.z Bs.z') := Formalism.FourierDecayAlt.P.Ux8.cont_Gf _ _ _ _
    have hv1 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | Gf k r Bs.z Bs.z' g < ε}, g ∈ GV k r →
        Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt hGc continuous_const)
        (fun g hg hgG => by by_contra hne; exact absurd (hεF g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hv2 : ∀ T ∈ Dop, ∀ g ∈ {g : Mat k r | R < gN g}, g ∈ GV k r → Rw T.word F g = 0 := fun T _ =>
      PBJ.rw_vanish_GV (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun g hg hgG => by by_contra hne; exact absurd (hR g hgG hne) (not_le.2 hg)) T.word T.word_lie
    have hcl : IsClosed {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} :=
      Formalism.FourierDecayAlt.P.B5.GV_closed.inter (isClosed_le continuous_const hGc)
    have hsub : {g : Mat k r | g ∈ GV k r ∧ ε ≤ Gf k r Bs.z Bs.z' g} ⊆ C6.domL Bs ∅ :=
      fun g hg => ⟨hg.1, lt_of_lt_of_le hε hg.2, by simp⟩
    have hsF : closure {g | g ∈ GV k r ∧ F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg; exact ⟨hg.1, hεF g hg.1 hg.2⟩
    have hsT : ∀ T ∈ Dop, closure {g | g ∈ GV k r ∧ Rw T.word F g ≠ 0} ⊆ C6.domL Bs ∅ := by
      intro T hT
      refine subset_trans (closure_minimal ?_ hcl) hsub
      intro g hg
      refine ⟨hg.1, ?_⟩
      by_contra hlt
      exact hg.2 (hv1 T hT g (not_le.1 hlt) hg.1)
    refine ⟨⟨?_, ⟨R, ?_⟩, ε, hε, ?_⟩, fun g hg hgn => ?_⟩
    · exact PBJ.ckOn_opApply_list _ F hFs hsF Dop (fun T hT => (hDop T hT).1) hsT
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv2 T hT g (not_le.1 hlt) hgG)
    · intro g hgG hne
      by_contra hlt
      exact hne (PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g (not_le.1 hlt) hgG)
    · refine PBJ.opApply_eq_zero Dop F g fun T hT => hv1 T hT g ?_ hg
      show Gf k r Bs.z Bs.z' g < ε
      by_contra hge
      exact hgn ⟨hg, lt_of_lt_of_le hε (not_lt.1 hge), by simp⟩

end

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCutTr
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section helpers

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem cutTr_Gf_gq (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ} (hc : ∀ a, q.1 a ≠ 0)
    (hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq q.2) :
    Formalism.QuantumDeterminants.Gf k r D.z D.z' (B.gq D q) =
      (∏ l, Complex.normSq (q.1 l)) * (Complex.normSq q.2 - Tz k r D.z * Tz k r D.z') := by
  have hsec := D.sec.2 q.2 hζ
  have hmin := big_cell_minors_holds k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem
  have hz := hmin.2.2 hc
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ D.z_mem D.z'_mem, hsec.2] at hz
  have hr := hmin.1 (Fin.last r)
  set P := Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) ⟨r, by omega⟩ with hP
  have hPe : P = ∏ a : Fin r, q.1 a := by
    have : P = ∏ a : Fin r with a.val < (Fin.last r).val, q.1 a := hr
    rw [this]
    congr 1
    ext a
    simp
  have hP0 : P ≠ 0 := by
    rw [hPe]; exact Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hlast : Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1)) = q.2 * P := by
    unfold zeta at hz
    rw [← hP] at hz
    have h2 := div_mul_cancel₀ (Dmin k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) (Fin.last (r + 1))) hP0
    rw [hz] at h2
    exact h2.symm
  show Formalism.QuantumDeterminants.Gf k r D.z D.z' (bigCell k r q.1 (D.μsec q.2)) = _
  unfold Formalism.QuantumDeterminants.Gf
  rw [hlast, ← hP, Complex.normSq_mul, hPe, map_prod]
  ring

theorem cutTr_hsVec_contDiff [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] :
    ContDiff ℝ ∞ (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) := by
  have h : (B.hsVec : (Wq →L[ℂ] Wp) → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) =
      ⇑((LinearMap.toContinuousLinearMap (Formalism.FourierDecayAlt.P.JFxI.hsVecL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ) := rfl
  rw [h]
  exact ContinuousLinearMap.contDiff _

theorem cutTr_jgq_smooth (D : B.RealPlaceData k r Wp Wq) (J : B.Mat k r → (Wq →L[ℂ] Wp)) (Om : Set (B.Mat k r))
    (hJ : Q.SmoothLev k r 0 Om J) (hOm : ∀ q ∈ JF.QDom k r D.z D.z', B.gq D q ∈ Om) :
    ContDiffOn ℝ ∞ (fun q => J (B.gq D q)) (JF.QDom k r D.z D.z') := by
  have hg : ContDiffOn ℝ ∞ (fun q => B.gq D q) (JF.QDom k r D.z D.z') :=
    contDiffOn_infty.2 fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn D n
  refine contDiffOn_of_locally_contDiffOn fun q hq => ?_
  have hG := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hq
  obtain ⟨U, F', hU, hgU, hc, he⟩ := hJ (B.gq D q) ⟨Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 hG.1, hOm q hq⟩
  refine ⟨JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U,
    hg.continuousOn.isOpen_inter_preimage (Formalism.FourierDecayAlt.P.BigCellOpenDomain.qdom_open D.z D.z') hU, ⟨hq, hgU⟩, ?_⟩
  have hcomp : ContDiffOn ℝ ∞ (F' ∘ fun q => B.gq D q)
      (JF.QDom k r D.z D.z' ∩ (JF.QDom k r D.z D.z' ∩ (fun q => B.gq D q) ⁻¹' U)) :=
    hc.comp (hg.mono Set.inter_subset_left) fun x hx => hx.2.2
  refine hcomp.congr fun x hx => ?_
  exact he _ hx.2.2 (Formalism.FourierDecayAlt.P.WordKeyIdentity.glev0 (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom D hx.1).1)

end helpers

theorem cutTr_normSq_contDiff : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  have : (fun z : ℂ => Complex.normSq z) = fun z => ‖z‖ ^ 2 := by
    funext z; exact Complex.normSq_eq_norm_sq z
  rw [this]
  exact contDiff_norm_sq ℝ

theorem cutoff_transport_to_model : CutTr := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he hJ c hc ε hε
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hQ : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun x hx => ⟨hx.1, hTT ▸ hx.2⟩
  have hOm : ∀ q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z', B.gq (T v).base q ∈ OmP S T v := by
    intro q hq
    have h := (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq).2
    exact ⟨h.2, fun a => h.1 _ (by simp)⟩
  funext ρ
  set u : MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ := fun q =>
    ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (B.JF (T v).base (f v) (B.gq (T v).base q.1))) with hu_def
  have hu : u ∈ MA.smSub (D.parOf S v).r (D.parOf S v).TT := by
    show ContDiffOn ℝ MA.sm (MA.ext u) (MA.Qset _ _)
    have hg : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => B.JF (T v).base (f v) (B.gq (T v).base x))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (cutTr_jgq_smooth (T v).base _ _ hJ.1 hOm).mono hQ
    have he' : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => e ρ x.2) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      (he.1 ρ).comp contDiff_snd.contDiffOn fun x hx => hx.2
    have hwc : ContDiff ℝ ∞ (fun x : MA.E (D.parOf S v).r => MA.wq S.G.k x (D.parOf S v).TT) := by
      have hn := cutTr_normSq_contDiff
      unfold MA.wq
      fun_prop
    have hwp : ∀ x ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, MA.wq S.G.k x (D.parOf S v).TT ≠ 0 := by
      intro x hx
      unfold MA.wq
      exact (mul_pos (Finset.prod_pos fun l _ => pow_pos (Complex.normSq_pos.2 (hx.1 l)) _)
        (pow_pos (sub_pos.2 hx.2) _)).ne'
    have hw : ContDiffOn ℝ ∞ (fun x : MA.E (D.parOf S v).r => ((Real.sqrt (MA.wq S.G.k x (D.parOf S v).TT) : ℝ) : ℂ))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (hwc.contDiffOn.sqrt hwp)
    refine (hw.mul ((cutTr_hsVec_contDiff.comp_contDiffOn he').inner ℂ
      (cutTr_hsVec_contDiff.comp_contDiffOn hg))).congr ?_
    intro x hx
    simp [MA.ext, hx, hu_def]
  have hL : trJ S T v e (B.JF (T v).base (D.cutF (T v).base χ (f v) ε)) ρ =
      MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) * u q) := by
    unfold trJ
    congr 1
    funext q
    rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right,
      cutTr_Gf_gq (T v).base q.2.1 (hTT ▸ q.2.2)]
    simp only [hu_def, LE.Cut.sc, hc, pow_one, MA.Gq, hTT]
    ring
  have hR : (trJ S T v e (B.JF (T v).base (f v)) ρ) = ⟨u, hu⟩ := by
    unfold trJ MA.toSm
    rw [dite_eq_left hu]
  rw [hL]
  show _ = MA.toSm (D.parOf S v) (fun q => ((c.sc ε 1 (MA.Gq (D.parOf S v) q) : ℝ) : ℂ) *
    (trJ S T v e (B.JF (T v).base (f v)) ρ).1 q)
  rw [hR]

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.YGSlice
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory

noncomputable section

def YGSlice : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (h' : C.LPt) (m ρ : ℕ)
    (e1 : r = D.ptSize h' + (m + 2) + ρ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (Φ : G.Mat (m + 2) → V) (L : V →L[ℂ] E) (γ : B.Mat k ρ) (Kc : Set ℂ) (K a : ℝ),
    D.IsLocPt h' (D.ptSize h') → (0 : ℂ) ∉ Kc → ((m : ℝ) + 1) * ((m : ℝ) + 4) < a →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → ContinuousAt Φ Z ∧ ‖Φ Z‖ ≤ K * (1 + ‖Z‖) ^ (-a)) →
    (∀ Z : G.Mat (m + 2), G.detM Z ≠ 0 → G.detM Z ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc →
      L (Φ Z) = U.PhiFun k ρ (D.ptPerm h') (D.ptDiag h') (D.castV e1 z) (D.castV e1 z')
        (D.castF e1.symm F) Z γ) →
    ∀ q, okG m Kc q →
    Integrable (fun ξ : U.Xi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) =>
        U.psiStar k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.castV (by rw [ptSize_ptG]; omega) z)
          (D.castV (by rw [ptSize_ptG]; omega) z') ξ •
          D.castF (by rw [ptSize_ptG]; omega) F
            (U.gaXi k (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q)) (D.ptDiag (ptG h' m q)) ξ
              (fun a => a.elim0) (D.castM (by rw [ptSize_ptG]; omega) γ)))
      (U.muXi k (D.ptSize (ptG h' m q)) 0 (r - D.ptSize (ptG h' m q)) (D.ptPerm (ptG h' m q))) →
    L (yG U.betaU m Φ q) = D.sliceAt k r z z' F (ptG h' m q) (D.castM (by rw [ptSize_ptG]; omega) γ)

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
end

