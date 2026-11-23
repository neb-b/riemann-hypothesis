module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0015
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.SmoothOfRegular
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerAverageSplit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem mahler_specFirst_eq (h3 : EvalSpecFirst.Statement) {n e : ℕ} (h : HermNorm n)
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (v : Fin n → ℂ) :
    mahler h e (specFirst f v) =
      sphereMean h e (fun w => Real.log ‖eval (consGroup v w) f‖) := by
  unfold mahler
  congr 1
  funext w
  rw [h3]

theorem MahlerAverageSplit.proof (h1 : MahlerIntegrand.Statement) (h2 : SphereMeanFubini.Statement)
    (h3 : EvalSpecFirst.Statement) : MahlerAverageSplit.Statement := by
  intro n e δ h f hf hhom
  have hint := h1 n (e + 1) δ h f hf hhom
  obtain ⟨hI, hM⟩ := h2 n e h (fun u => Real.log ‖eval u f‖) hint
  have key : (fun v => mahler h e (specFirst f (nrmv h v))) =
      fun v => sphereMean h e (fun w => Real.log ‖eval (consGroup (nrmv h v) w) f‖) := by
    funext v
    exact mahler_specFirst_eq h3 h f (nrmv h v)
  rw [key]
  exact ⟨hI, hM⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerIntegrand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PMahlerSectionOfConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

theorem MahlerSectionOfConst.proof (h1 : DefectAverage.Statement) (h2 : AdmissibleAENrm.Statement)
    (h3 : BallVolume.Statement) : MahlerSectionOfConst.Statement := by
  intro e hconst n δ h Z f u data hu
  set K := mahlerDefect h e Z f u with hK
  have hrel : ∀ W ∈ Z.support, IsRelevant W := fun W hW => (data.prime W hW).isRelevant
  have hae : (fun v => mahlerDefect h e Z f (nrmv h v)) =ᵐ[volume.restrict (ballH h)] fun _ => K := by
    filter_upwards [h2 n h Z hrel] with v hv
    exact hconst n δ h Z f (nrmv h v) u data hv hu
  have havg : ⨍ v in ballH h, mahlerDefect h e Z f (nrmv h v) = K := by
    rw [average_congr hae]
    obtain ⟨hpos, hfin⟩ := h3 n h
    exact setAverage_const hpos.ne' hfin.ne K
  have hmean := (h1 n e δ h Z f data).2
  rw [havg] at hmean
  have hK' : K = mahler h e (specFirst f u) - cycleIntegral h Z e (fsLog h u) := rfl
  linarith
end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PNormOfDividedFormSep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial
open scoped nonZeroDivisors

noncomputable section

namespace NormOfDividedFormSep

variable {O B K L : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Field K] [Field L] [Algebra O K]
  [IsFractionRing O K] [Algebra B L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O B L]
  [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L]


omit [IsDomain O] [IsFractionRing O K] [IsLocalization (Algebra.algebraMapSubmonoid B O⁰) L] in
theorem algebraMap_sum_smul {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap B L (∑ m, v m • η m) = ∑ m, algebraMap O K (v m) • algebraMap B L (η m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← IsScalarTower.algebraMap_apply O B L, IsScalarTower.algebraMap_apply O K L]

theorem adjoin_range_eq_top {n : ℕ} (η : Fin n → B) (hgen : Algebra.adjoin O (Set.range η) = ⊤) :
    Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid B O⁰) x
  obtain ⟨a, ha, has⟩ := s.2
  have hle : (Algebra.adjoin O (Set.range η)).map (IsScalarTower.toAlgHom O B L) ≤
      (Algebra.adjoin K (Set.range fun m => algebraMap B L (η m))).restrictScalars O := by
    rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, IsScalarTower.coe_toAlgHom']
    exact Algebra.subset_adjoin ⟨m, rfl⟩
  have hb : algebraMap B L b ∈ Algebra.adjoin K (Set.range fun m => algebraMap B L (η m)) :=
    hle (Subalgebra.mem_map.2 ⟨b, by rw [hgen]; trivial, IsScalarTower.toAlgHom_apply O B L b⟩)
  have ha0 : algebraMap O K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero ha)
  have hs : IsLocalization.mk' L b s = (algebraMap O K a)⁻¹ • algebraMap B L b := by
    rw [eq_inv_smul_iff₀ ha0, Algebra.smul_def, ← IsScalarTower.algebraMap_apply O K L,
      IsScalarTower.algebraMap_apply O B L, has]
    exact IsLocalization.mk'_spec' L b s
  change IsLocalization.mk' L b s ∈ _
  rw [hs]
  exact Subalgebra.smul_mem _ hb _


omit [IsDomain O] in
theorem algebraMap_det_mulLeft [Module.Free O B] [Module.Finite O B] [FiniteDimensional K L]
    (hEval : NormFormEval.Statement) {n : ℕ} (η : Fin n → B) (v : Fin n → O) :
    algebraMap O K (LinearMap.det (LinearMap.mulLeft O (∑ m, v m • η m))) =
      eval (fun m => algebraMap O K (v m)) (normForm K L fun m => algebraMap B L (η m)) := by
  rw [hEval K L n _ _]
  change algebraMap O K (Algebra.norm O _) = _
  rw [← Algebra.norm_localization O O⁰ (Sₘ := L), algebraMap_sum_smul (K := K)]

end NormOfDividedFormSep


open NormOfDividedFormSep in
theorem NormOfDividedFormSep.proof (hEval : NormFormEval.Statement) (hDvd : NormFormDvd.Statement)
    (hPrime : PrimeMapFractionRing.Statement) : NormOfDividedFormSep.Statement := by
  intro O B _ _ _ _ _ _ _ _ n η t P hsep hgen ht hP hdvd u
  let K := FractionRing O
  let L := FractionRing B
  let _ : Algebra K L := FractionRing.liftAlgebra O L
  have : IsScalarTower O K L := FractionRing.isScalarTower_liftAlgebra O L
  have : FiniteDimensional K L := .of_isLocalization O B O⁰
  have : Algebra.IsSeparable K L := hsep
  have hOB : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hOK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have : Infinite K := Infinite.of_injective _ hOK
  let ηL : Fin n → L := fun m => algebraMap B L (η m)
  let tK : Fin n → K := fun m => algebraMap O K (t m)
  have htL : ∑ m, tK m • ηL m = 1 := by
    rw [← algebraMap_sum_smul, ht, map_one]

  have hdvdL : (∑ m, X m * C (ηL m)) ∣ map (algebraMap K L) (map (algebraMap O K) P) := by
    have h := _root_.map_dvd (MvPolynomial.map (algebraMap B L)) hdvd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq O K L, ← map_map, map_sum] at h
    simpa only [map_mul, map_X, map_C] using h

  have hnc : ∀ a : O, P ≠ C a := by
    rintro a rfl
    obtain ⟨g, hg⟩ := hdvd
    have h := congrArg (eval 0) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_C, eval_C, map_mul, map_sum, eval_X, Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h
    exact hP.ne_zero (by rw [(map_eq_zero_iff _ hOB).1 h, map_zero])

  obtain ⟨c, hc⟩ := hDvd K L n ηL tK _ (adjoin_range_eq_top η hgen) htL hdvdL
  have hNt : eval tK (normForm K L ηL) = 1 := by
    rw [hEval K L n ηL, htL, map_one]
  have hN0 : ¬ IsUnit (normForm K L ηL) := by
    intro h
    have h0 := h.map (eval (0 : Fin n → K))
    rw [hEval K L n ηL] at h0
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, Algebra.norm_zero] at h0
    exact not_isUnit_zero h0
  have hcu : IsUnit c := ((hPrime O K n P hP hnc).irreducible.isUnit_or_isUnit hc).resolve_left hN0
  obtain ⟨c₀, -, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hcu
  have hev : ∀ v : Fin n → O, eval (fun m => algebraMap O K (v m)) (map (algebraMap O K) P) =
      algebraMap O K (eval v P) := fun v => by
    rw [eval_map]
    exact (eval₂_comp_left (algebraMap O K) (RingHom.id O) v P).symm
  have hct : c₀ = algebraMap O K (eval t P) := by
    have h := congrArg (eval tK) hc
    rw [map_mul, hNt, eval_C, one_mul] at h
    rw [← h, hev]
  apply hOK
  have h := congrArg (eval (fun m => algebraMap O K (u m))) hc
  rw [map_mul, eval_C, hct, hev] at h
  rw [map_mul, algebraMap_det_mulLeft (L := L) hEval η u, h, mul_comm]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPointLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace PointLine

variable {n : ℕ}

theorem eval_smul_of_isHomogeneous {φ : MvPolynomial (Fin n) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ m * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg := hφ.degree_eq_sum_deg_support hd
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

theorem smul_mem_zeroSet {W : Ideal (MvPolynomial (Fin n) ℂ)} (hW : IsHomogIdeal W)
    {x : Fin n → ℂ} (hx : ∀ q ∈ W, eval x q = 0) (t : ℂ) : ∀ q ∈ W, eval (t • x) q = 0 := by
  intro q hq
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sum_homogeneousComponent q, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [eval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous d q), hx _ (hW q hq d), mul_zero]

end PointLine


end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PPolyLocalGenerators
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Module IsLocalRing

noncomputable section

theorem PolyLocalGenerators.proof : PolyLocalGenerators.Statement := by
  intro n m J hJ hdim p hp htan
  classical

  have H := exists_polyDiff_basis J p
  rw [htan] at H
  obtain ⟨q, hqJ, hli, hspan⟩ := H
  have hqp : ∀ i, eval p (q i) = 0 := fun i => hp _ (hqJ i)
  have htq : polyTangent (Set.range q) p = polyTangent (J : Set (MvPolynomial (Fin n) ℂ)) p := by
    refine polyTangent_eq_of_subset _ _ p (by rintro _ ⟨i, rfl⟩; exact hqJ i) fun f hf => ?_
    have := hspan f hf
    rwa [Set.range_comp] at this

  set M : Ideal (MvPolynomial (Fin n) ℂ) := RingHom.ker (eval p) with hMdef
  have hevsurj : Function.Surjective (eval p : MvPolynomial (Fin n) ℂ →+* ℂ) :=
    fun c => ⟨C c, by simp⟩
  have hMmax : M.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj
  have : J.IsPrime := hJ
  let ev : (MvPolynomial (Fin n) ℂ ⧸ J) →+* ℂ := Ideal.Quotient.lift J (eval p) (fun x hx => hp x hx)
  set N : Ideal (MvPolynomial (Fin n) ℂ ⧸ J) := RingHom.ker ev with hNdef
  have hevsurj' : Function.Surjective ev :=
    fun c => ⟨Ideal.Quotient.mk J (C c), by simp [ev]⟩
  have hNmax : N.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hevsurj'
  have hNM : N.comap (Ideal.Quotient.mk J) = M := by
    ext x
    simp only [Ideal.mem_comap, hNdef, hMdef, RingHom.mem_ker, ev, Ideal.Quotient.lift_mk]

  let P := Localization.AtPrime M
  let S := Localization.AtPrime N
  let ψ : P →+* S := Localization.localRingHom M N (Ideal.Quotient.mk J) hNM.symm
  let _ : Algebra P S := ψ.toAlgebra
  have halg : ∀ x, algebraMap P S x = ψ x := fun _ => rfl
  have hψmk : ∀ x, ψ (algebraMap (MvPolynomial (Fin n) ℂ) P x) =
      algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S (Ideal.Quotient.mk J x) :=
    fun x => Localization.localRingHom_to_map M N (Ideal.Quotient.mk J) hNM.symm x
  have hsurj : Function.Surjective (algebraMap P S) := by
    intro z
    obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq N.primeCompl z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hyM : y ∈ M.primeCompl := by
      intro hyM'
      have hyN : y ∈ N.comap (Ideal.Quotient.mk J) := by rw [hNM]; exact hyM'
      apply t.2
      rw [← hy]
      exact hyN
    refine ⟨IsLocalization.mk' P x ⟨y, hyM⟩, ?_⟩
    rw [halg, Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hy

  have hdimS : ringKrullDim S = m := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height N S,
      NumbersDVR.MaximalIdealHeightFG.proof ℂ (MvPolynomial (Fin n) ℂ ⧸ J) N hNmax, hdim]

  let f : Fin (n - m) → P := fun i => algebraMap (MvPolynomial (Fin n) ℂ) P (q i)
  have hf : ∀ i, f i ∈ RingHom.ker (algebraMap P S) := by
    intro i
    rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i), map_zero]
  have hmP : maximalIdeal P = M.map (algebraMap (MvPolynomial (Fin n) ℂ) P) :=
    (Localization.AtPrime.map_eq_maximalIdeal (I := M)).symm

  have hJcov : J ≤ Ideal.span (Set.range q) ⊔ M ^ 2 := fun x hx =>
    mem_span_sup_sq_of_polyDiff_mem p q hqp (hp x hx) (hspan x hx)
  obtain ⟨Cc, hCc⟩ := Submodule.exists_isCompl (Submodule.span ℂ (Set.range (polyDiff p ∘ q)))
  have hfinD : finrank ℂ (Submodule.span ℂ (Set.range (polyDiff p ∘ q))) = n - m := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← htan]
    exact (Submodule.finrank_le _).trans (Module.finrank_fin_fun ℂ).le
  have hfinC : finrank ℂ Cc = m := by
    have := Submodule.finrank_add_eq_of_isCompl hCc
    rw [hfinD, Module.finrank_fin_fun] at this
    omega
  let c := Module.finBasisOfFinrankEq ℂ Cc hfinC
  let y : Fin m → MvPolynomial (Fin n) ℂ := fun k => tanLinPoly p (c k)
  have hMcov : M ≤ Ideal.span (Set.range (Sum.elim q y)) ⊔ M ^ 2 := by
    intro x hx
    refine mem_span_sup_sq_of_polyDiff_mem p (Sum.elim q y) ?_ (RingHom.mem_ker.1 hx) ?_
    · rintro (i | k)
      · exact hqp i
      · exact eval_tanLinPoly p _
    · have htop : Submodule.span ℂ (Set.range (polyDiff p ∘ Sum.elim q y)) = ⊤ := by
        rw [eq_top_iff, ← hCc.sup_eq_top]
        apply sup_le
        · apply Submodule.span_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨Sum.inl i, rfl⟩
        · intro v hv
          have hCspan : Cc = Submodule.span ℂ (Set.range (Cc.subtype ∘ c)) := by
            rw [Set.range_comp, Submodule.span_image, c.span_eq, Submodule.map_subtype_top]
          rw [hCspan] at hv
          refine Submodule.span_mono ?_ hv
          rintro _ ⟨k, rfl⟩
          exact ⟨Sum.inr k, by simp [y, polyDiff_tanLinPoly]⟩
      rw [htop]
      exact Submodule.mem_top

  let φ : MvPolynomial (Fin n) ℂ →+* S :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S).comp (Ideal.Quotient.mk J)
  have hmS : maximalIdeal S = M.map φ := by
    calc maximalIdeal S = N.map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) :=
          (Localization.AtPrime.map_eq_maximalIdeal (I := N)).symm
      _ = (M.map (Ideal.Quotient.mk J)).map (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) S) := by
          rw [← hNM, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
      _ = M.map φ := Ideal.map_map _ _
  have hφq : ∀ i, φ (q i) = 0 := by
    intro i
    simp [φ, Ideal.Quotient.eq_zero_iff_mem.2 (hqJ i)]
  have hS_le : maximalIdeal S ≤ Ideal.span (Set.range (φ ∘ y)) := by
    refine maximalIdeal_le_span_of_le_sup_sq (R := S) (Set.range (φ ∘ y)) ?_
    rw [hmS]
    have h1 := Ideal.map_mono (f := φ) hMcov
    rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow] at h1
    refine h1.trans (sup_le_sup ?_ ?_)
    · refine Ideal.span_le.2 ?_
      rintro _ ⟨_, ⟨i | k, rfl⟩, rfl⟩
      · simp [hφq]
      · exact Ideal.subset_span ⟨k, rfl⟩
    · exact le_rfl
  have hμ : (maximalIdeal S).spanFinrank ≤ m := by
    have heq : maximalIdeal S = Ideal.span (Set.range (φ ∘ y)) := by
      refine le_antisymm hS_le (Ideal.span_le.2 ?_)
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, hmS]
      exact Ideal.mem_map_of_mem _ (RingHom.mem_ker.2 (eval_tanLinPoly p _))
    rw [heq]
    calc (Ideal.span (Set.range (φ ∘ y))).spanFinrank ≤ (Set.range (φ ∘ y)).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ (Set.univ : Set (Fin m)).ncard := by
          rw [← Set.image_univ]
          exact Set.ncard_image_le Set.finite_univ
      _ = m := by simp [Set.ncard_univ]

  have hcov : RingHom.ker (algebraMap P S) ≤ Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
    intro z hz
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M.primeCompl z
    have hx0 : algebraMap P S (algebraMap (MvPolynomial (Fin n) ℂ) P x) = 0 := by
      rw [← IsLocalization.mk'_spec P x s, map_mul, RingHom.mem_ker.1 hz, zero_mul]
    rw [halg, hψmk] at hx0
    obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff N.primeCompl S _).1 hx0
    obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (t : MvPolynomial (Fin n) ℂ ⧸ J)
    have hwx : w * x ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hw, ht]
    have hwJ : w ∉ J := by
      intro hwJ
      apply t.2
      rw [← hw, Ideal.Quotient.eq_zero_iff_mem.2 hwJ]
      exact zero_mem _
    have hxJ : x ∈ J := (hJ.mem_or_mem hwx).resolve_left hwJ
    have hx' : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈
        Ideal.span (Set.range f) ⊔ maximalIdeal P ^ 2 := by
      have h1 := Ideal.mem_map_of_mem (algebraMap (MvPolynomial (Fin n) ℂ) P) (hJcov hxJ)
      rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, ← hmP, ← Set.range_comp] at h1
      exact h1
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ hx'

  have hker := GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le (P := P) (S := S) hsurj f hf hcov
    m hμ hdimS.ge

  have hloc : ∀ x ∈ J, ∃ s ∈ M.primeCompl, s * x ∈ Ideal.span (Set.range q) := by
    intro x hx
    have hx1 : algebraMap (MvPolynomial (Fin n) ℂ) P x ∈ Ideal.span (Set.range f) := by
      apply hker
      rw [RingHom.mem_ker, halg, hψmk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    have hspanf : Ideal.span (Set.range f) =
        (Ideal.span (Set.range q)).map (algebraMap (MvPolynomial (Fin n) ℂ) P) := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [hspanf] at hx1
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff M.primeCompl P).1 hx1
    rw [← map_mul, IsLocalization.eq_iff_exists M.primeCompl P] at e
    obtain ⟨c', hc'⟩ := e
    refine ⟨c' * s, M.primeCompl.mul_mem c'.2 hs, ?_⟩
    have e2 : (c' : MvPolynomial (Fin n) ℂ) * s * x = c' * a := by
      rw [← hc']
      ring
    rw [e2]
    exact Ideal.mul_mem_left _ _ ha
  choose! σ hσM hσ using hloc
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing J
  have hsJ : ∀ x ∈ s, x ∈ J := fun x hx => by
    rw [← hs]
    exact Submodule.subset_span hx
  refine ⟨q, ∏ x ∈ s, σ x, hqJ, ?_, ?_, ?_⟩
  · rw [map_prod]
    refine Finset.prod_ne_zero_iff.2 fun x hx h0 => ?_
    exact hσM x (hsJ x hx) (RingHom.mem_ker.2 h0)
  · rw [htq, htan]
  · intro r hr
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (MvPolynomial (Fin n) ℂ) (∏ x ∈ s, σ x))
        (Ideal.span (Set.range q)) := by
      rw [← hs]
      refine Submodule.span_le.2 fun x hx => ?_
      have hxJ := hsJ x hx
      show (∏ x ∈ s, σ x) * x ∈ Ideal.span (Set.range q)
      rw [← Finset.mul_prod_erase s σ hx,
        show σ x * (∏ y ∈ s.erase x, σ y) * x = (∏ y ∈ s.erase x, σ y) * (σ x * x) by ring]
      exact Ideal.mul_mem_left _ _ (hσ x hxJ)
    exact hle hr

end

end GroundTheory.Heights₂.Heights
end

