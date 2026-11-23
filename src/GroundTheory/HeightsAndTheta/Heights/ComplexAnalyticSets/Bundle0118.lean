module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0117
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0094
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchFillDimension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology MeasureTheory

noncomputable section

namespace BranchFillDimension

theorem hausdorffMeasure_pos_of_isOpen {d : ℕ} {V : Set (Fin d → ℂ)} (hV : IsOpen V)
    (hne : V.Nonempty) : 0 < μH[((2 * d : ℕ) : ℝ)] V := by
  have hr : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [← hr]
  exact hV.measure_pos _ hne

theorem not_open_subset_image {k d : ℕ} (hkd : k < d) {U : Set (Fin k → ℂ)} (hU : IsOpen U)
    {F : (Fin k → ℂ) → Fin d → ℂ} (hF : DifferentiableOn ℂ F U) {V : Set (Fin d → ℂ)}
    (hV : IsOpen V) (hne : V.Nonempty) : ¬ V ⊆ F '' U := by
  intro hsub
  let T : (Fin d → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castLE hkd.le i)
  have hT : ∀ u i, T u i = u (Fin.castLE hkd.le i) := fun _ _ => rfl
  have hU' : IsOpen (T ⁻¹' U) := hU.preimage T.continuous
  have hg : DifferentiableOn ℂ (F ∘ T) (T ⁻¹' U) := hF.comp T.differentiableOn (fun _ hu => hu)
  have hcrit : T ⁻¹' U ⊆ {s | s ∈ T ⁻¹' U ∧ ¬ Function.Injective (fderiv ℂ (F ∘ T) s)} := by
    intro u hu
    refine ⟨hu, fun hinj => ?_⟩
    have hTe : T (Pi.single ⟨k, hkd⟩ 1) = 0 := by
      funext i
      have hi : Fin.castLE hkd.le i ≠ ⟨k, hkd⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp [hT, hi]
    have hfd : fderiv ℂ (F ∘ T) u = (fderiv ℂ F (T u)).comp T := by
      rw [fderiv_comp u ((hF (T u) hu).differentiableAt (hU.mem_nhds hu)) T.differentiableAt,
        T.fderiv]
    have h0 : (Pi.single ⟨k, hkd⟩ (1 : ℂ) : Fin d → ℂ) = 0 :=
      hinj (by rw [hfd]; simp [hTe])
    have := congrFun h0 ⟨k, hkd⟩
    simp at this
  have hnull := CriticalImageNull.proof d d (T ⁻¹' U) (F ∘ T) hU' hg
  have hsub' : V ⊆ (F ∘ T) '' {s | s ∈ T ⁻¹' U ∧ ¬ Function.Injective (fderiv ℂ (F ∘ T) s)} := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hsub hy
    have hext : T (fun j => if hj : j.val < k then t ⟨j.val, hj⟩ else 0) = t := by
      funext i
      simp [hT]
    refine ⟨_, hcrit (show _ ∈ T ⁻¹' U from hext ▸ ht), ?_⟩
    simp only [Function.comp_apply, hext]
  exact (hausdorffMeasure_pos_of_isOpen hV hne).ne' (measure_mono_null hsub' hnull)

theorem of_fin (hHF : HolomorphicFibreInfinite.Statement) (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (h : MvPolynomial (Fin n) ℂ) (w : Fin n → ℂ) (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → Fin n → ℂ)
    (B : Set (Fin n → ℂ)) (hJ : J.IsPrime) (hh : h ∉ J) (hw : w ∈ zeroLocus J)
    (hφd : DifferentiableOn ℂ φ (Metric.ball 0 r)) (hφi : Set.InjOn φ (Metric.ball 0 r))
    (hφm : Set.MapsTo φ (Metric.ball 0 r) (zeroLocus J)) (hB : B ∈ 𝓝 w)
    (hcov : (zeroLocus J ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
    have h1 := ringKrullDim_quotient_le J
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at h0 h1 ⊢
    induction x using WithBot.recBotCoe with
    | bot => simp at h0
    | coe m =>
      induction m using ENat.recTopCoe with
      | top =>
        exfalso
        have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) := h1
        exact absurd (WithBot.coe_le_coe.1 h2) (by simp)
      | coe m => exact ⟨m, rfl⟩
  obtain ⟨A, hA⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.proof n d J hd
  let π : (Fin n → ℂ) → Fin d → ℂ := fun z => A.mulVec z
  have hπe : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = π := by
    funext z i
    simp [π, GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]
  have hπd : Differentiable ℂ π := (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  obtain ⟨z0, ⟨hz0, hhz0⟩, hz0B⟩ : ∃ z0, (z0 ∈ zeroLocus J ∧ eval z0 h ≠ 0) ∧ z0 ∈ interior B := by
    have hfreq : ∃ᶠ y in 𝓝 w, y ∈ zeroLocus J ∧ eval y h ≠ 0 := by
      intro hev
      exact hh (VanishNearPoint.proof FiniteMapOpen.proof n J h w hJ hw
        (hev.mono fun y hy hyZ => by by_contra hne; exact hy ⟨hyZ, hne⟩))
    exact (hfreq.and_eventually (interior_mem_nhds.2 hB)).exists
  have hUo : IsOpen (interior B ∩ {z | eval z h ≠ 0}) :=
    isOpen_interior.inter (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const)
  have hnb := FiniteMapOpen.proof n d J (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hJ hA.injective
    hA.finite z0 hz0 _ (hUo.mem_nhds ⟨hz0B, hhz0⟩)
  rw [hπe] at hnb
  have hsub : π '' (zeroLocus J ∩ (interior B ∩ {z | eval z h ≠ 0})) ⊆ (π ∘ φ) '' Metric.ball 0 r := by
    rintro _ ⟨z, ⟨hzZ, hzB, hzh⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hcov ⟨⟨hzZ, interior_subset hzB⟩, hzh⟩
    exact ⟨t, ht, rfl⟩
  have hΔ : (Metric.ball (0 : Fin k → ℂ) r).Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov ⟨⟨hz0, interior_subset hz0B⟩, hhz0⟩
    exact ⟨t, ht⟩
  have hle : k ≤ d := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy⟩ := hHF k d _ (π ∘ φ) hlt Metric.isOpen_ball hΔ (hπd.comp_differentiableOn hφd)
    have hfin := (GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof n d J A hJ hd hA y).2.1
    apply hy
    have hmaps : φ '' {t | t ∈ Metric.ball 0 r ∧ (π ∘ φ) t = y} ⊆
        GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y := by
      rintro _ ⟨t, ⟨ht, hty⟩, rfl⟩
      exact ⟨hφm ht, hty⟩
    exact Set.Finite.of_finite_image (hfin.subset hmaps) (hφi.mono fun t ht => ht.1)
  have hge : d ≤ k := by
    by_contra hlt
    push Not at hlt
    exact not_open_subset_image hlt Metric.isOpen_ball (hπd.comp_differentiableOn hφd) isOpen_interior
      ⟨_, mem_interior_iff_mem_nhds.2 hnb⟩ (interior_subset.trans hsub)
  rw [hd, le_antisymm hge hle]

end BranchFillDimension

theorem BranchFillDimension.proof (hHF : HolomorphicFibreInfinite.Statement) :
    BranchFillDimension.Statement := by
  intro σ _ I h w k r φ B hI hh hw hφd hφi hφm hB hcov
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let ψ : MvPolynomial σ ℂ ≃+* MvPolynomial (Fin (Fintype.card σ)) ℂ := (renameEquiv ℂ e).toRingEquiv
  have hψ : ∀ q, ψ q = rename e q := fun _ => rfl
  have hψs : ∀ q, ψ.symm q = rename e.symm q := fun _ => rfl
  let J : Ideal (MvPolynomial (Fin (Fintype.card σ)) ℂ) := I.comap ψ.symm
  have hJ : J.IsPrime := Ideal.comap_isPrime _ _
  have hmemJ : ∀ q, q ∈ J ↔ ψ.symm q ∈ I := fun _ => Iff.rfl
  let L : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (e.symm i)
  let M : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ) :=
    ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (e s)
  have hLM : ∀ x, L (M x) = x := fun x => funext fun i => by simp [L, M]
  have hML : ∀ z, M (L z) = z := fun z => funext fun s => by simp [L, M]
  have heval : ∀ z q, eval (L z) (ψ q) = eval z q := by
    intro z q
    have hc : L z ∘ e = z := funext fun s => by simp [L]
    rw [hψ, eval_rename, hc]
  have hZ : ∀ z, L z ∈ zeroLocus J ↔ z ∈ zeroSetIn I := by
    intro z
    constructor
    · intro hz q hq
      rw [← heval]
      exact hz _ (by rw [hmemJ, RingEquiv.symm_apply_apply]; exact hq)
    · intro hz q hq
      rw [← ψ.apply_symm_apply q, heval]
      exact hz _ ((hmemJ q).1 hq)
  have hdim : ringKrullDim (MvPolynomial σ ℂ ⧸ I) = ringKrullDim (MvPolynomial (Fin (Fintype.card σ)) ℂ ⧸ J) :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J ψ (Ideal.comap_symm (I := I) ψ))
  rw [hdim]
  refine BranchFillDimension.of_fin hHF _ J (ψ h) (L w) k r (L ∘ φ) (M ⁻¹' B) hJ ?_ ((hZ w).2 hw)
    (L.differentiable.comp_differentiableOn hφd) ?_ ?_ ?_ ?_
  · rw [hmemJ, RingEquiv.symm_apply_apply]
    exact hh
  · intro t ht t' ht' htt
    exact hφi ht ht' (by simpa [hML] using congrArg M htt)
  · intro t ht
    exact (hZ _).2 (hφm ht)
  · exact M.continuous.continuousAt.preimage_mem_nhds (by rwa [hML])
  · rintro x ⟨⟨hxZ, hxB⟩, hxh⟩
    rw [← hLM x] at hxZ hxh
    obtain ⟨t, ht, hteq⟩ := hcov ⟨⟨(hZ _).1 hxZ, hxB⟩, fun h0 => hxh (by simpa [heval] using h0)⟩
    exact ⟨t, ht, by simp [hteq, hLM]⟩

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

namespace BranchOffHypersurface

theorem eval_eq_zero_of_mem_sup {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {b : MvPolynomial (Fin n) ℂ}
    {x : Fin n → ℂ} (hx : x ∈ zeroSetIn J) (hb : eval x b = 0) :
    ∀ q ∈ J ⊔ Ideal.span {b}, eval x q = 0 := by
  have h : J ⊔ Ideal.span {b} ≤ RingHom.ker (eval x) := by
    refine sup_le (fun q hq => RingHom.mem_ker.2 (hx q hq)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact RingHom.mem_ker.2 hb
  exact fun q hq => RingHom.mem_ker.1 (h hq)

theorem ringKrullDim_sup_span_add_one_le {R : Type*} [CommRing R] {Q : Ideal R} [Q.IsPrime] {x : R}
    (hxQ : x ∉ Q) : ringKrullDim (R ⧸ (Q ⊔ Ideal.span {x})) + 1 ≤ ringKrullDim (R ⧸ Q) := by
  have hle : Q ≤ Q ⊔ Ideal.span {x} := le_sup_left
  have hx : x ∈ Q ⊔ Ideal.span {x} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
  have hr : Ideal.Quotient.mk Q x ∈ nonZeroDivisors (R ⧸ Q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  refine ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ (Ideal.Quotient.factor hle) ?_)
    (Ideal.Quotient.lift_surjective_of_surjective _ _ (Ideal.Quotient.factor_surjective hle))
  intro y hy
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  rw [map_mul]
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  simp only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, mul_zero]

theorem eval_comp_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (x : Fin n → ℂ) :
    (eval x).comp (GroundTheory.Heights₂.Heights.ComplexSets.pullback A).toRingHom = eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro a; simp [GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.pullback, GroundTheory.Heights₂.Heights.ComplexSets.linPoly,
      Matrix.mulVec, dotProduct]

theorem fibre_finite {n d : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection I A) (y : Fin d → ℂ) :
    {x : Fin n → ℂ | (∀ q ∈ I, eval x q = 0) ∧ A.mulVec x = y}.Finite := by
  classical
  let _ : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (GroundTheory.Heights₂.Heights.ComplexSets.projHom I A).toRingHom.toAlgebra
  let _ : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := Algebra.toModule
  have : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := hA.finite
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    Algebra.IsIntegral.of_finite _ _
  have key : ∀ i : Fin n, ∃ f : Polynomial (MvPolynomial (Fin d) ℂ), f.Monic ∧
      Polynomial.eval₂ (GroundTheory.Heights₂.Heights.ComplexSets.pullback A).toRingHom (X i) f ∈ I := by
    intro i
    obtain ⟨f, hfm, hf⟩ :=
      Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) (Ideal.Quotient.mk I (X i))
    refine ⟨f, hfm, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, Polynomial.hom_eval₂]
    exact hf
  choose f hfm hfI using key
  refine (Set.Finite.pi (t := fun i => {z : ℂ | z ∈ ((f i).map (eval y)).roots})
    (fun i => Multiset.finite_toSet _)).subset ?_
  rintro x ⟨hx, hAx⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro i
  have h0 := hx _ (hfI i)
  rw [Polynomial.hom_eval₂, eval_comp_pullback, hAx, eval_X] at h0
  rw [Polynomial.mem_roots ((hfm i).map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map]
  exact h0

theorem proof (hF : HolomorphicFibreInfinite.Statement) : BranchOffHypersurface.Statement := by
  intro n k J b U φ hJ hdim hb hU hne hφd hφi hφJ
  by_contra hall
  push Not at hall
  have hZ : ∀ t ∈ U, ∀ q ∈ J ⊔ Ideal.span {b}, eval (φ t) q = 0 :=
    fun t ht => eval_eq_zero_of_mem_sup (hφJ ht) (hall t ht)
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) + 1 ≤ (k : WithBot ℕ∞) :=
    hdim ▸ ringKrullDim_sup_span_add_one_le hb
  obtain ⟨t₀, ht₀⟩ := hne
  have hI : J ⊔ Ideal.span {b} ≠ ⊤ := by
    intro h
    have h1 := hZ t₀ ht₀ 1 (h ▸ Submodule.mem_top)
    simp at h1
  have : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) :=
    ringKrullDim_nonneg_of_nontrivial
  have hlek : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {b})) ≤ (k : WithBot ℕ∞) :=
    le_trans (le_add_of_nonneg_right zero_le_one) hle
  obtain ⟨d, -, hd⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.exists_nat_of_le h0 hlek
  have hdk : d < k := by
    rw [hd] at hle
    have : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (k : WithBot ℕ∞) := by exact_mod_cast hle
    have := WithBot.coe_le_coe.mp this
    exact_mod_cast this
  obtain ⟨A, hA⟩ := GroundTheory.Heights₂.Heights.ComplexSets.LinearNoetherNormalization.proof n d _ hd
  have hL : Differentiable ℂ (fun x : Fin n → ℂ => A.mulVec x) :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
  obtain ⟨y, hy⟩ := hF k d U (fun t => A.mulVec (φ t)) hdk hU ⟨t₀, ht₀⟩ (hL.comp_differentiableOn hφd)
  apply hy
  refine Set.Finite.of_finite_image ((fibre_finite _ A hA y).subset ?_) (hφi.mono fun t ht => ht.1)
  rintro _ ⟨t, ⟨ht, hty⟩, rfl⟩
  exact ⟨hZ t ht, hty⟩

end BranchOffHypersurface

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranchInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace SliceBranchInt

open ReciprocityTheory.AnForm.A (hypIncl)

theorem norm_hypIncl {d : ℕ} (w : Fin d → ℂ) : ‖hypIncl w‖ = ‖w‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [hypIncl]
    · simpa [hypIncl] using norm_le_pi_norm w j
  · simpa [hypIncl] using norm_le_pi_norm (hypIncl w) j.succ

theorem differentiable_hypIncl {d : ℕ} : Differentiable ℂ (hypIncl : (Fin d → ℂ) → Fin (d + 1) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [hypIncl, Fin.cons_zero]
    exact differentiable_const _
  · simp only [hypIncl, Fin.cons_succ]
    exact differentiable_apply j

theorem hypIncl_tail {d : ℕ} (t : Fin (d + 1) → ℂ) (ht : t 0 = 0) :
    hypIncl (Fin.tail t) = t ∧ ‖Fin.tail t‖ ≤ ‖t‖ := by
  refine ⟨?_, (pi_norm_le_iff_of_nonneg (norm_nonneg t)).2 fun j => norm_le_pi_norm t j.succ⟩
  rw [hypIncl, ← ht]
  exact Fin.cons_self_tail t

end SliceBranchInt


open ReciprocityTheory.AnForm.A (hypIncl densHyp) in
theorem SliceBranchInt.proof (hBP : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement)
    (hPCI : ParamChartInt.Statement) : SliceBranchInt.Statement := by
  classical
  intro n d J W u q m γ ord hJ hdim hu hW hq ⟨N₁, hN₁, h₁⟩ hcov ⟨N₃, hN₃, h₃⟩ hmeet hord
  have hWdim := IndefiniteRowSideFullHecke.ComplexSets.dim_component_linForm hJ hdim hu hW
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hex := ComplexSets.LinearNoetherNormalization.proof n d W hWdim
  have hr : ∀ b, 0 < (γ b).radius / 2 := fun b => half_pos (γ b).radius_pos
  have hP := fun b => hBP n (d + 1) J u q q m γ hJ hdim hu hcov hmeet b 0
    (Metric.mem_ball_self (γ b).radius_pos) (γ b).map_zero _ (Metric.closedBall_mem_nhds 0 (hr b))
  choose ε hε hprop using hP
  set N := interior N₁ ∩ interior N₃ ∩ ⋂ b, Metric.ball q (ε b) with hNdef
  have hNo : IsOpen N :=
    (isOpen_interior.inter isOpen_interior).inter (isOpen_iInter_of_finite fun b => Metric.isOpen_ball)
  refine ⟨N, hNo.mem_nhds ⟨⟨mem_interior_iff_mem_nhds.2 hN₁, mem_interior_iff_mem_nhds.2 hN₃⟩,
    Set.mem_iInter.2 fun b => Metric.mem_ball_self (hε b)⟩, fun b f φ hf hfc hfN hφ => ?_⟩

  have huq : linEval u q = 0 := by
    have := hq _ ((le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self (linForm u)))
    simpa [linForm, linEval] using this
  obtain ⟨H, -, hH0, hHF⟩ := hord b
  have hHF' : ∀ t ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      linEval u ((γ b).toFun t) = t 0 ^ ord b * H t := hHF
  have hord0 : ord b ≠ 0 := by
    intro h0
    have := hHF' 0 (Metric.mem_ball_self (γ b).radius_pos)
    rw [(γ b).map_zero, huq, h0, pow_zero, one_mul] at this
    exact hH0 0 (Metric.mem_ball_self (γ b).radius_pos) this.symm
  have hball : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius, hypIncl w ∈ Metric.ball 0 (γ b).radius :=
    fun w hw => by rwa [Metric.mem_ball, dist_zero_right, SliceBranchInt.norm_hypIncl, ← dist_zero_right]
  have hA := hPCI n d W hex.choose (fun w => (γ b).toFun (hypIncl w)) (γ b).radius ((γ b).radius / 2) N
    hW.1.1 hWdim hex.choose_spec
    ((γ b).differentiableOn.comp SliceBranchInt.differentiable_hypIncl.differentiableOn hball)
    (fun w hw w' hw' h => by
      have := (γ b).injOn (hball w hw) (hball w' hw') h
      simpa [hypIncl] using congrArg Fin.tail this)
    hNo (half_lt_self (γ b).radius_pos) (fun w hw hN => ⟨h₁ _ ⟨(γ b).mapsTo (hball w hw),
        interior_subset hN.1.1⟩ (by rw [hHF' _ (hball w hw), ReciprocityTheory.AnForm.A.hypIncl_zero,
          zero_pow hord0, zero_mul]), ?_⟩)
    (fun x hx => ?_) f φ hf hfc hfN
    (fun i => by
      obtain ⟨U, hU, hS, hc⟩ := hφ i
      exact ⟨U, hU, (show zeroSet W ⊆ zeroSet J from fun x hx p hp => hx p (hJW hp)).trans hS, hc⟩)
  · unfold varInt
    rw [dite_eq_left hex, hA]
    rfl
  · have h2 := hprop b (hypIncl w) (hball w hw) (Set.mem_iInter.1 hN.2 b)
    rwa [Metric.mem_closedBall, dist_zero_right, SliceBranchInt.norm_hypIncl] at h2
  · obtain ⟨t, ⟨ht, ht0⟩, rfl⟩ := h₃ b ⟨hx.1, interior_subset hx.2.1.2⟩
    obtain ⟨h1, h2⟩ := SliceBranchInt.hypIncl_tail t ht0
    refine ⟨Fin.tail t, ?_, show (γ b).toFun (hypIncl (Fin.tail t)) = _ by rw [h1]⟩
    rw [Metric.mem_ball, dist_zero_right] at ht ⊢
    exact h2.trans_lt ht

end

end GroundTheory.Heights₂.Heights
end

