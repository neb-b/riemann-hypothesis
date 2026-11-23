module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0067

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

namespace InjectiveHolomorphicJacobianNeZero

theorem det_fin_one (A : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) : LinearMap.det A = A 1 0 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 1)), Matrix.det_unique, LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_apply, Pi.basisFun_repr]
  have h1 : (Pi.single (default : Fin 1) (1 : ℂ) : Fin 1 → ℂ) = 1 := by
    funext i
    fin_cases i
    rfl
  rw [h1]
  rfl

theorem one {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne

end InjectiveHolomorphicJacobianNeZero

theorem InjectiveHolomorphicJacobianNeZero.proof (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem IsolatedFibreNear.proof (hFin : CompactHolomorphicFibreFinite.Statement) :
    IsolatedFibreNear.Statement := by
  intro σ _ X w d A hX hiso
  obtain ⟨N, k, f, hN, hwN, hf, hXN⟩ := hX
  obtain ⟨W, hW, hWiso⟩ := hiso
  have memX : ∀ z, z ∈ N → (∀ i, f i z = 0) → z ∈ X := fun z hz h0 => by
    have : z ∈ X ∩ N := by rw [hXN]; exact ⟨hz, h0⟩
    exact this.1
  have zerosX : ∀ z, z ∈ X → z ∈ N → ∀ i, f i z = 0 := fun z hzX hzN => by
    have : z ∈ X ∩ N := ⟨hzX, hzN⟩
    rw [hXN] at this
    exact this.2
  obtain ⟨r, hr, hrsub⟩ := (nhds_basis_closedBall (x := w)).mem_iff.1 (inter_mem (hN.mem_nhds hwN) hW)
  have hBN : closedBall w r ⊆ N := fun z hz => (hrsub hz).1
  have hBW : closedBall w r ⊆ W := fun z hz => (hrsub hz).2

  set g : (σ → ℂ) → (Fin k → ℂ) := fun z i => f i z with hg
  have hgc : ContinuousOn g (closedBall w r) :=
    continuousOn_pi.2 fun i => ((hf i).continuousOn).mono hBN
  set K := sphere w r ∩ g ⁻¹' {0} with hK
  have hKc : IsCompact K := by
    refine (isCompact_sphere w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.mono sphere_subset_closedBall).preimage_isClosed_of_isClosed isClosed_sphere isClosed_singleton
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, ⟨hzs, hz0⟩, hzA⟩
    have hzB : z ∈ closedBall w r := sphere_subset_closedBall hzs
    have hz0' : ∀ i, f i z = 0 := fun i => congrFun hz0 i
    have hzw : z = w := hWiso z ⟨memX z (hBN hzB) hz0', hBW hzB⟩ hzA
    rw [mem_sphere, hzw, dist_self] at hzs
    exact hr.ne hzs
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.1 ((hKc.image A.continuous).isClosed.isOpen_compl) (A w) hAK
  refine ⟨ball w r ∩ A ⁻¹' ball (A w) ε, ?_, ?_⟩
  · exact inter_mem (ball_mem_nhds w hr) (A.continuous.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε))
  rintro x ⟨hxX, hxB, hxD⟩

  set F := {z | z ∈ ball w r ∧ (∀ i, f i z = 0) ∧ A z = A x} with hF
  have hFeq : F = closedBall w r ∩ (fun z => (g z, A z)) ⁻¹' {(0, A x)} := by
    ext z
    simp only [hF, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, hg, funext_iff, Pi.zero_apply]
    constructor
    · rintro ⟨hzb, h0, hzA⟩
      exact ⟨ball_subset_closedBall hzb, h0, hzA⟩
    · rintro ⟨hzb, h0, hzA⟩
      refine ⟨?_, h0, hzA⟩
      rcases (mem_closedBall.1 hzb).lt_or_eq with hlt | heq
      · exact mem_ball.2 hlt
      · exfalso
        have hzK : z ∈ K := ⟨mem_sphere.2 heq, by funext i; exact h0 i⟩
        apply hεsub (show A z ∈ ball (A w) ε by rw [funext hzA]; exact hxD)
        exact ⟨z, hzK, rfl⟩
  have hFc : IsCompact F := by
    rw [hFeq]
    refine (isCompact_closedBall w r).of_isClosed_subset ?_ Set.inter_subset_left
    exact (hgc.prodMk A.continuous.continuousOn).preimage_isClosed_of_isClosed isClosed_closedBall
      isClosed_singleton

  set n := Fintype.card σ
  let L : (σ → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin n => ℂ) (Fintype.equivFin σ)
  set U : Set (Fin n → ℂ) := L.symm ⁻¹' ball w r with hU
  set h : (Fin n → ℂ) → Fin (k + d) → ℂ :=
    fun v => Fin.append (fun i => f i (L.symm v)) (A (L.symm v)) with hh
  set y : Fin (k + d) → ℂ := Fin.append (0 : Fin k → ℂ) (A x) with hy
  have hUo : IsOpen U := isOpen_ball.preimage L.symm.continuous
  have hhd : DifferentiableOn ℂ h U := by
    refine differentiableOn_pi.2 fun j => ?_
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [hh, Fin.append_left]
      exact ((hf i).differentiableOn.mono (ball_subset_closedBall.trans hBN)).comp
        L.symm.differentiable.differentiableOn (fun v hv => hv)
    · simp only [hh, Fin.append_right]
      exact ((differentiable_apply (𝕜 := ℂ) j).comp
        (A.differentiable.comp L.symm.differentiable)).differentiableOn
  have hfib : {v | v ∈ U ∧ h v = y} = L.symm ⁻¹' F := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hU, hF, hh, hy]
    constructor
    · rintro ⟨hv, he⟩
      refine ⟨hv, fun i => ?_, ?_⟩
      · simpa using congrFun he (Fin.castAdd d i)
      · funext j
        simpa using congrFun he (Fin.natAdd k j)
    · rintro ⟨hv, h0, hA⟩
      refine ⟨hv, funext fun j => ?_⟩
      refine Fin.addCases (fun i => ?_) (fun j => ?_) j
      · simp [h0 i]
      · simp [hA]
  have hfibc : IsCompact {v | v ∈ U ∧ h v = y} := by
    rw [hfib, ← L.image_eq_preimage_symm]
    exact hFc.image L.continuous
  have hFfin : F.Finite := by
    have h1 := (hFin n (k + d) U h y hUo hhd hfibc).image L.symm
    rwa [hfib, Set.image_preimage_eq _ L.symm.surjective] at h1

  refine ⟨ball w r \ (F \ {x}), ?_, ?_⟩
  · exact (isOpen_ball.sdiff (hFfin.sdiff).isClosed).mem_nhds ⟨hxB, fun hx => hx.2 rfl⟩
  rintro x' ⟨hx'X, hx'B, hx'F⟩ hx'A
  by_contra hne
  exact hx'F ⟨⟨hx'B, zerosX x' hx'X (hBN (ball_subset_closedBall hx'B)), hx'A⟩, hne⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalBoundedQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem monic_eval_div_mul_pow {d : ℕ} (a : Fin d → ℂ) {F G : ℂ} (hG : G ≠ 0) :
    F ^ d + ∑ j : Fin d, a j * F ^ (j : ℕ) * G ^ (d - (j : ℕ)) =
      G ^ d * ((F / G) ^ d + ∑ j : Fin d, a j * (F / G) ^ (j : ℕ)) := by
  rw [mul_add, Finset.mul_sum, div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hG)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ d := j.isLt.le
  have hGd : G ^ d = G ^ (j : ℕ) * G ^ (d - (j : ℕ)) := by rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hGd, div_pow]
  field_simp

theorem NormalBoundedQuotient.proof (hwi : WeaklyHolomorphicIntegral.Statement)
    (hic : NormalGermIntegrallyClosed.Statement) : NormalBoundedQuotient.Statement := by
  intro σ _ I w N F G hI hIc hw hN hwN hF hG hnv hb

  have hhol : HolomorphicOnSubset (fun z => F z / G z) ((zeroSetIn I ∩ N) \ {z | G z = 0}) := by
    intro z hz
    refine ⟨N ∩ G ⁻¹' {0}ᶜ, hG.continuousOn.isOpen_inter_preimage hN isOpen_compl_singleton,
      ⟨hz.1.2, hz.2⟩, fun z => F z / G z, ?_, fun _ _ => rfl⟩
    have hsub : N ∩ G ⁻¹' {0}ᶜ ⊆ N := Set.inter_subset_left
    simp only [div_eq_mul_inv]
    exact (hF.mono hsub).mul ((hG.mono hsub).inv fun y (hy : y ∈ N ∩ G ⁻¹' {0}ᶜ) => hy.2)
  obtain ⟨V, hVo, hwV, hVN, d, a, ha, heq⟩ :=
    hwi σ I w N G (fun z => F z / G z) hI hIc hw hN hwN hG hnv hhol hb
  refine hic σ I w V F G d a hI hIc hw hVo hwV (hF.mono hVN) (hG.mono hVN) ha hnv ?_
  intro z hz
  rw [monic_eval_div_mul_pow (fun j => a j z) (show G z ≠ 0 from hz.2), heq z hz, mul_zero]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalMaximumPrinciple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter RealInnerProductSpace

theorem eq_of_sum_eq_nsmul_of_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (a : Fin m → E) (c : E) (hle : ∀ j, ‖a j‖ ≤ ‖c‖) (hsum : ∑ j, a j = m • c) (j : Fin m) :
    a j = c := by
  have hj : ∀ i, ⟪c, a i⟫ ≤ ‖c‖ ^ 2 := fun i =>
    (real_inner_le_norm c (a i)).trans
      (by rw [sq]; exact mul_le_mul_of_nonneg_left (hle i) (norm_nonneg c))
  have htot : ∑ i, ⟪c, a i⟫ = m * ‖c‖ ^ 2 := by
    rw [← inner_sum, hsum, ← Nat.cast_smul_eq_nsmul ℝ, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hj i))).1
    (by rw [Finset.sum_sub_distrib, htot, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sub_self]) j (Finset.mem_univ j)
  have hsq : ‖a j - c‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, real_inner_comm]
    nlinarith [hle j, norm_nonneg (a j), norm_nonneg c]
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1
    (le_antisymm hsq (sq_nonneg _))))

theorem NormalMaximumPrinciple.proof (htr : LocalTrace.Statement) : NormalMaximumPrinciple.Statement := by
  intro σ _ I w U g hI _ hw hU hg hle
  obtain ⟨k, A, B, D, m, T, hB, hwB, hBU, hD, hwD, hfib, hT, hrep⟩ := htr σ I w U g hI hw hU hg
  have hle' : ∀ z ∈ zeroSetIn I ∩ B, ‖g z‖ ≤ ‖g w‖ := fun z hz => hle z ⟨hz.1, hBU hz.2⟩

  have hTw : T (A w) = m • g w := by
    obtain ⟨x, hx, -, hTx⟩ := hrep (A w) hwD
    rw [hTx, Finset.sum_congr rfl fun j _ => congrArg g (hfib (x j) (hx j).1 (hx j).2),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  have hmax : IsLocalMax (norm ∘ T) (A w) := by
    filter_upwards [hD.mem_nhds hwD] with y hy
    obtain ⟨x, hx, -, hTx⟩ := hrep y hy
    simp only [Function.comp_apply, hTx, hTw]
    calc ‖∑ j, g (x j)‖ ≤ ∑ j, ‖g (x j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin m, ‖g w‖ := Finset.sum_le_sum fun j _ => hle' _ (hx j).1
      _ = ‖m • g w‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp [nsmul_eq_mul]
  have hconst := Complex.eventually_eq_of_isLocalMax_norm
    (Filter.eventually_of_mem (hD.mem_nhds hwD) fun y hy =>
      (hT y hy).differentiableAt (hD.mem_nhds hy)) hmax
  have hcont : Tendsto A (𝓝 w) (𝓝 (A w)) := A.continuous.tendsto w
  filter_upwards [hB.mem_nhds hwB, hcont.eventually hconst, hcont.eventually (hD.mem_nhds hwD)]
    with z hzB hzT hzD hzZ
  obtain ⟨x, hx, hcov, hTx⟩ := hrep (A z) hzD
  obtain ⟨j, rfl⟩ := hcov z ⟨hzZ, hzB⟩ rfl
  exact eq_of_sum_eq_nsmul_of_norm_le (fun i => g (x i)) (g w) (fun i => hle' _ (hx i).1)
    (by rw [← hTx, hzT, hTw]) j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

attribute [local instance] FractionRing.liftAlgebra

theorem nonempty_normalModel_of_presentation {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (R : Type)
    [CommRing R] [IsDomain R] [Algebra ℂ R] (π : MvPolynomial (Fin n) ℂ →ₐ[ℂ] R)
    (hπ : Function.Surjective π) (hker : RingHom.ker π = J) : Nonempty (NormalModel J) :=
  _root_.UpperTheory.Reformulated.B.Gc5.nonempty_normalModel_of_presentation J R π hπ hker

theorem NormalModelExists.proof : NormalModelExists.Statement := by
  intro n J hJ
  exact nonempty_normalModel_of_presentation J (MvPolynomial (Fin n) ℂ ⧸ J) (Ideal.Quotient.mkₐ ℂ J)
    (Ideal.Quotient.mkₐ_surjective ℂ J) (Ideal.Quotient.mkₐ_ker ℂ J)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem isRoot_map_eval_of_mem_zeroSetIn {n m : ℕ} {I : Ideal (MvPolynomial (Fin n ⊕ Fin m) ℂ)}
    {w : Fin n ⊕ Fin m → ℂ} (hw : w ∈ zeroSetIn I) (i : Fin m) (P : Polynomial (MvPolynomial (Fin n) ℂ))
    (hP : P.eval₂ (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom
      (X (Sum.inr i)) ∈ I) :
    (P.map (eval (firstCoords w))).IsRoot (w (Sum.inr i)) := by
  have h0 := hw _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval w).comp
      (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin m) ℂ).toRingHom =
      eval (firstCoords w) := by
    ext q
    · simp
    · simp [firstCoords]
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem norm_lt_of_isRoot_map_eval {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hPm : P.Monic)
    (x : Fin n → ℂ) {a : ℂ} (ha : (P.map (eval x)).IsRoot a) :
    ‖a‖ < 1 + ∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖ := by
  have hQm : (P.map (eval x)).Monic := hPm.map _
  have hlt := Polynomial.IsRoot.norm_lt_cauchyBound hQm.ne_zero ha
  have hcb : Polynomial.cauchyBound (P.map (eval x)) ≤
      (∑ j ∈ Finset.range P.natDegree, ‖eval x (P.coeff j)‖₊) + 1 := by
    rw [Polynomial.cauchyBound, hQm.leadingCoeff, nnnorm_one, div_one, hPm.natDegree_map]
    gcongr
    refine Finset.sup_le fun j hj => ?_
    rw [Polynomial.coeff_map]
    exact Finset.single_le_sum (f := fun j => ‖eval x (P.coeff j)‖₊) (fun _ _ => zero_le) hj
  have h := hlt.trans_le hcb
  rw [← NNReal.coe_lt_coe, NNReal.coe_add, NNReal.coe_sum, coe_nnnorm, NNReal.coe_one] at h
  simp only [coe_nnnorm] at h
  linarith

theorem NormalModelProper.proof : NormalModelProper.Statement := by
  intro n J M K hK
  choose P hPm hP using M.integral
  set f : (Fin n → ℂ) → ℝ := fun x =>
    ∑ i, ∑ j ∈ Finset.range (P i).natDegree, ‖eval x ((P i).coeff j)‖ with hf
  have hfc : Continuous f := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (MvPolynomial.continuous_eval _).norm
  obtain ⟨C, hC⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK
  refine isBounded_iff_forall_norm_le.2 ⟨max R (1 + C), fun w hw => ?_⟩
  obtain ⟨hwZ, hwK⟩ := hw
  have hxR : ‖firstCoords w‖ ≤ R := hR _ hwK
  have hR0 : 0 ≤ max R (1 + C) := (norm_nonneg _).trans (hxR.trans (le_max_left _ _))
  refine (pi_norm_le_iff_of_nonneg hR0).2 fun s => ?_
  rcases s with j | i
  · exact ((norm_le_pi_norm (firstCoords w) j).trans hxR).trans (le_max_left _ _)
  · have hroot := isRoot_map_eval_of_mem_zeroSetIn hwZ i (P i) (hP i)
    have hlt := norm_lt_of_isRoot_map_eval (hPm i) (firstCoords w) hroot
    have hfi : ∑ j ∈ Finset.range (P i).natDegree, ‖eval (firstCoords w) ((P i).coeff j)‖ ≤
        f (firstCoords w) :=
      Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (P i).natDegree,
        ‖eval (firstCoords w) ((P i).coeff j)‖) (fun i _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.mem_univ i)
    have hfC : f (firstCoords w) ≤ C := by
      have := hC _ (subset_closure hwK)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    exact (hlt.le.trans (by linarith)).trans (le_max_right _ _)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalRiemannExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology

theorem NormalRiemannExtension.proof (hloc : NormalRiemannExtensionLocal.Statement)
    (hirr : NormalLocallyIrreducible.Statement) : NormalRiemannExtension.Statement := by
  intro σ _ I h U f hI hIc hh hU hf hb
  classical
  have hex : ∀ w ∈ zeroSetIn I ∩ U, ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ V ⊆ U ∧
      ∃ F : (σ → ℂ) → ℂ, DifferentiableOn ℂ F V ∧
        Set.EqOn F f ((zeroSetIn I ∩ V) \ {z | eval z h = 0}) := fun w hw =>
    hloc σ I h w U f hI hIc hh hw.1 (hU.mem_nhds hw.2) hf hb
  choose! V hVo hwV hVU F hF hFf using hex

  have hagree : ∀ w ∈ zeroSetIn I ∩ U, ∀ y ∈ zeroSetIn I ∩ U, y ∈ V w → F y y = F w y := by
    intro w hw y hy hyw
    have hWo : IsOpen (V y ∩ V w) := (hVo y hy).inter (hVo w hw)
    obtain ⟨B, -, hyB, hBW, -, hdense⟩ :=
      hirr σ I h y hI hIc hh hy.1 (V y ∩ V w) (hWo.mem_nhds ⟨hwV y hy, hyw⟩)
    set S := (zeroSetIn I ∩ B) \ {z | eval z h = 0}
    have hSW : insert y S ⊆ V y ∩ V w :=
      Set.insert_subset_iff.2 ⟨⟨hwV y hy, hyw⟩, fun z hz => hBW hz.1.2⟩
    have heq : Set.EqOn (F y) (F w) S := fun z hz => by
      have hzW := hBW hz.1.2
      rw [hFf y hy ⟨⟨hz.1.1, hzW.1⟩, hz.2⟩, hFf w hw ⟨⟨hz.1.1, hzW.2⟩, hz.2⟩]
    exact heq.of_subset_closure ((hF y hy).continuousOn.mono fun z hz => (hSW hz).1)
      ((hF w hw).continuousOn.mono fun z hz => (hSW hz).2) (Set.subset_insert y S)
      (Set.insert_subset_iff.2 ⟨hdense ⟨hy.1, hyB⟩, subset_closure⟩) (Set.mem_insert y S)
  refine ⟨fun z => if z ∈ zeroSetIn I ∩ U then F z z else f z, ?_, ?_⟩
  · intro w hw
    refine ⟨V w, hVo w hw, hwV w hw, F w, hF w hw, fun y hy => ?_⟩
    simp only [if_pos hy.1]
    exact hagree w hw y hy.1 hy.2
  · intro z hz
    simp only [if_pos hz.1]
    exact hFf z hz.1 ⟨⟨hz.1.1, hwV z hz.1⟩, hz.2⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticGermsNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def AnalyticGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

