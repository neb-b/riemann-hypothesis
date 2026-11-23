module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
section
open MeasureTheory

namespace GlobalTheory.SeparatingCharacters


open MeasureTheory in
open scoped Pointwise in
theorem _root_.GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → (∀ a, ∫ x in 𝓕, χ a x * Φ x ∂μ = 0) → Φ = 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hKΓ A _ χ hχc hχx hχa hχ0 hχn hsep μ 𝓕 hμ h𝓕 Φ hΦc hΦp hcoef
  classical
  haveI : Countable Γ := Set.countable_univ_iff.mp isLindelof_univ.countable_of_discrete

  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [add_comm, hχx, (hsep γ).2 hγ a, mul_one]
  have hinv : ∀ {f : G → ℂ}, (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
    intro f hf x y hxy
    have h := QuotientAddGroup.leftRel_apply.mp hxy
    rw [← hf _ h x]
    congr 1
    abel
  haveI : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have : (Set.univ : Set (G ⧸ Γ)) = QuotientAddGroup.mk '' K := by
      refine (Set.eq_univ_of_forall fun q => ?_).symm
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨γ, hγ, hx⟩ := hKΓ x
      refine ⟨γ + x, hx, ?_⟩
      rw [QuotientAddGroup.eq]
      simpa using Γ.neg_mem hγ
    rw [this]
    exact hK.image QuotientAddGroup.continuous_mk

  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦc.continuousOn
    refine ⟨C, fun x => ?_⟩
    obtain ⟨γ, hγ, hx⟩ := hKΓ x
    rw [← hΦp γ hγ x]
    exact hC _ hx
  have h𝓕fin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hKΓ μ h𝓕

  let ψ : A → C(G ⧸ Γ, ℂ) := fun a =>
    ⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) (χ a) (hinv (hχper a)),
      (hχc a).quotient_lift _⟩
  have hψ : ∀ a (x : G), ψ a (x : G ⧸ Γ) = χ a x := fun _ _ => rfl
  have hψmul : ∀ a b, ψ a * ψ b = ψ (a + b) := by
    intro a b
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [ContinuousMap.mul_apply, hψ, hψ, hψ, hχa]
  have hψ0 : ψ 0 = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hψ, hχ0, ContinuousMap.one_apply]
  have hψstar : ∀ a, star (ψ a) = ψ (-a) := by
    intro a
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [ContinuousMap.star_apply, hψ, hψ]
    have hz : χ a x ≠ 0 := by
      intro h
      have := hχn a x
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have h1 : χ (-a) x * χ a x = 1 := by rw [← hχa, neg_add_cancel, hχ0]
    have h2 : (starRingEnd ℂ) (χ a x) * χ a x = 1 := by
      rw [Complex.conj_mul', hχn]
      norm_num
    exact mul_right_cancel₀ hz (h2.trans h1.symm)

  let S : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range ψ)
  have hSψ : ∀ a, ψ a ∈ S := fun a => Submodule.subset_span ⟨a, rfl⟩
  have hSmul : ∀ f g, f ∈ S → g ∈ S → f * g ∈ S := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨b, rfl⟩ := hg
        rw [hψmul]
        exact hSψ _
      | zero => rw [mul_zero]; exact S.zero_mem
      | add x y _ _ hx hy => rw [mul_add]; exact S.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm]; exact S.smul_mem c hx
    | zero => rw [zero_mul]; exact S.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact S.smul_mem c hx
  have hSstar : ∀ f, f ∈ S → star f ∈ S := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      rw [hψstar]
      exact hSψ _
    | zero => rw [star_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact S.smul_mem _ hx
  have hSalg : ∀ c : ℂ, algebraMap ℂ C(G ⧸ Γ, ℂ) c ∈ S := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← hψ0]
    exact S.smul_mem c (hSψ 0)
  let T : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := S
      mul_mem' := fun {f g} hf hg => hSmul f g hf hg
      one_mem' := hψ0 ▸ hSψ 0
      add_mem' := fun {f g} hf hg => S.add_mem hf hg
      zero_mem' := S.zero_mem
      algebraMap_mem' := hSalg
      star_mem' := fun {f} hf => hSstar f hf }
  have hTsep : T.SeparatesPoints := by
    intro q r hqr
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
    have hnot : -x + y ∉ Γ := fun h => hqr (QuotientAddGroup.eq.mpr h)
    obtain ⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by
      by_contra h
      push_neg at h
      exact hnot ((hsep _).1 h)
    refine ⟨ψ a, ⟨ψ a, hSψ a, rfl⟩, ?_⟩
    simp only [hψ]
    intro hxy
    have hz : χ a x ≠ 0 := by
      intro h
      have := hχn a x
      rw [h, norm_zero] at this
      exact zero_ne_one this
    apply ha
    have : χ a y = χ a x * χ a (-x + y) := by rw [← hχx, add_neg_cancel_left]
    rw [← hxy] at this
    exact (mul_right_eq_self₀.mp this.symm).resolve_right hz
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints T hTsep

  have hint : ∀ f : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) 𝓕 μ := by
    intro f
    refine Measure.integrableOn_of_bounded (M := ‖f‖ * C) h𝓕fin.ne
      (((map_continuous f).comp QuotientAddGroup.continuous_mk).mul hΦc).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)
  let L₀ : C(G ⧸ Γ, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ
      map_add' := fun f g => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
  let L : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ := L₀.mkContinuous (C * μ.real 𝓕) fun f => by
    have h := norm_setIntegral_le_of_norm_le_const (f := fun x => f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x) h𝓕fin
      (C := ‖f‖ * C) fun x _ => by
        rw [norm_mul]
        exact mul_le_mul (f.norm_coe_le_norm _) (hC x) (norm_nonneg _) (norm_nonneg f)
    calc ‖L₀ f‖ ≤ ‖f‖ * C * μ.real 𝓕 := h
      _ = C * μ.real 𝓕 * ‖f‖ := by ring
  have hL : ∀ f, L f = ∫ x in 𝓕, f (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ := fun _ => rfl
  have hTL : ((T.topologicalClosure : StarSubalgebra ℂ C(G ⧸ Γ, ℂ)) : Set C(G ⧸ Γ, ℂ)) ⊆ {f | L f = 0} := by
    rw [StarSubalgebra.topologicalClosure_coe]
    refine closure_minimal ?_ (isClosed_eq L.continuous continuous_const)
    intro f hf
    change f ∈ S at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      exact hcoef a
    | zero => exact map_zero L
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _), hx, hy, add_zero]
    | smul c x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [map_smul, hx, smul_zero]

  let Φq : C(G ⧸ Γ, ℂ) :=
    ⟨Quotient.lift (s := QuotientAddGroup.leftRel Γ) Φ (hinv hΦp), hΦc.quotient_lift _⟩
  have hzero : L (star Φq) = 0 := by
    apply hTL
    rw [hclos]
    trivial
  rw [hL] at hzero
  have hsq : ∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ = 0 := by
    have : ∫ x in 𝓕, (star Φq) (QuotientAddGroup.mk x : G ⧸ Γ) * Φ x ∂μ = ((∫ x in 𝓕, ‖Φ x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [ContinuousMap.star_apply]
      change (starRingEnd ℂ) (Φ x) * Φ x = _
      rw [Complex.conj_mul']
      push_cast
      rfl
    rw [this] at hzero
    exact_mod_cast hzero
  have hsqint : IntegrableOn (fun x => ‖Φ x‖ ^ 2) 𝓕 μ := by
    refine Measure.integrableOn_of_bounded (M := C ^ 2) h𝓕fin.ne
      (hΦc.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2
  have hae : ∀ᵐ x ∂μ.restrict 𝓕, Φ x = 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hsqint).mp hsq
    filter_upwards [this] with x hx
    simpa using hx

  set U : Set G := {x | Φ x ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hΦc continuous_const
  have hUF : μ (U ∩ 𝓕) = 0 := by
    rw [ae_iff, Measure.restrict_apply hUo.measurableSet] at hae
    exact hae
  have hUinv : ∀ γ : Γ, γ +ᵥ U = U := by
    intro γ
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Φ ((γ : G) + y) ≠ 0
      rw [hΦp _ γ.2]
      exact hy
    · intro hx
      refine ⟨-(γ : G) + x, ?_, ?_⟩
      · change Φ (-(γ : G) + x) ≠ 0
        rw [← hΦp _ γ.2, add_neg_cancel_left]
        exact hx
      · change (γ : G) + (-(γ : G) + x) = x
        exact add_neg_cancel_left _ _
  have hU0 : μ U = 0 := h𝓕.measure_zero_of_invariant U hUinv hUF
  have hUe : U = ∅ := hUo.measure_eq_zero_iff μ |>.mp hU0
  funext x
  by_contra hx
  have : x ∈ U := hx
  rw [hUe] at this
  exact this

end GlobalTheory.SeparatingCharacters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlueOfDenseOpenImmersion
section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

theorem app_injective_of_dense_range {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j]
    (hj : Dense (Set.range j)) (W : Z.Opens) : Function.Injective (j.app W).hom := by
  intro a b hab
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  have h0 : j ⁻¹ᵁ Z.basicOpen (a - b) = ⊥ := by
    rw [Scheme.preimage_basicOpen, map_sub, hab, sub_self, Scheme.basicOpen_zero]
  by_contra hne
  obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty _).mp hne
  obtain ⟨x, hx1, ⟨y, rfl⟩⟩ := hj.inter_open_nonempty _ (Z.basicOpen (a - b)).isOpen ⟨z, hz⟩
  have : y ∈ j ⁻¹ᵁ Z.basicOpen (a - b) := hx1
  rw [h0] at this
  exact this

theorem app_res_eq {T Z : Scheme.{0}} (j : T ⟶ Z) {V W : Z.Opens} (i : V ⟶ W)
    (i' : j ⁻¹ᵁ V ⟶ j ⁻¹ᵁ W) (a : Γ(Z, W)) :
    j.app V (Z.presheaf.map i.op a) = T.presheaf.map i'.op (j.app W a) := by
  obtain rfl : i' = (Opens.map j.base).map i := Subsingleton.elim _ _
  have := congrArg (fun f => f.hom a) (j.naturality i.op)
  simpa using this

theorem glue_of_dense_openImmersion : ∀ {T Z : Scheme.{0}} [IsReduced Z] (j : T ⟶ Z) [IsOpenImmersion j], Dense (Set.range j) →
    ∀ (U : Z.Opens) (s : Γ(T, j ⁻¹ᵁ U)), (∀ u ∈ U, ∃ (W : Z.Opens) (hWU : W ≤ U), u ∈ W ∧
      ∃ h : Γ(Z, W), j.app W h = T.presheaf.map (homOfLE (j.preimage_mono hWU)).op s) →
    ∃ h : Γ(Z, U), j.app U h = s := by
  intro T Z _ j _ hj U s hloc
  choose W hWU hmem h hh using hloc
  let Wf : U → Z.Opens := fun u => W u.1 u.2
  have hcover : U ≤ iSup Wf := fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hmem x hx⟩
  obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' Wf U (fun u => homOfLE (hWU u.1 u.2)) hcover
    (fun u => h u.1 u.2) (by
      intro u v
      apply app_injective_of_dense_range j hj
      change j.app _ (Z.presheaf.map _ (h u.1 u.2)) = j.app _ (Z.presheaf.map _ (h v.1 v.2))
      rw [app_res_eq j _ (homOfLE (j.preimage_mono inf_le_left)),
        app_res_eq j _ (homOfLE (j.preimage_mono inf_le_right)), hh, hh]
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  let g' : Γ(Z, U) := g
  have hg' : ∀ u : U, Z.presheaf.map (homOfLE (hWU u.1 u.2)).op g' = h u.1 u.2 := hg
  refine ⟨g', ?_⟩
  refine T.sheaf.eq_of_locally_eq' (fun u : U => j ⁻¹ᵁ Wf u) (j ⁻¹ᵁ U)
    (fun u => homOfLE (j.preimage_mono (hWU u.1 u.2))) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.2 ⟨⟨j x, hx⟩, hmem _ hx⟩
  · intro u
    have key : T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op (j.app U g') =
        T.presheaf.map (homOfLE (j.preimage_mono (hWU u.1 u.2))).op s := by
      rw [← app_res_eq j (homOfLE (hWU u.1 u.2)), hg' u, hh]
    exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeisenbergSmoothVectorDerivativeCalculus
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.DCalc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E} (hF : Differentiable ℝ F)
    (w y : V) : HasDerivAt (fun t : ℝ => F (w + t • y)) (fderiv ℝ F w y) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add w
  have hF' : HasFDerivAt F (fderiv ℝ F w) (w + (0 : ℝ) • y) := by
    simpa using (hF w).hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl

theorem hasDerivAt_lin (a : ℝ) : HasDerivAt (fun t : ℝ => (π * I * ((t * a : ℝ) : ℂ))) (π * I * a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * a : ℝ) : ℂ)) (a : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp
  exact h1.const_mul (π * I)

theorem hasDerivAt_phase (a : ℝ) {G : ℝ → B} {G' : B} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) (G' + (π * I * a : ℂ) • G 0) 0 := by
  have hc := (hasDerivAt_lin a).cexp
  have hp : HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) _ 0 := hc.smul hG
  convert hp using 1
  simp

variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}

theorem skew (h0 : ∀ x, om x x = 0) (x y : V) : om y x = -om x y := by
  have hxy := h0 (x + y)
  simp only [map_add (f := _), _root_.add_apply, h0] at hxy
  linarith

theorem heis_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w y : V) :
    ρ w (dH ρ y f) = fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f)) (ρ w (dH ρ y f)) 0 := by
    have hl := hasDerivAt_dH y hf
    exact ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f))
      (fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om w y) (hasDerivAt_line hd w y)
    convert (preTransparency := .reducible) hp using 1
    · funext t
      rw [h.2.1]
      simp
    · simp
  exact h1.unique h2

theorem sm_heis (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w : V) : Sm ρ (ρ w f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (ρ w f)) = fun u => cexp (π * I * (om u w : ℂ)) • ρ (u + w) f := by
    funext u
    exact h.2.1 u w f
  show ContDiff ℝ ∞ (fun u => ρ u (ρ w f))
  rw [e]
  apply ContDiff.smul
  · apply ContDiff.cexp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))
  · exact hf'.comp (contDiff_id.add contDiff_const)

theorem contDiff_fderiv {f : B} (hf : Sm ρ f) : ContDiff ℝ ∞ (fderiv ℝ fun u => ρ u f) := (contDiff_infty_iff_fderiv.1 (show ContDiff ℝ ∞ (fun u => ρ u f) from hf)).2

theorem sm_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (dH ρ v f)) =
      fun u => fderiv ℝ (fun u => ρ u f) u v + (π * I * (om u v : ℂ)) • ρ u f := by
    funext u
    exact heis_dH h hf u v
  show ContDiff ℝ ∞ (fun u => ρ u (dH ρ v f))
  rw [e]
  refine ((contDiff_fderiv hf).clm_apply contDiff_const).add ?_
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))).smul hf'

theorem dH_heis (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 := hasDerivAt_dH v (sm_heis h hf w)
  have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) (ρ w f))
      (fderiv ℝ (fun u => ρ u f) w v + (π * I * (om v w : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om v w) (hasDerivAt_line hd w v)
    convert (preTransparency := .reducible) hp using 1
    · funext t
      rw [h.2.1, add_comm (t • v) w]
      simp
    · simp
  rw [h1.unique h2, heis_dH h hf w v, skew h0 w v, add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

theorem dH_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) = fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v + (π * I * (om u v : ℂ)) • f := by
  have hd2 : Differentiable ℝ (fderiv ℝ fun u => ρ u f) :=
    (contDiff_fderiv hf).differentiable (by simp)
  have h1 := hasDerivAt_dH u (sm_dH h hf v)
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (fun u => ρ u f) (0 + t • u) v)
      (fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v) 0 := by
    have hl := (hasDerivAt_line hd2 0 u).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using hl
  have hB := (hasDerivAt_lin (om u v)).smul (hasDerivAt_dH u hf)
  have h2 := hA.add hB
  have e : (fun t : ℝ => ρ (t • u) (dH ρ v f)) = fun t : ℝ =>
      fderiv ℝ (fun u => ρ u f) (0 + t • u) v + (π * I * ((t * om u v : ℝ) : ℂ)) • ρ (t • u) f := by
    funext t
    rw [heis_dH h hf]
    simp
  rw [e] at h1
  rw [h1.unique h2]
  simp [h.1]

theorem dH_commutator (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have hs : IsSymmSndFDerivAt ℝ (fun u => ρ u f) 0 := hf'.contDiffAt.isSymmSndFDerivAt
    (by simpa using (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [dH_dH h hf u v, dH_dH h hf v u, hs v u, skew h0 u v, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

theorem dH_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  intro V _ _ B _ _ om ρ h0 h f hf
  exact ⟨fun v => sm_dH h hf v, fun w => sm_heis h hf w,
    fun w y => eq_sub_of_add_eq (heis_dH h hf w y).symm, fun v w => dH_heis h0 h hf v w,
    fun u v => dH_commutator h0 h hf u v⟩

end GlobalTheory.Mem.Lift.DCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
section
set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace GlobalTheory.UnifDens

theorem measurePreserving_comp_equiv {κ : Type} [Fintype κ] {n : ℕ} (e : κ ≃ Fin n) :
    MeasurePreserving (fun x : Fin n → ℂ => fun i : κ => x (e i)) volume volume := by
  have := MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : κ => ℂ) e.symm
  convert this using 1
  funext x i
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : κ => ℂ) e.symm x (e i)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

variable {ι : Type} [Fintype ι] {p q n : ℕ}

def flatL (h : Fintype.card (ι × Fin p × Fin q) = n) : ReciprocityTheory.L2DbarEstimates.V n ≃L[ℂ] (ι × Fin p × Fin q → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFinOfCardEq h)).toContinuousLinearEquiv

theorem flatL_mp (h : Fintype.card (ι × Fin p × Fin q) = n) :
    MeasurePreserving (flatL h) volume volume := by
  let E' : (Fin n → ℂ) ≃ᵐ ReciprocityTheory.L2DbarEstimates.V n :=
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : Fin n => ℂ).symm.toHomeomorph.toMeasurableEquiv
  have h1 : MeasurePreserving E' volume volume := GlobalTheory.measurePreserving_toLp_complex
  have h2 : MeasurePreserving E'.symm volume volume := h1.symm
  exact (measurePreserving_comp_equiv (Fintype.equivFinOfCardEq h)).comp h2

end GlobalTheory.UnifDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)
end

