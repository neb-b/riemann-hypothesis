module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroup
section
open MeasureTheory

namespace GlobalTheory

theorem unfold_tsum_along_subgroup : ∀ (G H : Type) [Group G] [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant] (ι : H →* G), Function.Injective ι → ∀ (Γ : Subgroup G) [Countable Γ] (𝓕 : Set H), IsFundamentalDomain (Γ.comap ι) 𝓕 ν → ∀ (f : G → ℂ) (φ : H → ℂ), (∀ γ : G, Measurable fun h => f (γ * ι h)) → Measurable φ → (∀ γ ∈ Γ.comap ι, ∀ h, φ (γ * h) = φ h) → (∑' q : Γ ⧸ ι.range.subgroupOf Γ, ∫⁻ h, ‖f ((q.out : Γ) * ι h) * φ h‖ₑ ∂ν) ≠ ⊤ → IntegrableOn (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) 𝓕 ν ∧ HasSum (fun q : Γ ⧸ ι.range.subgroupOf Γ => ∫ h, f ((q.out : Γ) * ι h) * φ h ∂ν) (∫ h in 𝓕, (∑' γ : Γ, f (γ * ι h)) * φ h ∂ν) := by
  intro G H _ _ _ _ ν _ ι hι Γ _ 𝓕 h𝓕 f φ hf hφ hφinv hT
  haveI : MeasurableConstSMul (Γ.comap ι) H := ⟨fun g => measurable_const_mul (g : H)⟩
  haveI : SMulInvariantMeasure (Γ.comap ι) H ν := ⟨fun g s _ => measure_preimage_mul ν (g : H) s⟩
  haveI : Countable (Γ.comap ι) := by
    refine Function.Injective.countable (f := fun δ : Γ.comap ι => (⟨ι δ, δ.2⟩ : Γ)) ?_
    intro a b hab
    exact Subtype.ext (hι (congrArg Subtype.val hab))
  let e : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι → Γ := fun p => (p.1.out : Γ) * ⟨ι p.2, p.2.2⟩
  have hmemK : ∀ δ : Γ.comap ι, (⟨ι δ, δ.2⟩ : Γ) ∈ ι.range.subgroupOf Γ := fun δ => by
    rw [Subgroup.mem_subgroupOf]; exact ⟨δ, rfl⟩
  have he_inj : Function.Injective e := by
    rintro ⟨q, δ⟩ ⟨q', δ'⟩ h
    have hq : ∀ q δ, (QuotientGroup.mk (e (q, δ)) : Γ ⧸ ι.range.subgroupOf Γ) = q := by
      intro q δ
      show (QuotientGroup.mk ((q.out : Γ) * ⟨ι δ, δ.2⟩) : Γ ⧸ ι.range.subgroupOf Γ) = q
      rw [QuotientGroup.mk_mul_of_mem _ (hmemK δ)]
      exact QuotientGroup.out_eq' q
    have hqq : q = q' := by rw [← hq q δ, ← hq q' δ', h]
    subst hqq
    have h2 := mul_left_cancel h
    have h3 : ι δ = ι δ' := congrArg Subtype.val h2
    rw [Prod.mk.injEq]
    exact ⟨rfl, Subtype.ext (hι h3)⟩
  have he_surj : Function.Surjective e := by
    intro γ
    set q : Γ ⧸ ι.range.subgroupOf Γ := QuotientGroup.mk γ with hqdef
    have hm : (q.out : Γ)⁻¹ * γ ∈ ι.range.subgroupOf Γ := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hm
    obtain ⟨y, hy⟩ := hm
    have hyΓ : ι y ∈ Γ := by rw [hy]; exact ((q.out : Γ)⁻¹ * γ).2
    refine ⟨(q, ⟨y, hyΓ⟩), ?_⟩
    apply Subtype.ext
    show ((q.out : Γ) : G) * ι y = γ
    rw [hy]
    simp
  let eq := Equiv.ofBijective e ⟨he_inj, he_surj⟩
  let F : Γ → H → ℂ := fun γ h => f ((γ : G) * ι h) * φ h
  let g : Γ ⧸ ι.range.subgroupOf Γ → H → ℂ := fun q h => f (((q.out : Γ) : G) * ι h) * φ h
  have hkey : ∀ q (δ : Γ.comap ι) h, F (e (q, δ)) h = g q (δ • h) := by
    intro q δ h
    show f ((((q.out : Γ) : G) * ι δ) * ι h) * φ h = f (((q.out : Γ) : G) * ι ((δ : H) * h)) * φ ((δ : H) * h)
    rw [map_mul, mul_assoc, hφinv δ δ.2 h]
  have hFm : ∀ γ, Measurable (F γ) := fun γ => (hf γ).mul hφ
  have hgm : ∀ q, Measurable (g q) := fun q => (hf _).mul hφ
  have hA : ∀ q, ∫⁻ h, ‖g q h‖ₑ ∂ν = ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν := by
    intro q
    rw [h𝓕.lintegral_eq_tsum'' (fun h => ‖g q h‖ₑ)]
    simp_rw [hkey]
  have hsumF : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν = ∑' q, ∫⁻ h, ‖g q h‖ₑ ∂ν := by
    rw [← eq.tsum_eq]
    calc ∑' p, ∫⁻ h in 𝓕, ‖F (eq p) h‖ₑ ∂ν
        = ∑' q, ∑' δ : Γ.comap ι, ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν :=
          ENNReal.tsum_prod (f := fun q δ => ∫⁻ h in 𝓕, ‖F (e (q, δ)) h‖ₑ ∂ν)
      _ = _ := by simp_rw [hA]
  have hT' : ∑' γ : Γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν ≠ ⊤ := by rw [hsumF]; exact hT
  have hfun : (fun h => (∑' γ : Γ, f (γ * ι h)) * φ h) = fun h => ∑' γ : Γ, F γ h :=
    funext fun h => tsum_mul_right.symm
  have hint : IntegrableOn (fun h => ∑' γ : Γ, F γ h) 𝓕 ν := by
    refine ⟨(AEMeasurable.tsum fun γ => (hFm γ).aemeasurable).aestronglyMeasurable, ?_⟩
    show ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν < ⊤
    calc ∫⁻ h in 𝓕, ‖∑' γ : Γ, F γ h‖ₑ ∂ν ≤ ∫⁻ h in 𝓕, ∑' γ, ‖F γ h‖ₑ ∂ν :=
          lintegral_mono fun h => enorm_tsum_le_tsum_enorm
      _ = ∑' γ, ∫⁻ h in 𝓕, ‖F γ h‖ₑ ∂ν := lintegral_tsum fun γ => (hFm γ).aemeasurable.enorm
      _ < ⊤ := lt_top_iff_ne_top.2 hT'
  have hsumm : Summable fun γ : Γ => ∫ h in 𝓕, F γ h ∂ν := by
    refine Summable.of_norm ?_
    have h1 : ∑' γ : Γ, ‖∫ h in 𝓕, F γ h ∂ν‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top hT' (ENNReal.tsum_le_tsum fun γ => enorm_integral_le_lintegral_enorm _)
    simp only [enorm_eq_nnnorm] at h1
    exact NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 h1)
  have hI : ∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν = ∑' γ : Γ, ∫ h in 𝓕, F γ h ∂ν :=
    integral_tsum (fun γ => (hFm γ).aestronglyMeasurable) hT'
  have hgint : ∀ q, Integrable (g q) ν := fun q =>
    ⟨(hgm q).aestronglyMeasurable,
      lt_of_le_of_lt (ENNReal.le_tsum (f := fun q => ∫⁻ h, ‖g q h‖ₑ ∂ν) q) (lt_top_iff_ne_top.2 hT)⟩
  have hs : Summable (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν) :=
    (eq.summable_iff).2 hsumm
  have hinner : ∀ q, HasSum (fun δ : Γ.comap ι => ∫ h in 𝓕, F (e (q, δ)) h ∂ν) (∫ h, g q h ∂ν) := by
    intro q
    have h1 := (hs.prod_factor q).hasSum
    rw [h𝓕.integral_eq_tsum'' (g q) (hgint q)]
    simp_rw [← hkey]
    exact h1
  have htot : HasSum (fun p : (Γ ⧸ ι.range.subgroupOf Γ) × Γ.comap ι => ∫ h in 𝓕, F (eq p) h ∂ν)
      (∫ h in 𝓕, (∑' γ : Γ, F γ h) ∂ν) := by
    rw [hI]; exact (eq.hasSum_iff).2 hsumm.hasSum
  rw [hfun]
  exact ⟨hint, htot.prod_fiberwise hinner⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitriangularMapInduction
section
open MeasureTheory Matrix
open scoped Pointwise

namespace GlobalTheory.UnipChange

section Shear

variable {k : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k]
  {ι : Type} [Fintype ι]

end Shear

section Linear

variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_mul_left_eq_smul' (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) ν = distribHaarChar F (Units.mk0 a ha)⁻¹ • ν := by
  have hf : (fun x : F => a * x) = fun x => Units.mk0 a ha • x := by
    funext x; simp [Units.smul_def]
  ext s hs
  rw [Measure.map_apply (by rw [hf]; exact (continuous_const_smul _).measurable) hs, hf,
    Set.preimage_smul, ← distribHaarChar_mul ν]
  rw [Measure.coe_nnreal_smul_apply]

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem map_diagonal_mulVec_pi (D : κ → F) (hD : ∀ i, D i ≠ 0) :
    Measure.map (diagonal D).mulVec (Measure.pi fun _ : κ => ν)
      = (∏ i, distribHaarChar F (Units.mk0 (D i) (hD i))⁻¹) • Measure.pi fun _ : κ => ν := by
  have hfun : (diagonal D).mulVec = fun x i => (fun y => D i * y) (x i) := by
    funext x i; simp [mulVec_diagonal]
  haveI : ∀ i, SigmaFinite (Measure.map (fun y => D i * y) ν) := fun i => by
    rw [map_mul_left_eq_smul' ν (D i) (hD i)]; infer_instance
  rw [hfun, Measure.pi_map_pi (f := fun i y => D i * y)
    (fun i => (continuous_const.mul continuous_id).aemeasurable)]
  simp_rw [map_mul_left_eq_smul' ν _ (hD _)]
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi, ENNReal.ofNNReal_finsetProd,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => Measure.coe_nnreal_smul_apply _ _ _

open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
private theorem measurePreserving_transvection_mulVec (t : TransvectionStruct κ F) :
    MeasurePreserving t.toMatrix.mulVec (Measure.pi fun _ : κ => ν)
      (Measure.pi fun _ : κ => ν) := by
  let p : κ → Prop := fun i => i ≠ t.i
  let α : Type := { x // p x }
  let β : Type := { x // ¬p x }
  let g : (α → F) → (β → F) → β → F := fun a b => (fun _ => t.c * a ⟨t.j, t.hij.symm⟩) + b
  let G : (α → F) × (β → F) → (α → F) × (β → F) := fun q => (id q.1, g q.1 q.2)
  let e : (κ → F) ≃ᵐ (α → F) × (β → F) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : κ => F) p
  have hmv : t.toMatrix.mulVec = e.symm ∘ G ∘ e := by
    cases t with | mk i j hij c =>
    ext f k
    by_cases h : i = k
    · subst h
      simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, Matrix.single, ite_and, Matrix.one_apply, ite_mul]
      ring
    · simp [e, G, g, p, TransvectionStruct.toMatrix, transvection, mulVec, dotProduct,
        add_mul, Finset.sum_add_distrib, MeasurableEquiv.piEquivPiSubtypeProd,
        Equiv.piEquivPiSubtypeProd, h, Matrix.single, ite_and, Ne.symm h, Matrix.one_apply,
        ite_mul]
  rw [hmv]
  have hA : MeasurePreserving e (Measure.pi fun _ : κ => ν)
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ : κ => ν) p
  have hB : MeasurePreserving G ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν))
      ((Measure.pi fun _ : α => ν).prod (Measure.pi fun _ : β => ν)) := by
    have hg : Measurable (Function.uncurry g) := by
      refine Measurable.add ?_ measurable_snd
      exact Measurable.of_eval fun _ =>
        ((measurable_pi_apply _).comp measurable_fst).const_mul _
    exact (MeasurePreserving.id _).skew_product hg
      (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  exact ((hA.symm e).comp hB).comp hA


open MeasureTheory Matrix in
open scoped Pointwise in
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
  [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F] (ν : Measure F) [ν.IsAddHaarMeasure]
  {κ : Type} [Fintype κ] [DecidableEq κ] in
theorem _root_.GlobalTheory.UnipChange.smul_map_mulVec_pi (M : Matrix κ κ F) (u : Fˣ)
    (hu : (u : F) = M.det) :
    (distribHaarChar F u : ENNReal) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = Measure.pi fun _ : κ => ν := by
  have hmeas : ∀ N : Matrix κ κ F, Measurable N.mulVec := fun N =>
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have key : ∀ u : Fˣ, (u : F) = M.det → Measure.map M.mulVec (Measure.pi fun _ : κ => ν)
      = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν := by
    refine diagonal_transvection_induction_of_det_ne_zero (fun N : Matrix κ κ F => ∀ u : Fˣ,
      (u : F) = N.det → Measure.map N.mulVec (Measure.pi fun _ : κ => ν)
        = distribHaarChar F u⁻¹ • Measure.pi fun _ : κ => ν) M
      (hu ▸ u.ne_zero) ?_ ?_ ?_
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := fun i => by
        rw [det_diagonal] at hD
        exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
      rw [map_diagonal_mulVec_pi ν D hD']
      have hu' : u = ∏ i, Units.mk0 (D i) (hD' i) := by
        ext
        rw [hu, det_diagonal, Units.coe_prod]
        rfl
      rw [hu', ← Finset.prod_inv_distrib, map_prod]
    · intro t u hu
      have hu' : u = 1 := by
        ext
        rw [hu, TransvectionStruct.det, Units.val_one]
      rw [hu', inv_one, map_one, one_smul]
      exact (measurePreserving_transvection_mulVec ν t).map_eq
    · intro A B hA hB hPA hPB u hu
      have hcomp : (A * B).mulVec = A.mulVec ∘ B.mulVec :=
        funext fun x => (mulVec_mulVec x A B).symm
      have hu' : u = Units.mk0 _ hA * Units.mk0 _ hB := by
        ext
        simp [hu, det_mul]
      rw [hcomp, ← Measure.map_map (hmeas A) (hmeas B), hPB (Units.mk0 _ hB) rfl,
        Measure.map_smul _ (hmeas A).aemeasurable, hPA (Units.mk0 _ hA) rfl, smul_smul, hu', _root_.mul_inv_rev, map_mul,
        mul_comm]
  rw [key u hu]
  ext s hs
  rw [Measure.smul_apply, Measure.coe_nnreal_smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one, one_mul]

end Linear

section Algebra

variable {k : Type} [Field k] {r : ℕ} {b : Fin r → ℕ}



end Algebra

section Top

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k]
  {r : ℕ} {b : Fin r → ℕ}


end Top

end GlobalTheory.UnipChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylNumberOperatorCommutation
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem weyl_number_operator_commutation
    (V A κ : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Ring A] [Algebra ℂ A]
    [Fintype κ] (J : V ≃ₗᵢ[ℝ] V) (e : OrthonormalBasis κ ℝ V) (D a c : V → A) (N : A)
    (hJJ : ∀ x, J (J x) = -x) (hadd : ∀ u v, D (u + v) = D u + D v)
    (hsmul : ∀ (r : ℝ) v, D (r • v) = (r : ℂ) • D v)
    (hcomm : ∀ u v, D u * D v - D v * D u =
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1)
    (hc : ∀ z, c z = D z - Complex.I • D (J z)) (ha : ∀ z, a z = -(D z + Complex.I • D (J z)))
    (hN : N = ∑ j, c (e j) * a (e j)) :
    (∀ z, a z * c z - c z * a z = ((4 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) • 1) ∧
    (∀ z, N * c z = c z * (N + ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    (∀ z, N * a z = a z * (N - ((8 * Real.pi : ℝ) : ℂ) • 1)) ∧
    ∀ z, D z ∈ Submodule.span ℂ (Set.range (fun j => a (e j)) ∪ Set.range fun j => c (e j)) := by
  have I3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
  have hJl : ∀ u v, inner ℝ (J u) v = -inner ℝ u (J v) := by
    intro u v
    have h := J.inner_map_map (J u) v
    rw [hJJ, inner_neg_left] at h
    linarith
  have hJself : ∀ z, inner ℝ z (J z) = 0 := by
    intro z
    have h := hJl z z
    have h' := real_inner_comm z (J z)
    linarith
  have hDneg : ∀ w, D (-w) = -D w := by
    intro w
    have h := hsmul (-1) w
    simpa using h
  have key : ∀ F : V → A, (∀ u v, F (u + v) = F u + F v) →
      (∀ (r : ℝ) v, F (r • v) = (r : ℂ) • F v) →
      ∀ w, F w = ∑ j, ((inner ℝ (e j) w : ℝ) : ℂ) • F (e j) := by
    intro F hFa hFs w
    have h := map_sum (AddMonoidHom.mk' F hFa) (fun j => inner ℝ (e j) w • e j) Finset.univ
    simp only [AddMonoidHom.mk'_apply, e.sum_repr'] at h
    rw [h]
    exact Finset.sum_congr rfl fun j _ => hFs _ _
  have hca : ∀ u v, c (u + v) = c u + c v := by
    intro u v; rw [hc, hc, hc, map_add (f := _), hadd, hadd, smul_add]; abel
  have hcs : ∀ (r : ℝ) v, c (r • v) = (r : ℂ) • c v := by
    intro r v; rw [hc, hc, map_smul, hsmul, hsmul, smul_sub, smul_comm Complex.I (r : ℂ)]
  have haa' : ∀ u v, a (u + v) = a u + a v := by
    intro u v; rw [ha, ha, ha, map_add (f := _), hadd, hadd, smul_add]; abel
  have has : ∀ (r : ℝ) v, a (r • v) = (r : ℂ) • a v := by
    intro r v
    rw [ha, ha, map_smul, hsmul, hsmul, smul_comm Complex.I (r : ℂ), ← smul_add, smul_neg]
  have hcJ : ∀ w, c (J w) = Complex.I • c w := by
    intro w
    rw [hc, hc, hJJ, hDneg]
    simp only [smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul]
    abel
  have haJ : ∀ w, a (J w) = -(Complex.I • a w) := by
    intro w
    rw [ha, ha, hJJ, hDneg]
    simp only [smul_add, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
    abel
  have hsw : ∀ u v, D u * D v = D v * D u +
      (2 * Real.pi * Complex.I * (inner ℝ u (J v) : ℝ) : ℂ) • 1 := by
    intro u v; rw [← hcomm u v]; abel
  have hac : ∀ z w, a z * c w - c w * a z =
      (4 * (Real.pi : ℂ) * ((inner ℝ z w : ℝ) : ℂ)
        - 4 * Real.pi * Complex.I * ((inner ℝ z (J w) : ℝ) : ℂ)) • (1 : A) := by
    intro z w
    rw [ha, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcc : ∀ z w, c z * c w = c w * c z := by
    intro z w
    rw [← sub_eq_zero, hc, hc]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have haa : ∀ z w, a z * a w = a w * a z := by
    intro z w
    rw [← sub_eq_zero, ha, ha]
    simp only [mul_sub, sub_mul, mul_add, add_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    rw [hsw z w, hsw z (J w), hsw (J z) w, hsw (J z) (J w)]
    simp only [hJJ, map_neg, inner_neg_right, inner_neg_left, hJl, neg_neg]
    match_scalars <;> (ring_nf; try simp only [Complex.I_sq, I3]; try ring_nf)
  have hcsum := key c hca hcs
  have hasum := key a haa' has
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    rw [hac, hJself, real_inner_self_eq_norm_sq]
    congr 1
    push_cast
    ring
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * c z - c z * (c (e j) * a (e j)) =
        (4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • c (e j))
          - (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • c (e j)) := by
      intro j
      rw [mul_assoc, ← mul_assoc (c z), hcc z (e j), mul_assoc, ← mul_sub, hac (e j) z,
        mul_smul_comm, mul_one]
      module
    have hsum : N * c z - c z * N = ((8 * Real.pi : ℝ) : ℂ) • c z := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_sub_distrib, ← Finset.smul_sum]
      rw [← hcsum z, ← hcsum (J z), hcJ, smul_smul, ← sub_smul]
      congr 1
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_add, mul_smul_comm, mul_one, ← sub_eq_iff_eq_add', hsum]
  · intro z
    have hterm : ∀ j, c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
        -((4 * (Real.pi : ℂ)) • (((inner ℝ (e j) z : ℝ) : ℂ) • a (e j))
          + (4 * Real.pi * Complex.I) • (((inner ℝ (e j) (J z) : ℝ) : ℂ) • a (e j))) := by
      intro j
      have h1 := hac z (e j)
      have h2 : inner ℝ z (J (e j)) = -inner ℝ (e j) (J z) := by
        rw [real_inner_comm (J (e j)) z, hJl]
      rw [real_inner_comm (e j) z, h2] at h1
      have h3 : c (e j) * a (e j) * a z - a z * (c (e j) * a (e j)) =
          -((a z * c (e j) - c (e j) * a z) * a (e j)) := by
        rw [mul_assoc, haa (e j) z]
        noncomm_ring
      rw [h3, h1, smul_mul_assoc, one_mul]
      simp only [Complex.ofReal_neg]
      module
    have hsum : N * a z - a z * N = -(((8 * Real.pi : ℝ) : ℂ) • a z) := by
      rw [hN, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      simp only [hterm, Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
      rw [← hasum z, ← hasum (J z), haJ, smul_neg, smul_smul, ← sub_eq_add_neg, ← sub_smul]
      congr 2
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    rw [mul_sub, mul_smul_comm, mul_one, sub_eq_iff_eq_add.mp hsum]
    abel
  · intro z
    have hDz : D z = (1 / 2 : ℂ) • (c z - a z) := by
      rw [hc, ha]
      module
    rw [hDz, hcsum z, hasum z]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
      refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    · exact Or.inr ⟨j, rfl⟩
    · exact Or.inl ⟨j, rfl⟩

end GlobalTheory
end

