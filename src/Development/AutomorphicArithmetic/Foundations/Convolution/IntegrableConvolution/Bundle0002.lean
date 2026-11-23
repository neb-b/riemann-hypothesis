module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ChangeVar
section
open MeasureTheory

private theorem measurePreserving_chainCoords {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] (m : ℕ) :
    ∀ δ : Fin m → G,
    MeasurePreserving (fun x : Fin (m + 1) → G => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ))
      (Measure.pi fun _ => μ) (μ.prod (Measure.pi fun _ => μ)) := by
  induction m with
  | zero =>
    intro δ
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin 1 => μ) 0
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    exact i.elim0
  | succ m ih =>
    intro δ
    have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 2) => μ) 0
    have h2 := (MeasurePreserving.id μ).prod (ih (Fin.tail δ))
    have h3 : MeasurePreserving
        (fun p : G × (G × (Fin m → G)) => (id p.1, (p.1⁻¹ * δ 0 * p.2.1, p.2.2)))
        (μ.prod (μ.prod (Measure.pi fun _ => μ))) (μ.prod (μ.prod (Measure.pi fun _ => μ))) := by
      refine MeasurePreserving.skew_product (g := fun (a : G) (q : G × (Fin m → G)) => (a⁻¹ * δ 0 * q.1, q.2))
        (MeasurePreserving.id μ) ?_ (Filter.Eventually.of_forall fun a => ?_)
      · unfold Function.uncurry
        fun_prop
      · exact ((measurePreserving_mul_left μ (a⁻¹ * δ 0)).prod (MeasurePreserving.id _)).map_eq
    have h4 := (MeasurePreserving.id μ).prod
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0).symm
    have h := h4.comp (h3.comp (h2.comp h1))
    convert h using 1
    funext x
    refine Prod.ext rfl ?_
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]

private theorem tele {G : Type} [Group G] (m : ℕ) : ∀ (δ : Fin m → G) (x : Fin (m + 1) → G),
    (List.ofFn fun i : Fin m => (x i.castSucc)⁻¹ * δ i * x i.succ).prod =
      (x 0)⁻¹ * (List.ofFn δ).prod * x (Fin.last m) := by
  induction m with
  | zero => intro δ x; simp
  | succ m ih =>
    intro δ x
    have h := ih (fun i => δ i.succ) (fun i => x i.succ)
    simp only [List.ofFn_succ, List.prod_cons, ← Fin.succ_castSucc]
    rw [h]
    simp [mul_assoc]

theorem UpperTheory.ConvolutionTheory.L1.changeVar :
    UpperTheory.ConvolutionTheory.L1.ChangeVar := by
  intro G _ _ _ _ _ _ _ _ μ _ m δ
  refine ⟨measurePreserving_chainCoords μ m (fun i => δ i.castSucc), fun x => ?_⟩
  funext i
  unfold UpperTheory.ConvolutionTheory.L1.fib
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, tele m (fun i => δ i.castSucc) x, List.ofFn_succ' δ]
    simp [mul_assoc]
  · rw [Fin.snoc_castSucc, Fin.coeSucc_eq_succ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProper
section
open Topology

private theorem UpperTheory.ConvolutionTheory.L1.compact_lift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] {f : X → Y} (hf : IsOpenMap f) (hs : Function.Surjective f) {D : Set Y}
    (hD : IsCompact D) : ∃ K : Set X, IsCompact K ∧ D ⊆ f '' K := by
  have h : ∀ z : Y, ∃ K : Set X, IsCompact K ∧ f '' K ∈ 𝓝 z := by
    intro z
    obtain ⟨g, rfl⟩ := hs z
    obtain ⟨K, hK, hg⟩ := exists_compact_mem_nhds g
    exact ⟨K, hK, hf.image_mem_nhds hg⟩
  choose K hK hK' using h
  obtain ⟨t, -, ht⟩ := hD.elim_nhds_subcover (fun z => f '' K z) (fun z _ => hK' z)
  refine ⟨⋃ z ∈ t, K z, t.isCompact_biUnion fun z _ => hK z, ?_⟩
  intro y hy
  obtain ⟨z, hz, g, hg, rfl⟩ := Set.mem_iUnion₂.1 (ht hy)
  exact ⟨g, Set.mem_iUnion₂.2 ⟨z, hz, hg⟩, rfl⟩

theorem UpperTheory.ConvolutionTheory.L1.closedProper :
    UpperTheory.ConvolutionTheory.L1.ClosedProper := by
  intro G _ _ _ _ _ _ γ hO D hD
  set O : Set G := {y | ∃ x, y = x⁻¹ * γ * x} with hOdef
  let : MulAction G O :=
    { smul := fun g y => ⟨g * y.1 * g⁻¹, by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨x * g⁻¹, by rw [hx]; group⟩⟩
      one_smul := fun y => Subtype.ext (by change 1 * y.1 * 1⁻¹ = y.1; group)
      mul_smul := fun a b y => Subtype.ext (by
        change a * b * y.1 * (a * b)⁻¹ = a * (b * y.1 * b⁻¹) * a⁻¹; group) }
  have hsm : ∀ (g : G) (y : O), ((g • y : O) : G) = g * y.1 * g⁻¹ := fun _ _ => rfl
  have : ContinuousSMul G O := ⟨by
    refine continuous_induced_rng.2 ?_
    change Continuous fun p : G × O => p.1 * p.2.1 * p.1⁻¹
    fun_prop⟩
  have : MulAction.IsPretransitive G O := ⟨by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact ⟨b⁻¹ * a, Subtype.ext (by rw [hsm]; group)⟩⟩
  have : LocallyCompactSpace O := hO.locallyCompactSpace
  let γ₀ : O := ⟨γ, 1, by group⟩
  have hopen : IsOpenMap (fun g : G => g • γ₀) := isOpenMap_smul_of_sigmaCompact γ₀
  have hsurj : Function.Surjective (fun g : G => g • γ₀) := fun y => MulAction.exists_smul_eq G γ₀ y
  have hD' : IsCompact (Subtype.val ⁻¹' D : Set O) := hO.isClosedEmbedding_subtypeVal.isCompact_preimage hD
  obtain ⟨K, hK, hDK⟩ := UpperTheory.ConvolutionTheory.L1.compact_lift hopen hsurj hD'
  refine ⟨(·⁻¹) '' K, hK.image continuous_inv, fun x hx => ?_⟩
  obtain ⟨g, hg, hgx⟩ := hDK (a := ⟨x⁻¹ * γ * x, x, rfl⟩) hx
  have h1 : g * γ * g⁻¹ = x⁻¹ * γ * x := congrArg Subtype.val hgx
  refine ⟨x * g, ?_, g⁻¹, ⟨g, hg, rfl⟩, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro h rfl
  calc h * (x * g) = x * (x⁻¹ * h * x) * g := by group
    _ = x * (g * h * g⁻¹) * g := by rw [h1]
    _ = x * g * h := by group
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CutIrr
section
open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

private lemma UpperTheory.ConvolutionTheory.L1.cutIrr_prod {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (E : H →L[ℂ] H) {m : ℕ} (ι : Fin (m + 1) → G →* Γ)
    (hE : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)) (P : Submodule ℂ H)
    (hP : ∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) (l : List Γ) (hl : ∀ x ∈ l, ∃ i g, x = ι i g) :
    (∀ v, E (π l.prod v) = π l.prod (E v)) ∧ ∀ v ∈ P, π l.prod v ∈ P := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨i, g, rfl⟩ := hl a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun x hx => hl x (by simp [hx]))
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [List.prod_cons, UnitaryRep.map_mul_apply, UnitaryRep.map_mul_apply, hE, h1]
    · rw [List.prod_cons, UnitaryRep.map_mul_apply]
      exact hP _ _ _ (h2 v hv)

theorem UpperTheory.ConvolutionTheory.L1.cutIrr :
    UpperTheory.ConvolutionTheory.L1.CutIrr := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h
  have hfix : ∀ v, v ∈ eigIn V E 1 ↔ v ∈ V ∧ E v = v := by
    intro v
    simp [eigIn, Module.End.mem_eigenspace_iff]
  refine ⟨?_, ?_, ?_⟩
  · have hset : (eigIn V E 1 : Set H) = (V : Set H) ∩ {v | E v = v} := by
      ext v
      exact hfix v
    rw [hset]
    exact h.summand.closed.inter (isClosed_eq E.continuous continuous_id)
  · intro i g v hv
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    exact (hfix _).2 ⟨h.summand.inv _ _ hV, by rw [h.E_ι, hE]⟩
  · intro P hPle hPc hPinv
    by_cases hbot : P = ⊥
    · exact Or.inl hbot
    right
    obtain ⟨w, hwP, hw0⟩ := P.ne_bot_iff.1 hbot
    obtain ⟨hwV, hEw⟩ := (hfix w).1 (hPle hwP)
    let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun γ => π γ w)
    have hSinv : π.IsInvariant S := by
      intro g v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * γ, by simp [UnitaryRep.map_mul_apply]⟩
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact S.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact S.smul_mem a hx
    have hSV : S ≤ V := Submodule.span_le.2 (by
      rintro _ ⟨γ, rfl⟩
      exact h.summand.inv _ _ hwV)
    have hQle : S.topologicalClosure ≤ V :=
      Submodule.topologicalClosure_minimal _ hSV h.summand.closed
    have hQ : S.topologicalClosure = V := by
      rcases h.summand.irred _ hQle S.isClosed_topologicalClosure hSinv.topologicalClosure with h0 | h1
      · exfalso
        have hmem : w ∈ S.topologicalClosure :=
          S.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
        rw [h0] at hmem
        exact hw0 (by simpa using hmem)
      · exact h1
    have hES : ∀ v ∈ S, E v ∈ P := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨γ, rfl⟩ := hx
        obtain ⟨g, γ', c, hγ, hc⟩ := h.rest γ
        have hl : ∀ x ∈ List.ofFn (fun i => ι i (g i)), ∃ i g, x = ι i g := by
          intro x hx
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
          exact ⟨i, g i, rfl⟩
        obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr_prod π E ι h.E_ι P hPinv _ hl
        have hc' := hc w hwV
        rw [hEw] at hc'
        show E (π γ w) ∈ P
        rw [hγ, UnitaryRep.map_mul_apply, h1, hc']
        exact h2 _ (P.smul_mem c hwP)
      | zero => simp
      | add x y _ _ hx hy =>
        rw [map_add (f := _)]
        exact P.add_mem hx hy
      | smul a x _ hx =>
        rw [map_smul]
        exact P.smul_mem a hx
    have hEQ : ∀ v ∈ V, E v ∈ P := by
      intro v hv
      rw [← hQ] at hv
      have hcl : v ∈ closure (S : Set H) := hv
      have hm := map_mem_closure E.continuous hcl (t := (P : Set H)) (fun x hx => hES x hx)
      rwa [hPc.closure_eq] at hm
    refine le_antisymm hPle fun v hv => ?_
    obtain ⟨hV, hE⟩ := (hfix v).1 hv
    rw [← hE]
    exact hEQ v hV
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.CvBasic
section
open MeasureTheory

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
private theorem cvb_int {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) (x : G) :
    Integrable (fun y => a y * b (y⁻¹ * x)) μ :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (ha'.mul_right)

private theorem cvb_cont {a b : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b) :
    Continuous (cv μ a b) := by
  have h : cv μ a b = fun x => ∫ y in tsupport a, a y * b (y⁻¹ * x) ∂μ := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  rw [h]
  refine continuous_parametric_integral_of_continuous (f := fun x y => a y * b (y⁻¹ * x)) ?_ ha'
  unfold Function.uncurry
  fun_prop

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_supp {a b : G → ℂ} (x : G) (hx : cv μ a b x ≠ 0) :
    ∃ y z, a y ≠ 0 ∧ b z ≠ 0 ∧ x = y * z := by
  by_contra h
  apply hx
  have : (fun y => a y * b (y⁻¹ * x)) = fun _ => 0 := by
    funext y
    by_contra h'
    exact h ⟨y, y⁻¹ * x, left_ne_zero_of_mul h', right_ne_zero_of_mul h', by simp⟩
  simp only [cv, this, integral_zero]

open scoped Pointwise in
omit [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G] [μ.IsHaarMeasure] in
private theorem cvb_cs {a b : G → ℂ} (ha' : HasCompactSupport a) (hb' : HasCompactSupport b) :
    HasCompactSupport (cv μ a b) := by
  refine HasCompactSupport.intro (K := tsupport a * tsupport b) (IsCompact.mul ha' hb') fun x hx => ?_
  by_contra h
  obtain ⟨y, z, hy, hz, rfl⟩ := cvb_supp μ x h
  exact hx (Set.mul_mem_mul (subset_tsupport _ hy) (subset_tsupport _ hz))

open scoped Pointwise in
private theorem cvb_assoc {a b c : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (hb : Continuous b)
    (hb' : HasCompactSupport b) (hc : Continuous c) : cv μ (cv μ a b) c = cv μ a (cv μ b c) := by
  funext x
  have hint : Integrable (Function.uncurry fun y z : G => a z * b (z⁻¹ * y) * c (y⁻¹ * x)) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · unfold Function.uncurry
      fun_prop
    · refine HasCompactSupport.intro (K := (tsupport a * tsupport b) ×ˢ tsupport a)
        ((IsCompact.mul ha' hb').prod ha') fun p hp => ?_
      by_contra h
      have h1 := left_ne_zero_of_mul h
      have h2 : a p.2 ≠ 0 := left_ne_zero_of_mul h1
      have h3 : b (p.2⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul h1
      refine hp ⟨?_, subset_tsupport _ h2⟩
      have := Set.mul_mem_mul (subset_tsupport _ h2) (subset_tsupport _ h3)
      simpa using this
  calc cv μ (cv μ a b) c x = ∫ y, ∫ z, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := by
        simp only [cv, integral_mul_const]
    _ = ∫ z, ∫ y, a z * b (z⁻¹ * y) * c (y⁻¹ * x) ∂μ ∂μ := integral_integral_swap hint
    _ = cv μ a (cv μ b c) x := by
        simp only [cv]
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only
        rw [← integral_const_mul, ← integral_mul_left_eq_self _ z]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp [mul_assoc]

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.cvBasic :
    UpperTheory.ConvolutionTheory.L1.CvBasic := by
  intro G _ _ _ _ _ _ _ _ μ _ a b c ha ha' hb hb' hc hc'
  refine ⟨cvb_cont μ ha ha' hb, cvb_cs μ ha' hb', cvb_supp μ, cvb_assoc μ ha ha' hb hb' hc, ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · funext x
    simp only [cv, Pi.add_apply, add_mul]
    exact integral_add (cvb_int μ ha ha' hc x) (cvb_int μ hb hb' hc x)
  · funext x
    simp only [cv, Pi.add_apply, mul_add]
    exact integral_add (cvb_int μ ha ha' hb x) (cvb_int μ ha ha' hc x)
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  · funext x
    simp only [cv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ t, integral_const_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GalSplit
section
open scoped TensorProduct
open PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

private theorem orderOf_gen (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) : orderOf σ = m + 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank, hm]

private theorem det_ne (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (b : Module.Basis (Fin (m + 1)) F E) :
    (Matrix.of fun (i j : Fin (m + 1)) => (σ ^ (i : ℕ)) (b j)).det ≠ 0 :=
  _root_.UpperTheory.Reformulated.B.DeterminantNonzero.det_ne σ hσ hm b

variable {A : Type} [CommRing A] [Algebra F A]

private noncomputable def phi (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) : E ⊗[F] A →ₐ[F] (Fin (m + 1) → A) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom F _ fun i : Fin (m + 1) => p.comp ((σ ^ (i : ℕ) : E ≃ₐ[F] E) : E →ₐ[F] E))
    (Pi.algHom F _ fun _ => AlgHom.id F A)

private theorem phi_tmul (σ : E ≃ₐ[F] E) (p : E →ₐ[F] A) (m : ℕ) (x : E) (a : A) (i : Fin (m + 1)) :
    phi σ p m (x ⊗ₜ a) i = p ((σ ^ (i : ℕ)) x) * a := by
  simp [phi]

private theorem phi_bij (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) : Function.Bijective (phi σ p m) := by
  let b : Module.Basis (Fin (m + 1)) F E := Module.finBasisOfFinrankEq F E hm
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) E := Matrix.of fun i j => (σ ^ (i : ℕ)) (b j)
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.2 (det_ne σ hσ hm b)
  let N := M⁻¹
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv _ hunit
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul _ hunit
  let Ψ : (Fin (m + 1) → A) → E ⊗[F] A := fun f => ∑ j, b j ⊗ₜ[F] (∑ i, p (N j i) * f i)
  have hr : Function.RightInverse Ψ (phi σ p m) := by
    intro f
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Ψ, map_sum, Finset.sum_apply, phi_tmul]
    have h1 : ∀ i, ∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i) = if k = i then 1 else 0 := fun i => by
      have h2 := congrArg p (congrFun (congrFun hMN k) i)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mul_apply, Matrix.one_apply, M, Matrix.of_apply, map_sum, map_mul] at h2
      rw [h2]
      split_ifs <;> simp
    calc _ = ∑ i, (∑ j, p ((σ ^ (k : ℕ)) (b j)) * p (N j i)) * f i := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = f k := by
          simp only [h1, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hadd : ∀ f g, Ψ (f + g) = Ψ f + Ψ g := fun f g => by
    simp only [Ψ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.tmul_add]
  have hl : Function.LeftInverse Ψ (phi σ p m) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp [Ψ]
    | add s t hs ht => rw [map_add (f := _), hadd, hs, ht]
    | tmul x a =>
      let c : Fin (m + 1) → E := fun l => algebraMap F E (b.repr x l)
      have hx : (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = M.mulVec c := by
        funext i
        conv_lhs => rw [← b.sum_repr x]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, c]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, Algebra.smul_def, mul_comm]
      have hc : ∀ j, ∑ i, N j i * (σ ^ (i : ℕ)) x = c j := fun j => by
        have : N.mulVec (fun i : Fin (m + 1) => (σ ^ (i : ℕ)) x) = c := by
          rw [hx, Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
        exact congrFun this j
      have h3 : ∀ j, ∑ i, p (N j i) * (p ((σ ^ (i : ℕ)) x) * a) = b.repr x j • a := fun j => by
        calc _ = p (∑ i, N j i * (σ ^ (i : ℕ)) x) * a := by
              set_option synthInstance.maxHeartbeats 100000 in
                simp only [map_sum, map_mul, Finset.sum_mul, mul_assoc]
          _ = _ := by rw [hc]; simp only [c, p.commutes, Algebra.smul_def]
      simp only [Ψ, phi_tmul, h3, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul, b.sum_repr]
  exact ⟨hl.injective, hr.surjective⟩

private theorem phi_shift (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) {m : ℕ}
    (hm : Module.finrank F E = m + 1) (p : E →ₐ[F] A) (t : E ⊗[F] A) (i : Fin (m + 1)) :
    phi σ p m (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) t) i = phi σ p m t (i + 1) := by
  have h1 : σ ^ (m + 1) = 1 := by rw [← orderOf_gen σ hσ hm]; exact pow_orderOf_eq_one σ
  have hv : ((i + 1 : Fin (m + 1)) : ℕ) = ((i : ℕ) + 1) % (m + 1) := by simp [Fin.val_add]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add (f := _), Pi.add_apply, hs, ht]
  | tmul x a =>
    rw [Algebra.TensorProduct.map_tmul, phi_tmul, phi_tmul, hv, ← pow_eq_pow_mod _ h1, pow_succ]
    rfl

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.galSplit :
    UpperTheory.ConvolutionTheory.L1.GalSplit := by
  intro F E _ _ _ _ _ _ σ hσ m hm A B _ _ _ _ e₀ p
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  refine ⟨e₀.symm.toRingEquiv.trans (RingEquiv.ofBijective (phi σ p m) (phi_bij σ hσ hm p)),
    fun x a i => ?_, fun b i => ?_⟩
  · show phi σ p m (e₀.symm (e₀ (x ⊗ₜ a))) i = _
    rw [AlgEquiv.symm_apply_apply, phi_tmul]
  · show phi σ p m (e₀.symm (galOf e₀ σ b)) i = phi σ p m (e₀.symm b) (i + 1)
    rw [← phi_shift σ hσ hm p]
    have h : e₀.symm (galOf e₀ σ b) =
        Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e₀.symm b) :=
      e₀.symm_apply_apply _
    rw [h]
end

