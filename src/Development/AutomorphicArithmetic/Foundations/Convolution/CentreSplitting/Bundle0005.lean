module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ConjCarries
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem map_closure {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H)
    (hU : ∀ v, ‖U v‖ = ‖v‖) (A V : Submodule ℂ H) :
    V = A.topologicalClosure ↔ V.map U.toLinearMap = (A.map U.toLinearMap).topologicalClosure := by
  have hi : Isometry U := AddMonoidHomClass.isometry_of_norm U hU
  have e : (A.map U.toLinearMap).topologicalClosure = A.topologicalClosure.map U.toLinearMap := SetLike.coe_injective (by
    rw [Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.map_coe, Submodule.topologicalClosure_coe]
    exact hi.isClosedEmbedding.closure_image_eq _)
  rw [e]
  exact (Submodule.map_injective_of_injective (f := U.toLinearMap) hi.injective).eq_iff.symm

theorem UpperTheory.ConvolutionTheory.Dp.conjCarries :
    UpperTheory.ConvolutionTheory.Dp.ConjCarries := by
  intro E _ _ _ n μ _ θ σ s hs hθ π π' V' hsp
  set m : GA E n →* GA E n := Matrix.GeneralLinearGroup.map s.toRingHom with hm
  have hsurj : Function.Surjective m := fun g => ⟨Matrix.GeneralLinearGroup.map s.symm.toRingHom g, by
    ext i j : 2
    exact s.apply_symm_apply _⟩
  have hcen : ∀ t, m (centralSection E n t) = centralSection E n t := (galCentral E n σ s hs).2
  have hmem : ∀ (ρ : CuspSub E n) (f : GA E n → ℂ), f ∈ (UpperTheory.CBC.Cusp.cx ρ).space ↔ ∃ φ ∈ Cm.carrier ρ, f = φ.1 := fun ρ f => by
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← Cm.map_carrier] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      exact ⟨ψ, hψ, rfl⟩
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨_, hφ, rfl⟩
  have h1 : ∀ ψ ∈ Cm.carrier π', ∃ φ ∈ Cm.carrier π, ∀ g, ψ.1 g = φ.1 (m g) := fun ψ hψ => by
    have h := (hmem π' _).2 ⟨ψ, hψ, rfl⟩
    rw [hsp] at h
    obtain ⟨f, hf, e⟩ := h
    obtain ⟨φ, hφ, rfl⟩ := (hmem π f).1 hf
    exact ⟨φ, hφ, fun g => (congrFun e g).symm⟩
  have h2 : ∀ φ ∈ Cm.carrier π, ∃ ψ ∈ Cm.carrier π', ∀ g, ψ.1 g = φ.1 (m g) := fun φ hφ => by
    have h : (fun g => φ.1 (m g)) ∈ (UpperTheory.CBC.Cusp.cx π').space := by
      rw [hsp]
      exact ⟨φ.1, (hmem π _).2 ⟨φ, hφ, rfl⟩, rfl⟩
    obtain ⟨ψ, hψ, e⟩ := (hmem π' _).1 h
    exact ⟨ψ, hψ, fun g => (congrFun e g).symm⟩
  have hc : Cm.carrier π' ≤ centralCuspForms E n ↔ Cm.carrier π ≤ centralCuspForms E n := by
    constructor
    · intro h φ hφ t x
      obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      obtain ⟨y, rfl⟩ := hsurj x
      have h3 := h hψ t y
      rwa [e, e, map_mul, hcen] at h3
    · intro h ψ hψ t x
      obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      have h3 := h hφ t (m x)
      show ψ.1 (centralSection E n t * x) = ψ.1 x
      rw [e, e, map_mul, hcen]
      exact h3
  rw [exSummand E n μ π' V', exSummand E n μ π, hc]
  refine and_congr_right fun h => ?_
  have hU : ∀ φ ∈ Cm.carrier π, ∀ ψ ∈ Cm.carrier π', (∀ g, ψ.1 g = φ.1 (m g)) → θ.U (clsL μ ψ) = clsL μ φ := fun φ hφ ψ hψ e =>
    (twCls E n μ θ φ (h hφ) ψ (hc.2 h hψ)).2 fun x => (e x).trans (congrArg φ.1 (hθ x).symm)
  have e : (Cm.carrier π).map (clsL μ) = ((Cm.carrier π').map (clsL μ)).map θ.U.toLinearMap := by
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => ?_)
      (Submodule.map_le_iff_le_comap.2 (Submodule.map_le_iff_le_comap.2 fun ψ hψ => ?_))
    · obtain ⟨ψ, hψ, e⟩ := h2 φ hφ
      exact Submodule.mem_map.2 ⟨_, Submodule.mem_map_of_mem hψ, hU φ hφ ψ hψ e⟩
    · obtain ⟨φ, hφ, e⟩ := h1 ψ hψ
      exact Submodule.mem_map.2 ⟨φ, hφ, (hU φ hφ ψ hψ e).symm⟩
  rw [e]
  exact map_closure θ.U (twUnitary E n μ θ).1 _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.InfZcCoeff
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem UpperTheory.ConvolutionTheory.Dp.infZc_prod {n : ℕ} {m : Multiset ℂ} (hm : m.card = n) (u : ℂ) :
    (m.map fun x => u + x).prod = u ^ n + ∑ i : Fin n, u ^ (n - (i + 1)) * m.esymm (i + 1) := by
  have h := congrArg (Polynomial.eval u) (Multiset.prod_X_add_C_eq_sum_esymm m)
  rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
  simp only [Function.comp_def, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, hm] at h
  rw [h, Finset.sum_range_succ', add_comm, ← Fin.sum_univ_eq_sum_range
    (fun i => m.esymm (i + 1) * u ^ (n - (i + 1))) n]
  congr 1
  · simp [Multiset.esymm]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem UpperTheory.ConvolutionTheory.Dp.infZc_coeff {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    simp only [Finsupp.single_apply]
    rw [if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

theorem UpperTheory.ConvolutionTheory.Dp.infZc :
    UpperTheory.ConvolutionTheory.Dp.InfZc := by
  intro E _ _ _ n π τ m
  have hc := (UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2
  have key : ∀ (u : ℂ) (φ : GlobalTheory.CuspRep.Sm E n), GlobalTheory.CuspRep.cap τ u φ =
      u ^ n • φ + ∑ i : Fin n, u ^ (n - (i + 1)) • Cm.uC E n (UpperTheory.ConvolutionTheory.zc τ i) φ := fun u φ => by
    rw [← Cm.uC_capC, hc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_add (f := _), map_smul, map_one, map_sum, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.sum_apply, Module.End.one_apply]
  change (m.card = n ∧ ∀ u : ℂ, ∀ φ ∈ π.V, GlobalTheory.CuspRep.cap τ u φ = (m.map fun x => u + x).prod • φ) ↔ _
  refine and_congr_right fun hm => ⟨fun h i φ hφ => ?_, fun h u φ hφ => ?_⟩
  · rw [← sub_eq_zero]
    refine infZc_coeff (fun i : Fin n => Cm.uC E n (UpperTheory.ConvolutionTheory.zc τ i) φ - m.esymm (i + 1) • φ) (fun u => ?_) i
    have := h u φ hφ
    rw [key, infZc_prod hm, add_smul, add_right_inj, Finset.sum_smul] at this
    simp only [smul_sub, Finset.sum_sub_distrib, this, smul_smul, sub_self]
  · rw [key, infZc_prod hm, add_smul, Finset.sum_smul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [h i φ hφ, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem proj_range {G H X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G H) (σ : Representation ℂ G X) (τ : Representation ℂ G Y) (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖)
    (hσ : ∀ x, ∃ U : Subgroup G, IsCompact (U : Set G) ∧ IsOpen (U : Set G) ∧ ∀ u ∈ U, σ u x = x)
    (hτ : GroundTheory.Automorphic.IsAdmissible τ) (i : Y →ₗ[ℂ] H) (f : X →ₗ[ℂ] H) (hi : ∀ g y, i (τ g y) = ρ g (i y))
    (hf : ∀ g x, f (σ g x) = ρ g (f x)) {x₀ : X} {y₀ : Y} (h0 : inner ℂ (i y₀) (f x₀) ≠ 0) :
    ∃ f' : X →ₗ[ℂ] H, f' ≠ 0 ∧ (∀ g x, f' (σ g x) = ρ g (f' x)) ∧ ∀ x, f' x ∈ LinearMap.range i := by
  let W := (LinearMap.range i).topologicalClosure
  let L : G → H →ₗᵢ[ℂ] H := fun g => ⟨ρ g, hρ g⟩
  have hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W := fun g v hv =>
    map_mem_closure (L g).continuous hv fun z ⟨y, hy⟩ => ⟨τ g y, by rw [hi, hy]; try rfl⟩
  have hP : ∀ g v, W.starProjection (ρ g v) = ρ g (W.starProjection v) := fun g v => by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW g _ (W.starProjection_apply_mem v)) fun w hw => ?_
    have e : w = ρ g (ρ g⁻¹ w) := by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
    rw [← map_sub, e]
    exact ((L g).inner_map_map _ _).trans (W.starProjection_inner_eq_zero v _ (hW _ _ hw))
  refine ⟨W.starProjection.toLinearMap ∘ₗ f, fun e => h0 ?_, fun g x => ?_, fun x => ?_⟩
  · have h1 : W.starProjection (f x₀) = 0 := LinearMap.congr_fun e x₀
    have h2 := W.starProjection_inner_eq_zero (f x₀) (i y₀) (Submodule.le_topologicalClosure _ ⟨y₀, rfl⟩)
    rw [h1, sub_zero] at h2
    exact inner_eq_zero_symm.1 h2
  · exact (congrArg W.starProjection (hf g x)).trans (hP g _)
  · obtain ⟨U, hc, ho, hU⟩ := hσ x
    let ρ' : Representation ℂ G W := (⟨W, fun g _ hv => hW g _ hv⟩ : Subrepresentation ρ).toRepresentation
    let J : Y →ₗ[ℂ] W := i.codRestrict W fun y => Submodule.le_topologicalClosure _ ⟨y, rfl⟩
    have hd : DenseRange J := fun v => by
      rw [closure_subtype]
      refine closure_mono ?_ v.2
      rintro _ ⟨y, rfl⟩
      exact ⟨J y, ⟨y, rfl⟩, rfl⟩
    have h1 := fixedDense G W Y ρ' τ J U hc (fun g v => hρ g v) hτ.1 (fun g y => Subtype.ext (hi g y)) hd
      ⟨_, W.starProjection_apply_mem (f x)⟩ fun u hu => Subtype.ext (by
        show ρ u (W.starProjection (f x)) = W.starProjection (f x)
        rw [← hP, ← hf, hU u hu])
    have := hτ.2 U hc ho
    have h2 : IsClosed (((fixedVectors τ U).map J : Submodule ℂ W) : Set W) := Submodule.closed_of_finiteDimensional _
    obtain ⟨y, -, hy⟩ := closure_minimal (t := (((fixedVectors τ U).map J : Submodule ℂ W) : Set W))
      (by rintro _ ⟨y, hy, rfl⟩; exact Submodule.mem_map_of_mem (mem_fixedVectors.2 hy)) h2 h1
    exact ⟨y, congrArg Subtype.val hy⟩

set_option maxHeartbeats 800000 in
open PositivityTheory.Rg.Rs.C3.Fl in
theorem UpperTheory.ConvolutionTheory.Dp.locIff :
    UpperTheory.ConvolutionTheory.Dp.LocIff := by
  intro E _ _ _ n μ _ π V h w σ
  obtain ⟨J, hi, -, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hJ := hJ' w
  constructor
  · rintro ⟨f, h0, hf⟩
    exact ⟨J ∘ₗ f, fun e => h0 (LinearMap.ext fun x => hi ((LinearMap.congr_fun e x).trans (map_zero J).symm)),
      fun g x => (congrArg J (hf g x)).trans (hJ g _)⟩
  rintro ⟨f, h0, hf⟩
  obtain ⟨D⟩ := nonempty_adelicDecomposition _ (Cm.isIrreducible_toModule π) (Cm.isAdmissible_toModule π)
  obtain ⟨j, hj0, hj⟩ := (locFlath E n π D w
    { V := D.finite.W w, ρ := D.finite.π w, smooth := (D.finite.isAdmissible w).1, irred := D.finite.isIrreducible w }).2
    ⟨Representation.Equiv.refl _⟩
  have hm : ∀ a b v, RG μ (a * b) v = RG μ a (RG μ b v) := fun a b v => by
    simp only [RG]
    rw [retractOne_mul, UnitaryRep.map_mul]; rfl
  have h1 : ∀ v, RG μ 1 v = v := fun v => by
    have e : retractOne (1 : AdelicGLn.AdelicGL E n) = 1 := retractOne_coe 1
    simp only [RG, e, UnitaryRep.map_one]; rfl
  have hn : ∀ a v, ‖RG μ a v‖ = ‖v‖ := fun a v => UnitaryRep.norm_map _ _ _
  have hin : ∀ a u v, inner ℂ (RG μ a u) v = inner ℂ u (RG μ a⁻¹ v) := fun a u v => by
    have e : v = RG μ a (RG μ a⁻¹ v) := by rw [← hm, mul_inv_cancel, h1]
    conv_lhs => rw [e]
    exact (⟨(RG μ a).toLinearMap, hn a⟩ : LL μ →ₗᵢ[ℂ] LL μ).inner_map_map _ _
  let i : D.finite.W w →ₗ[ℂ] LL μ := V.subtype ∘ₗ J ∘ₗ j
  have hi' : ∀ g y, i (D.finite.π w g y) = RG μ (iota n w g) (i y) := fun g y =>
    congrArg Subtype.val ((congrArg J (hj g y)).trans (hJ g _))
  have hex : ∃ a, wPart n w a = 1 ∧ ∃ y x, inner ℂ (RG μ a (i y)) (f x).1 ≠ 0 := by
    by_contra hno
    push Not at hno
    let S : Submodule ℂ (LL μ) := Submodule.span ℂ {v | ∃ a y, wPart n w a = 1 ∧ v = RG μ a (i y)}
    have hS : ∀ v, v ∈ Sᗮ ↔ ∀ a y, wPart n w a = 1 → inner ℂ (RG μ a (i y)) v = 0 := fun v => by
      refine ⟨fun hv a y ha => hv _ (Submodule.subset_span ⟨a, y, ha, rfl⟩), fun hv u hu => ?_⟩
      induction hu using Submodule.span_induction with
      | mem u hu => obtain ⟨a, y, ha, rfl⟩ := hu; exact hv a y ha
      | zero => simp
      | add u u' _ _ h1 h2 => rw [inner_add_left, h1, h2, add_zero]
      | smul c u _ h1 => rw [inner_smul_left, h1, mul_zero]
    rcases h.summand.irred (V ⊓ Sᗮ) inf_le_left (h.summand.closed.inter S.isClosed_orthogonal) (fun g v hv =>
      ⟨h.summand.inv g v hv.1, (hS _).2 fun a y ha => by
        have e : rightRegularRep (rationalGLOne (K := E) (n := n)) μ g v = RG μ (g⁻¹.1)⁻¹ v := by
          simp only [RG, Subgroup.coe_inv, inv_inv, retractOne_coe]
        rw [e, ← hin, ← hm, ← awayPart_mul_iota_wPart (w := w) (g⁻¹.1 * a), hm, ← hi']
        exact (hS v).1 hv.2 _ _ (wPart_awayPart _)⟩) with hb | hb
    · refine h0 (LinearMap.ext fun x => Subtype.ext ?_)
      have : (f x).1 ∈ V ⊓ Sᗮ := ⟨(f x).2, (hS _).2 fun a y ha => hno a ha y x⟩
      rwa [hb] at this
    · refine hj0 (LinearMap.ext fun y => hi (Subtype.ext ?_))
      have h2 : i y ∈ V ⊓ Sᗮ := hb.ge (J (j y)).2
      have h3 := (hS _).1 h2.2 1 y (map_one _)
      rw [h1] at h3
      have h4 : i y = 0 := inner_self_eq_zero.1 h3
      exact h4.trans (congrArg Subtype.val (map_zero J)).symm
  obtain ⟨a, ha, y, x, hne⟩ := hex
  rw [hin] at hne
  obtain ⟨f', h2, h3, h4⟩ := proj_range (localRepresentationL2 μ w) σ.ρ (D.finite.π w) (fun g v => hn _ v)
    (fun x => (isSmooth_iff_forall_exists σ.ρ).1 σ.smooth x) (D.finite.isAdmissible w) i
    ((RG μ a⁻¹).toLinearMap ∘ₗ V.subtype ∘ₗ f) hi' (fun g x => by
      show RG μ a⁻¹ (f (σ.ρ g x)).1 = RG μ (iota n w g) (RG μ a⁻¹ (f x).1)
      rw [hf, ← hm, ← commute_iota (by rw [map_inv, ha, inv_one]), hm]
      rfl) hne
  have hk : Function.Injective (V.subtype ∘ₗ J) := V.injective_subtype.comp hi
  have h5 : ∀ x, f' x ∈ LinearMap.range (V.subtype ∘ₗ J) := fun x => (h4 x).elim fun y e => ⟨j y, e⟩
  let t := LinearEquiv.ofInjective _ hk
  have ht : ∀ x, (J (t.symm ⟨f' x, h5 x⟩)).1 = f' x := fun x => congrArg Subtype.val (t.apply_symm_apply ⟨f' x, h5 x⟩)
  refine ⟨t.symm.toLinearMap ∘ₗ f'.codRestrict _ h5, fun e => h2 (LinearMap.ext fun x => ?_), fun g x => hi (Subtype.ext ?_)⟩
  · have e1 : t.symm ⟨f' x, h5 x⟩ = 0 := LinearMap.congr_fun e x
    rw [← ht, e1, map_zero]
    rfl
  · refine (ht _).trans ((h3 g x).trans ?_)
    rw [← ht x]
    exact (congrArg Subtype.val (hJ g _)).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SatIff
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem continuous_heckeVec {G H : Type} [Group G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    {ρ : Representation ℂ G H} (hρ : ∀ g v, ‖ρ g v‖ = ‖v‖) {K : Subgroup G} (hK : Formalism.UG.IsCommensurated K)
    {h : G → ℂ} (hh : h ∈ Formalism.UG.Hecke ℂ K) : Continuous fun v => GlobalTheory.LFun.heckeVec ρ K h v := by
  have hS : (Function.support fun c : G ⧸ K => h c.out).Finite := Formalism.UG.P.finite_support_cosets hK hh.2
  have hc : ∀ g, Continuous (ρ g) := fun g => (AddMonoidHomClass.isometry_of_norm (ρ g) (hρ g)).continuous
  have e : (fun v => GlobalTheory.LFun.heckeVec ρ K h v) = fun v => ∑ c ∈ hS.toFinset, h c.out • ρ c.out v := by
    funext v
    refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
    simp only [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun h0 => hc' (by simp [h0])
  rw [e]
  exact continuous_finsetSum _ fun c _ => (hc _).const_smul _

theorem UpperTheory.ConvolutionTheory.Dp.satIff :
    UpperTheory.ConvolutionTheory.Dp.SatIff := by
  intro E _ _ _ n μ _ π V h w B
  obtain ⟨J, hi, hd, -, hJ'⟩ := UpperTheory.ConvolutionTheory.Dp.locEmb E n μ π V h
  have hJ := hJ' w
  have hρ : ∀ g v, ‖locOn h.summand w g v‖ = ‖v‖ := fun g v => by
    change ‖RG μ (finGL E n (locGL E n w g)) (v : LL μ)‖ = ‖(v : LL μ)‖
    exact UnitaryRep.norm_map _ _ _
  have hτ : ∀ x, IsOpen {g | π.locRep w g x = x} := fun x => by
    obtain ⟨ψ, rfl⟩ := (Cm.carrierEq π).surjective x
    have h1 := ((Cm.isAdmissible_toModule π).1 ψ).preimage (CuspSub.continuous_locGL w)
    convert h1 using 1
    ext g
    have e : π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ((Cm.toModule π).τ (locGL E n w g) ψ) := by
      rw [CuspSub.locRep_eq, Cm.carrierEq_τ]
    change π.locRep w g (Cm.carrierEq π ψ) = Cm.carrierEq π ψ ↔ (Cm.toModule π).τ (locGL E n w g) ψ = ψ
    rw [e]
    exact (Cm.carrierEq π).injective.eq_iff
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2
  have hdense := UpperTheory.ConvolutionTheory.Dp.fixedDense _ _ _ (locOn h.summand w) (π.locRep w) J (GlobalTheory.LFun.KGL w (n := n)) hK hρ hτ hJ hd
  have hcl : ∀ ϖ, Formalism.UG.IsUnifV E w ϖ → ∀ (j : ℕ) (c : ℂ), IsClosed {v : V |
      GlobalTheory.LFun.heckeVec (locOn h.summand w) (GlobalTheory.LFun.KGL w (n := n)) (Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j) v = c • v} :=
    fun ϖ hϖ j c => isClosed_eq (continuous_heckeVec hρ (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ j))
      (continuous_const_smul c)
  change GlobalTheory.LFun.HasSatGL w (π.locRep w) B ↔ _
  constructor
  · intro hB
    refine ⟨?_, fun v hv h0 => ?_⟩
    · obtain ⟨x, hx⟩ := hB.exists_vec
      have h1 := hx.map J hJ fun e => hx.1 (hi (by rw [e, map_zero]))
      exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
    · refine ⟨h0, hv, hB.card, fun ϖ hϖ j hj => ?_⟩
      have hv' := hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv u hu
      refine closure_minimal ?_ (hcl ϖ hϖ j _) hv'
      rintro _ ⟨x, hx, rfl⟩
      by_cases hx0 : x = 0
      · subst hx0
        simp [GlobalTheory.LFun.heckeVec]
      · exact ((hB.2 x (GlobalTheory.LGrp.mem_fixed.2 hx) hx0).map J hJ
          fun e => hx0 (hi (by rw [e, map_zero]))).2.2.2 ϖ hϖ j hj
  · intro hB
    obtain ⟨v, hv⟩ := hB.exists_vec
    have hv' := hdense v fun u hu => GlobalTheory.LGrp.mem_fixed.1 hv.2.1 u hu
    refine ⟨(Submodule.ne_bot_iff _).2 ?_, fun x hx h0 => ?_⟩
    · by_contra hno
      push Not at hno
      have hsub : J '' {x | ∀ u ∈ GlobalTheory.LFun.KGL w (n := n), π.locRep w u x = x} ⊆ {0} := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hno x (GlobalTheory.LGrp.mem_fixed.2 hx), map_zero]
        rfl
      exact hv.1 (closure_minimal hsub isClosed_singleton hv')
    · have hJx : J x ∈ GlobalTheory.PRep.fixed (locOn h.summand w) (GlobalTheory.LFun.KGL w (n := n)) :=
        GlobalTheory.LGrp.mem_fixed.2 fun k hk => by rw [← hJ, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
      exact GlobalTheory.LFun.IsSatVecGL.of_map J hJ hi (hB.2 _ hJx fun e => h0 (hi (by rw [e, map_zero])))
end

