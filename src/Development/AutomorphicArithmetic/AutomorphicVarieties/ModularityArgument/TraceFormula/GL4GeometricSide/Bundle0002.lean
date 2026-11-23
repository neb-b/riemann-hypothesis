module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
public import Development.DiscreteGroups.PiInvariants.CasimirInfinity.CasInfOfIm
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OfLinearEquiv
section
noncomputable section

open MeasureTheory UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc
open scoped InnerProductSpace

namespace UpperTheory.V.Z.GSp4Splitting

section Gen

variable {G : Type} [TopologicalSpace G]

private def WC {W : Type} [AddCommGroup W] [Module ℂ W] (f : G → W) : Prop :=
  ∀ φ : Module.Dual ℂ W, Continuous fun g => φ (f g)

private theorem wc_of_basis {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W) {f : G → W}
    (h : ∀ i, Continuous fun g => b.repr (f g) i) : WC f := by
  intro φ
  have e : (fun g => φ (f g)) = fun g => ∑ i, b.repr (f g) i * φ (b i) := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (f g), map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  rw [e]
  exact continuous_finsetSum _ fun i _ => (h i).mul continuous_const

private theorem wc_hom {X Y : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [FiniteDimensional ℂ Y] {f : G → (X →ₗ[ℂ] Y)} (h : ∀ x, WC fun g => f g x) : WC f := by
  classical
  refine wc_of_basis ((Module.finBasis ℂ X).linearMap (Module.finBasis ℂ Y)) fun i => ?_
  have := h (Module.finBasis ℂ X i.2) ((Module.finBasis ℂ Y).coord i.1)
  refine this.congr fun g => ?_
  simp [Module.Basis.linearMap, Matrix.stdBasis, Matrix.ofLinearEquiv, LinearMap.toMatrix_apply]

private theorem exists_wint [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] {f : G → W} (hf : WC f) :
    ∃ q : W, ∀ φ : Module.Dual ℂ W, φ q = ∫ g, φ (f g) ∂ν := by
  let b := Module.finBasis ℂ W
  refine ⟨∑ i, (∫ g, b.coord i (f g) ∂ν) • b i, fun φ => ?_⟩
  have e : ∀ g, φ (f g) = ∑ i, b.coord i (f g) * φ (b i) := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← b.sum_repr (f g), map_sum]
    simp only [map_smul, smul_eq_mul, Module.Basis.coord_apply]
  simp_rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [integral_finsetSum _ fun i _ =>
    ((hf (b.coord i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_const _, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_mul_const, map_smul, smul_eq_mul]

private theorem dual_ext {W : Type} [AddCommGroup W] [Module ℂ W] {x y : W}
    (h : ∀ φ : Module.Dual ℂ W, φ x = φ y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  rw [map_sub, h, sub_self]

private theorem tr_inv [Group G] [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G)
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (τ : G → Module.End ℂ M) (hτ : ∀ g h, τ (g * h) = τ g * τ h) (hc : WC τ) (I : Submodule ℂ M)
    (hI : ∀ t, t ∈ I ↔ ∀ g, τ g t = t) (F : Module.End ℂ M) (hF : ∀ t ∈ I, F t ∈ I) :
    trOn I F = ∫ g, LinearMap.trace ℂ M (τ g * F) ∂ν := by
  obtain ⟨Q, hQ⟩ := exists_wint ν hc
  have h1 : ∀ g, τ g * Q = Q := fun g => dual_ext fun φ => by
    have := hQ (φ ∘ₗ LinearMap.mulLeft ℂ (τ g))
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, ← hτ] at this
    rw [this, hQ φ, integral_mul_left_eq_self (fun h => φ (τ h)) g]
  have h2 : ∀ t ∈ I, Q t = t := fun t ht => dual_ext fun φ => by
    have := hQ (φ ∘ₗ LinearMap.applyₗ t)
    simp only [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, (hI t).1 ht] at this
    simpa using this
  have h3 : ∀ t, (Q * F) t ∈ I := fun t => (hI _).2 fun g => by
    have := LinearMap.congr_fun (h1 g) (F t)
    simpa using this
  have h4 := hQ (LinearMap.trace ℂ M ∘ₗ LinearMap.mulRight ℂ F)
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at h4
  rw [← h4, ← LinearMap.trace_restrict_eq_of_forall_mem I (Q * F) h3]
  unfold trOn
  rw [dite_eq_left hF]
  congr 1
  refine LinearMap.ext fun t => Subtype.ext ?_
  exact (h2 _ (hF t t.2)).symm

private theorem trOn_map' {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (j : M →ₗ[ℂ] N)
    (hj : Function.Injective j) (S : Submodule ℂ M) (f : Module.End ℂ M) (g : Module.End ℂ N) (hf : ∀ x ∈ S, f x ∈ S)
    (h : ∀ x, g (j x) = j (f x)) : trOn (S.map j) g = trOn S f := by
  have hg : ∀ y ∈ S.map j, g y ∈ S.map j := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨f x, hf x hx, (h x).symm⟩
  unfold trOn
  rw [dite_eq_left hg, dite_eq_left hf, ← LinearMap.trace_conj' (f.restrict hf) (Submodule.equivMapOfInjective j hj S)]
  congr 1
  refine LinearMap.ext fun y => ?_
  obtain ⟨x, rfl⟩ := (Submodule.equivMapOfInjective j hj S).surjective y
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  exact Subtype.ext (h x)

end Gen

section Fin

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem tr_dualT (E : KMod n) (T : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E T).toLinearMap = LinearMap.trace ℂ E.V (T : E.V →ₗ[ℂ] E.V) := by
  let e : (E.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] (E.V →L[ℂ] ℂ) := LinearMap.toContinuousLinearMap
  rw [← LinearMap.trace_transpose' (T : E.V →ₗ[ℂ] E.V), ← LinearMap.trace_conj' _ e]
  congr 1

private theorem tr_flipA [FiniteDimensional ℂ V] (E : KMod n) (A : Module.End ℂ V) (T : E.V →L[ℂ] E.V) :
    LinearMap.trace ℂ _ (flipA E A T) = LinearMap.trace ℂ E.V (T : E.V →ₗ[ℂ] E.V) * LinearMap.trace ℂ V A := by
  let e := dualTensorHomEquiv ℂ (E.V →L[ℂ] ℂ) V
  rw [← tr_dualT, ← LinearMap.trace_transpose' (dualT E T).toLinearMap, ← LinearMap.trace_tensorProduct',
    ← LinearMap.trace_conj' _ e]
  congr 1
  refine LinearMap.ext fun t => ?_
  obtain ⟨u, rfl⟩ := e.surjective t
  rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v =>
    refine LinearMap.ext fun ξ => ?_
    simp [e, flipA, Module.Dual.transpose_apply]

private theorem mem_invA (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) (t : (E.V →L[ℂ] ℂ) →ₗ[ℂ] V) :
    t ∈ invA σ E ↔ ∀ g, flipA E (σ g) (E.ρ g) t = t := by
  have e : ∀ (g : Un n) (ξ : E.V →L[ℂ] ℂ), (ξ ∘L E.ρ g) ∘L E.ρ g⁻¹ = ξ := fun g ξ => by
    rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
    rfl
  constructor
  · intro ht g
    refine LinearMap.ext fun ξ => ?_
    show σ g (t (ξ ∘L E.ρ g)) = t ξ
    rw [← ht g, e]
  · intro ht g ξ
    have h : σ g (t ((ξ ∘L E.ρ g⁻¹) ∘L E.ρ g)) = t (ξ ∘L E.ρ g⁻¹) := LinearMap.congr_fun (ht g) _
    have e' := e g⁻¹ ξ
    rw [inv_inv] at e'
    rw [← h, e']

private theorem flipA_mul (E : KMod n) (A B : Module.End ℂ V) (T U : E.V →L[ℂ] E.V) :
    flipA E A T * flipA E B U = flipA E (A * B) (T * U) := rfl

private theorem flip_mem (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) {T : E.V →L[ℂ] E.V} {A : Module.End ℂ V}
    (hT : ∀ k, T * E.ρ k = E.ρ k * T) (hA : ∀ k, A * σ k = σ k * A) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht
  rw [mem_invA] at ht ⊢
  intro g
  rw [← Module.End.mul_apply, flipA_mul, ← hT, ← hA, ← flipA_mul, Module.End.mul_apply, ht g]

private theorem wc_flip [FiniteDimensional ℂ V] (σ : Un n →* (V →ₗ[ℂ] V))
    (hσ : ∀ v w : V, Continuous fun k => ⟪w, σ k v⟫_ℂ) (E : KMod n) : WC fun g => flipA E (σ g) (E.ρ g) := by
  let b := stdOrthonormalBasis ℂ V
  refine wc_hom fun t => wc_hom fun ξ => wc_of_basis b.toBasis fun i => ?_
  have hv : Continuous fun g : Un n => t (ξ ∘L E.ρ g) :=
    t.continuous_of_finiteDimensional.comp (continuous_const.clm_comp E.cont)
  have e : ∀ g : Un n, b.toBasis.repr (flipA E (σ g) (E.ρ g) t ξ) i =
      ∑ j, ⟪b j, t (ξ ∘L E.ρ g)⟫_ℂ * ⟪b i, σ g (b j)⟫_ℂ := by
    intro g
    rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    show ⟪b i, σ g (t (ξ ∘L E.ρ g))⟫_ℂ = _
    conv_lhs => rw [← b.sum_repr' (t (ξ ∘L E.ρ g))]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, inner_sum, inner_smul_right]
  simp_rw [e]
  exact continuous_finsetSum _ fun j _ => (continuous_const.inner hv).mul (hσ _ _)

private theorem fin_case [FiniteDimensional ℂ V] [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (σ : Un n →* (V →ₗ[ℂ] V))
    (hσ : ∀ v w : V, Continuous fun k => ⟪w, σ k v⟫_ℂ) (E : KMod n) (T : E.V →L[ℂ] E.V) (P A : Module.End ℂ V)
    (hT : ∀ k, T * E.ρ k = E.ρ k * T) (hP : IsAvg ν σ E T P) (hA : ∀ k, A * σ k = σ k * A) :
    LinearMap.trace ℂ V (P * A) = trOn (invA σ E) (flipA E A T) := by
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  rw [tr_inv ν (fun g => flipA E (σ g) (E.ρ g)) (fun g h => by simp only [flipA_mul, map_mul]) (wc_flip σ hσ E)
    (invA σ E) (mem_invA σ E) _ (flip_mem σ E hT hA)]
  simp only [flipA_mul, tr_flipA]
  let b := stdOrthonormalBasis ℂ V
  have hc : Continuous fun κ : Un n => LinearMap.trace ℂ E.V ((E.ρ κ * T : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V) :=
    ((LinearMap.trace ℂ E.V).comp (ContinuousLinearMap.coeLM ℂ)).continuous_of_finiteDimensional.comp
      (E.cont.mul continuous_const)
  simp_rw [LinearMap.trace_eq_sum_inner _ b, Finset.mul_sum, Module.End.mul_apply, hP _ _]
  exact (integral_finsetSum _ fun i _ =>
    (hc.mul (hσ _ _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).symm

private theorem iso_stable (σ : Un n →* (V →ₗ[ℂ] V)) (E : KMod n) {A : Module.End ℂ V}
    (hA : ∀ t ∈ invA σ E, ∀ ξ, ∃ t' ∈ invA σ E, ∃ ξ', A (t ξ) = t' ξ') : ∀ x ∈ isoSp σ E, A x ∈ isoSp σ E := by
  intro x hx
  have : isoSp σ E ≤ (isoSp σ E).comap A := by
    refine iSup_le ?_
    rintro t _ ⟨ξ, rfl⟩
    obtain ⟨t', ht', ξ', h⟩ := hA t.1 t.2 ξ
    exact (le_iSup (fun s : invA σ E => LinearMap.range s.1) ⟨t', ht'⟩) ⟨ξ', h.symm⟩
  exact this hx

end Fin

end UpperTheory.V.Z.GSp4Splitting

theorem UpperTheory.V.Z.GSp4Splitting.avgTr :
    AvgFacts → AvgTr := by
  intro hF n _ _ ν _ hν V _ _ σ hσ E T P A hT hP hA hfd
  haveI : IsProbabilityMeasure ν := ⟨hν⟩
  set S := isoSp σ E with hS
  have hPS : ∀ x, P x ∈ S := (hF n ν V σ hσ E T P hT hP).1
  have hσS : ∀ k, ∀ x ∈ S, σ k x ∈ S := fun k =>
    iso_stable σ E fun t ht ξ => ⟨t, ht, _, (ht k ξ).symm⟩
  have hAS : ∀ x ∈ S, A x ∈ S :=
    iso_stable σ E fun t ht ξ => ⟨_, flip_mem σ E (T := 1) (fun k => by simp) hA t ht, ξ, rfl⟩
  let σ' : Un n →* (S →ₗ[ℂ] S) :=
    { toFun := fun k => (σ k).restrict (hσS k)
      map_one' := LinearMap.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => LinearMap.ext fun x => Subtype.ext (by simp) }
  let j : ((E.V →L[ℂ] ℂ) →ₗ[ℂ] S) →ₗ[ℂ] ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V) := LinearMap.llcomp ℂ _ S V S.subtype
  have hj : Function.Injective j := fun a b h =>
    LinearMap.ext fun ξ => Subtype.ext (LinearMap.congr_fun h ξ)
  have hmap : invA σ E = (invA σ' E).map j := by
    refine le_antisymm (fun t ht => ?_) ?_
    · have hm : ∀ ξ, t ξ ∈ S := fun ξ =>
        (le_iSup (fun s : invA σ E => LinearMap.range s.1) ⟨t, ht⟩) ⟨ξ, rfl⟩
      exact ⟨t.codRestrict S hm, fun k ξ => Subtype.ext (ht k ξ), rfl⟩
    · rintro _ ⟨t, ht, rfl⟩ k ξ
      exact congrArg Subtype.val (ht k ξ)
  have hA' : ∀ k, A.restrict hAS * σ' k = σ' k * A.restrict hAS := fun k =>
    LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (hA k) x.1)
  refine ⟨?_, fun hne hb => hne ?_, ?_⟩
  · rw [hmap]
    infer_instance
  · refine iSup_eq_bot.2 fun t => ?_
    have ht : t.1 ∈ (⊥ : Submodule ℂ ((E.V →L[ℂ] ℂ) →ₗ[ℂ] V)) := hb ▸ t.2
    rw [(Submodule.mem_bot ℂ).1 ht, LinearMap.range_zero]
  · have hPA : ∀ x ∈ S, (P * A) x ∈ S := fun x _ => hPS _
    rw [hmap, trOn_map' j hj _ (flipA E (A.restrict hAS) T) _ (flip_mem σ' E hT hA') (fun _ => rfl),
      ← fin_case ν σ' (fun v w => hσ.cont v.1 w.1) E T (P.restrict fun x _ => hPS x) (A.restrict hAS) hT
        (fun v w => hP v.1 w.1) hA']
    unfold trOn
    rw [dite_eq_left hPA]
    rfl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.OpForm
section
noncomputable section

open NumberField MeasureTheory Measure
open GlobalTheory.CuspRep
open PositivityTheory.RgTw (G)

namespace UpperTheory.V.Z.GSp4Splitting

section Iter

variable {X Γ U ι : Type} [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  [Monoid Γ] [TopologicalSpace Γ] [ContinuousMul Γ] [AddCommGroup U] [Module ℂ U]

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
private theorem prod_cs {κ : Type} [Fintype κ] (e : κ → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) :
    Continuous (fun y : κ → X => ∏ v, e v (y v)) ∧ HasCompactSupport (fun y : κ → X => ∏ v, e v (y v)) := by
  refine ⟨continuous_finsetProd _ fun v _ => (he v).1.comp (continuous_apply v), ?_⟩
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (he v).2.isCompact) fun y hy => ?_
  obtain ⟨v, hv⟩ := not_forall.1 (mt Set.mem_univ_pi.2 hy)
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

private theorem iter_fin (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (m : ℕ) :
    ∀ (s : Fin m → ι) (u : U) (g : Γ),
      ∫ y : Fin m → X, (∏ i, e (s i) (y i)) * Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod) ∂(Measure.pi fun _ => μ) =
        (∏ i, val (s i)) * Φ ((List.ofFn fun i => P (s i)).prod u) g := by
  induction m with
  | zero =>
    intro s u g
    simp [Measure.pi_of_empty (fun _ : Fin 0 => μ)]
  | succ m ih =>
    intro s u g
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => μ) 0
    have hl : Continuous fun y : Fin (m + 1) → X => (List.ofFn fun i => j (s i) (y i)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun i _ => (hj _).comp (continuous_apply i)
    have hF : Integrable (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) (Measure.pi fun _ => μ) :=
      ((prod_cs (fun i => e (s i)) fun i => he _).1.mul ((hΦ u).comp (continuous_const.mul hl))).integrable_of_hasCompactSupport
        (prod_cs (fun i => e (s i)) fun i => he _).2.mul_right
    rw [← (hmp.symm _).integral_comp']
    refine (integral_prod _ (((hmp.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF)).trans ?_
    have hin : ∀ t : X, ∫ z : Fin m → X, (fun y : Fin (m + 1) → X => (∏ i, e (s i) (y i)) *
        Φ u (g * (List.ofFn fun i => j (s i) (y i)).prod)) ((MeasurableEquiv.piFinSuccAbove (fun _ => X) 0).symm (t, z))
          ∂(Measure.pi fun _ => μ) = (∏ i : Fin m, val (s i.succ)) *
            (e (s 0) t * Φ ((List.ofFn fun i : Fin m => P (s i.succ)).prod u) (g * j (s 0) t)) := by
      intro t
      have e1 : ∀ z : Fin m → X, (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => X) 0).symm (t, z) = Fin.cons t z :=
        fun z => Fin.insertNth_zero' t z
      simp only [e1, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ]
      simp only [← mul_assoc g, mul_assoc (e (s 0) t)]
      rw [integral_const_mul, ih (fun i => s i.succ) u (g * j (s 0) t)]
      ring
    refine (integral_congr_ae (Filter.Eventually.of_forall hin)).trans ?_
    rw [integral_const_mul, hloc, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    ring

private theorem iter_list [Fintype ι] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (e : ι → X → ℂ) (he : ∀ v, Continuous (e v) ∧ HasCompactSupport (e v)) (j : ι → X → Γ) (hj : ∀ v, Continuous (j v))
    (Φ : U → Γ → ℂ) (hΦ : ∀ u, Continuous (Φ u)) (val : ι → ℂ) (P : ι → Module.End ℂ U)
    (hloc : ∀ v u g, ∫ t, e v t * Φ u (g * j v t) ∂μ = val v * Φ (P v u) g) (l : List ι) (hl : l.Nodup) (hm : ∀ v, v ∈ l)
    (u : U) (g : Γ) :
    ∫ y : ι → X, (∏ v, e v (y v)) * Φ u (g * (l.map fun v => j v (y v)).prod) ∂(Measure.pi fun _ => μ) =
      (∏ v, val v) * Φ ((l.map P).prod u) g := by
  classical
  let σ : Fin l.length ≃ ι := List.Nodup.getEquivOfForallMemList l hl hm
  have hσ : ∀ {β : Type} (f : ι → β), (List.ofFn fun i => f (σ i)) = l.map f := fun f => by
    conv_rhs => rw [← List.ofFn_get l, List.map_ofFn]
    rfl
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => μ) σ
  have key := iter_fin μ e he j hj Φ hΦ val P hloc _ σ u g
  rw [hσ P, Equiv.prod_comp σ val] at key
  rw [← key, ← hmp.integral_comp']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have e1 : ∀ i, MeasurableEquiv.piCongrLeft (fun _ : ι => X) σ y (σ i) = y i := fun i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : ι => X) σ y i
  beta_reduce
  rw [← hσ, ← Equiv.prod_comp σ]
  simp only [e1]

end Iter

private theorem prod_single {ι M : Type} [DecidableEq ι] [Monoid M] (y : ι → M) :
    ∀ l : List ι, l.Nodup → ∀ w, (l.map fun v => (Pi.mulSingle v (y v) : ι → M)).prod w = if w ∈ l then y w else 1 := by
  intro l
  induction l with
  | nil => simp
  | cons a l ih =>
    intro hl w
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hl.2]
    by_cases h : w = a
    · subst h
      simp [hl.1]
    · simp [h]

private theorem split_two {X Y K : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (e : X × Y ≃ₜ* K) (μ : Measure K) [IsHaarMeasure μ]
    (mX : Measure X) [IsHaarMeasure mX] (mY : Measure Y) [IsHaarMeasure mY] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ f : K → ℂ, Continuous f → HasCompactSupport f →
      ∫ g, f g ∂μ = c * ∫ x, ∫ y, f (e (x, y)) ∂mY ∂mX := by
  let em : X × Y ≃ᵐ K := e.toHomeomorph.toMeasurableEquiv
  haveI : IsHaarMeasure ((mX.prod mY).map e) := ContinuousMulEquiv.isHaarMeasure_map _ e
  haveI : LocallyCompactSpace K := e.symm.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology K := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  have h := isMulLeftInvariant_eq_smul μ ((mX.prod mY).map e)
  have hpos := haarScalarFactor_pos_of_isHaarMeasure μ ((mX.prod mY).map e)
  generalize haarScalarFactor μ ((mX.prod mY).map e) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun f hf hs => ?_⟩
  rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  congr 1
  refine (integral_map_equiv em f).trans ?_
  exact integral_prod (fun z => f (e z))
    ((hf.comp e.continuous).integrable_of_hasCompactSupport (hs.comp_homeomorph e.toHomeomorph))

private theorem hecke_cont {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Subgroup Γ)
    (hK : IsOpen (K : Set Γ)) (h : Γ → ℂ) (hh : ∀ k ∈ K, ∀ g, h (g * k) = h g) : Continuous h := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hn : (fun x => g⁻¹ * x) ⁻¹' (K : Set Γ) ∈ nhds g :=
    (hK.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  refine continuousAt_const.congr (f := fun _ => h g) (Filter.mem_of_superset hn fun x hx => ?_)
  have := hh _ hx g
  simpa using this.symm


open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG in
private def split0 (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (InfinitePlace E → G n) × GL (Fin n) (Af E) ≃ₜ* PositivityTheory.Rg.BcB.E.H E n 0 where
  toFun p := (splitGA n p, 1)
  invFun g := (splitGA n).symm g.1
  left_inv p := by simp
  right_inv g := Prod.ext (by simp) (Subsingleton.elim _ _)
  map_mul' p q := by simp
  continuous_toFun := (splitGA n).continuous.prodMk continuous_const
  continuous_invFun := (splitGA n).symm.continuous.comp continuous_fst

end UpperTheory.V.Z.GSp4Splitting

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH PositivityTheory.Rg.BcB.CG.lc_G PositivityTheory.Rg.BcB.CG.sc_G PositivityTheory.Rg.BcB.CG.lc_GLf
  PositivityTheory.Rg.BcB.CG.sc_GLf PositivityTheory.Rg.BcB.CG.t2_GL_finite_adeles PositivityTheory.Rg.BcB.CG.borelSpaceH in
open PositivityTheory.Rg.BcB.CG in
theorem UpperTheory.V.Z.GSp4Splitting.opForm :
    HeckeMem → RlComm → LocAct → OpForm := by
  intro _ _ hL E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D lam hch _ _ ν _ hν _ _ μC _ μ _ P hP
  classical
  haveI : IsHaarMeasure (Measure.pi fun _ : InfinitePlace E => μC) := pi.isHaarMeasure _
  obtain ⟨c, hc0, hc⟩ := split_two (split0 E n) μ (Measure.pi fun _ : InfinitePlace E => μC) μf
  refine ⟨c, hc0, fun k val T hk h hh ψ u hu x => ?_⟩
  set e : InfinitePlace E → G n → ℂ := fun w => phiOf (lefE n (lam w)) (lefT n (lam w)) (k w) with he
  have hecs : ∀ w, Continuous (e w) ∧ HasCompactSupport (e w) := fun w =>
    PositivityTheory.Rg.BcB.F.F0.phiOf_cs μC _ _ _ _ _ (hk w)
  have hhc : Continuous h := hecke_cont K hKo h fun k hk g => by simpa using hh.2 1 K.one_mem k hk g
  have hcont : ∀ φ : π.V, Continuous φ.1.1 := fun φ => DiscreteGroups.T1.G.continuous_of_mem π φ.2
  have hphi : ∀ p : (InfinitePlace E → G n) × GL (Fin n) (Af E), phiProd lam k h (split0 E n p) = (∏ w, e w (p.1 w)) * h p.2 := by
    intro p
    have e1 : ∀ w, infAt E n w (split0 E n p).1 = p.1 w := fun w => gInf_splitGA n p w
    have e2 : finOf E n (split0 E n p).1 = p.2 := gFin_splitGA n p
    simp only [phiProd, e1, e2, he]
  have hphi' : phiProd lam k h = (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2) ∘
      (split0 E n).symm.toHomeomorph := by
    funext y
    obtain ⟨p, rfl⟩ := (split0 E n).surjective y
    rw [hphi]
    exact (congrArg (fun p : (InfinitePlace E → G n) × GL (Fin n) (Af E) => (∏ w, e w (p.1 w)) * h p.2)
      ((split0 E n).symm_apply_apply p)).symm
  have hpc : Continuous (phiProd lam k h) := by
    rw [hphi']
    exact (((prod_cs e hecs).1.comp continuous_fst).mul (hhc.comp continuous_snd)).comp (Homeomorph.continuous _)
  have hps : HasCompactSupport (phiProd lam k h) := by
    rw [hphi']
    refine HasCompactSupport.comp_homeomorph ?_ _
    refine HasCompactSupport.intro ((prod_cs e hecs).2.isCompact.prod hh.1.isCompact) fun p hp => ?_
    rcases not_and_or.1 hp with h1 | h1
    · rw [show (∏ w, e w (p.1 w)) = 0 from
        image_eq_zero_of_notMem_tsupport (f := fun y : InfinitePlace E → G n => ∏ v, e v (y v)) h1, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]
  rw [hc (fun y => phiProd lam k h y * ψ.1.1 (x * y.1))
    (hpc.mul ((hcont ψ).comp (continuous_const.mul continuous_fst))) hps.mul_right, mul_assoc]
  congr 1
  let j : InfinitePlace E → G n → GA E n := fun w t => infP n (Pi.mulSingle w t)
  let l := (Finset.univ : Finset (InfinitePlace E)).toList
  let ih : (InfinitePlace E → G n) →* GA E n := MonoidHom.mk' (infP n) (infinitePart_mul n)
  have hjl : ∀ y : InfinitePlace E → G n, (l.map fun v => j v (y v)).prod = infP n y := by
    intro y
    have e1 : (l.map fun v => (Pi.mulSingle v (y v) : InfinitePlace E → G n)).prod = y := by
      funext w
      rw [prod_single y l (Finset.nodup_toList _), if_pos (Finset.mem_toList.2 (Finset.mem_univ w))]
    conv_rhs => rw [← e1]
    refine Eq.trans ?_ (map_list_prod ih _).symm
    rw [List.map_map]
    rfl
  have hj : ∀ w, Continuous (j w) := fun w => (continuous_infP n).comp (continuous_mulSingle (A := fun _ => G n) w)
  have key := iter_list μC e hecs j hj (fun u => (D.i u).1.1) (fun u => hcont _) (fun w => val w (infOf (lam w))) P
    (fun w u g => by
      have := hL E n hn π hθ K hKo hKc hKθ μf D w (lam w) (hch w) ν hν μC _ _ (P w) (hP w) (k w) (val w) (T w) (hk w) u g
      simp only [along_val] at this
      exact this) l (Finset.nodup_toList _) (fun v => Finset.mem_toList.2 (Finset.mem_univ v)) u x
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hjl, hu, heckeOp, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  beta_reduce
  rw [hphi, mul_assoc, mul_assoc x]
  rfl
end
end

