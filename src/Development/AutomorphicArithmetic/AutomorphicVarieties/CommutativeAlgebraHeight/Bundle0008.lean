module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ChEltOne
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)

private theorem chiS_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y) = (D.chiS S y).map (f : S →+* T) := by
  have h := D.nat (Polynomial S) (Polynomial T) (Polynomial.mapAlgHom f) (Polynomial.X ⊗ₜ 1 -
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom A S (Polynomial S)) (AlgHom.id A E) y)
  refine Eq.trans ?_ h
  unfold Det.chiS
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y with
    | tmul s x => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem F_map (S T : Type) [CommRing S] [Algebra A S] [CommRing T] [Algebra A T] (f : S →ₐ[A] T)
    (y : S ⊗[A] E) :
    Polynomial.aeval (Algebra.TensorProduct.map f (AlgHom.id A E) y)
      (D.chiS T (Algebra.TensorProduct.map f (AlgHom.id A E) y)) =
      Algebra.TensorProduct.map f (AlgHom.id A E) (Polynomial.aeval y (D.chiS S y)) := by
  rw [chiS_map]
  generalize D.chiS S y = p
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add (f := _), map_add (f := _), hp, hq]
  | monomial k a =>
    simp [Polynomial.aeval_monomial, Algebra.TensorProduct.algebraMap_apply]

private theorem expand {ι : Type} (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S)
    (N : Set E) (w : MvPolynomial ι A ⊗[A] E)
    (h : ∀ α, TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) ∈ N) :
    Algebra.TensorProduct.map f (AlgHom.id A E) w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  classical
  have hw : ∃ s : Finset (ι →₀ ℕ), ∀ t, s ⊆ t → w = ∑ α ∈ t, (MvPolynomial.monomial α (1 : A)) ⊗ₜ[A]
      TensorProduct.lid A E ((MvPolynomial.lcoeff A α).rTensor E w) := by
    clear h
    induction w with
    | add a b ha hb =>
      obtain ⟨s, hs⟩ := ha
      obtain ⟨s', hs'⟩ := hb
      refine ⟨s ∪ s', fun t ht => ?_⟩
      simp only [map_add (f := _), tmul_add, Finset.sum_add_distrib]
      rw [← hs t (Finset.subset_union_left.trans ht), ← hs' t (Finset.subset_union_right.trans ht)]
    | tmul p z =>
      refine ⟨p.support, fun t ht => ?_⟩
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, MvPolynomial.lcoeff_apply, ← smul_tmul,
        ← sum_tmul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      congr 1
      conv_lhs => rw [p.as_sum]
      refine Finset.sum_subset ht fun α _ hα => ?_
      rw [MvPolynomial.notMem_support_iff.1 hα, map_zero]
  obtain ⟨s, hs⟩ := hw
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hs s le_rfl, map_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  rw [Algebra.TensorProduct.map_tmul, ← mul_one (f _), ← smul_eq_mul, ← smul_tmul']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, h α, rfl⟩)

private theorem part1 (S : Type) [CommRing S] [Algebra A S] (y : S ⊗[A] E) :
    Polynomial.aeval y (D.chiS S y) ∈
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  obtain ⟨k, s, x, rfl⟩ := TensorProduct.exists_sum_tmul_eq y
  have : ∑ j, s j ⊗ₜ[A] x j =
      Algebra.TensorProduct.map (MvPolynomial.aeval s) (AlgHom.id A E) (Det.gen (A := A) x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum]
  rw [this, F_map]
  exact expand S _ _ _ fun α => TwoSidedIdeal.subset_span ⟨k, x, α, rfl⟩

private theorem rT_mem (P S : Type) [CommRing P] [Algebra A P] [CommRing S] [Algebra A S] (g : P →ₗ[A] S)
    (N : Set E) (w : P ⊗[A] E) (h : w ∈ Submodule.span P ((fun z : E => (1 : P) ⊗ₜ[A] z) '' N)) :
    g.rTensor E w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) := by
  suffices H : ∀ p : P, g.rTensor E (p • w) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' N) by
    simpa using H 1
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    intro p
    rw [smul_tmul', LinearMap.rTensor_tmul, ← mul_one (g _), ← smul_eq_mul, ← smul_tmul']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hz, rfl⟩)
  | zero => intro p; simp
  | add x y _ _ hx hy => intro p; rw [smul_add, map_add (f := _)]; exact add_mem (hx p) (hy p)
  | smul a x _ hx => intro p; rw [smul_smul]; exact hx _

private theorem chElt_bc (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → S ⊗[A] E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt x α = ((MvPolynomial.lcoeff S α).restrictScalars A).rTensor E
      (Polynomial.aeval (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x))
        (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen x)))) := by
  unfold Det.chElt
  generalize Det.gen (A := S) x = y
  have h1 : (D.baseChange S).chiS (MvPolynomial (Fin k) S) y =
      D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y) := by
    unfold Det.chiS
    rw [(d_bc D S).1]
    congr 1
    rw [map_sub]
    congr 1
    · rw [Algebra.TensorProduct.one_def, Det.cancel_tmul]; simp
    · induction y with
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | tmul s y =>
        induction y with
        | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
        | tmul b z => simp [Det.cancel_tmul]
  rw [h1, Polynomial.aeval_algHom_apply]
  generalize Polynomial.aeval y (D.chiS _ (Det.cancel A E S (MvPolynomial (Fin k) S) y)) = w
  induction w with
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul s y =>
    induction y with
    | add a b ha hb => simp only [tmul_add, map_add (f := _), ha, hb]
    | tmul b z =>
      rw [Det.cancel_tmul, mul_comm]
      simp [smul_tmul', MvPolynomial.coeff_C_mul, mul_comm b]

private theorem chElt_one (S : Type) [CommRing S] [Algebra A S] {k : ℕ} (x : Fin k → E) (α : Fin k →₀ ℕ) :
    (D.baseChange S).chElt (fun i => (1 : S) ⊗ₜ[A] x i) α = (1 : S) ⊗ₜ[A] D.chElt x α := by
  rw [chElt_bc]
  have : Det.cancel A E S (MvPolynomial (Fin k) S) (Det.gen fun i => (1 : S) ⊗ₜ[A] x i) =
      Algebra.TensorProduct.map (MvPolynomial.mapAlgHom (Algebra.ofId A S)) (AlgHom.id A E)
        (Det.gen (A := A) x) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Det.gen, map_sum, Det.cancel_tmul]
  rw [this, F_map]
  unfold Det.chElt
  generalize Polynomial.aeval (Det.gen (A := A) x) (D.chiS (MvPolynomial (Fin k) A) (Det.gen x)) = w
  induction w with
  | add a b ha hb => simp only [map_add (f := _), tmul_add, ha, hb]
  | tmul s y =>
    simp [MvPolynomial.coeff_map, Algebra.ofId_apply, Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem span_mul (S : Type) [CommRing S] [Algebra A S] (I : TwoSidedIdeal E) (w : S ⊗[A] E)
    (h : w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E))) (u : S ⊗[A] E) :
    u * w ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) ∧
    w * u ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    induction u with
    | add a b ha hb => rw [add_mul, mul_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
    | tmul s e =>
      have key : ∀ t ∈ I, s ⊗ₜ[A] t ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (I : Set E)) := by
        intro t ht
        rw [← mul_one s, ← smul_eq_mul, ← smul_tmul']
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ht, rfl⟩)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact ⟨key _ (I.mul_mem_left _ _ hz), key _ (I.mul_mem_right _ _ hz)⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, mul_add]; exact ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    rw [mul_smul_comm, smul_mul_assoc]
    exact ⟨Submodule.smul_mem _ _ hx.1, Submodule.smul_mem _ _ hx.2⟩

private theorem part2 (S : Type) [CommRing S] [Algebra A S] :
    ((D.baseChange S).CH : Set (S ⊗[A] E)) =
      Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) := by
  ext w
  simp only [SetLike.mem_coe]
  constructor
  · intro h
    unfold Det.CH at h
    induction h using TwoSidedIdeal.span_induction with
    | mem x hx =>
      obtain ⟨k, x, α, rfl⟩ := hx
      rw [chElt_bc]
      exact rT_mem _ _ _ _ _ (part1 D _ _)
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | neg x _ hx => exact neg_mem hx
    | left_absorb a x _ hx => exact (span_mul S _ _ hx a).1
    | right_absorb b x _ hx => exact (span_mul S _ _ hx b).2
  · intro h
    induction h using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      change z ∈ TwoSidedIdeal.span _ at hz
      induction hz using TwoSidedIdeal.span_induction with
      | mem x hx =>
        obtain ⟨k, x, α, rfl⟩ := hx
        exact TwoSidedIdeal.subset_span ⟨k, _, α, (chElt_one D S x α).symm⟩
      | zero => simp
      | add x y _ _ hx hy => simp only [tmul_add]; exact add_mem hx hy
      | neg x _ hx => simp only [tmul_neg]; exact neg_mem hx
      | left_absorb a x _ hx =>
        have := TwoSidedIdeal.mul_mem_left _ ((1 : S) ⊗ₜ[A] a) _ hx
        simpa using this
      | right_absorb b x _ hx =>
        have := TwoSidedIdeal.mul_mem_right _ _ ((1 : S) ⊗ₜ[A] b) hx
        simpa using this
    | zero => simp
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact TwoSidedIdeal.mul_mem_left _ _ _ hx

end

theorem UpperTheory.V.CA.d_chS :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S], (∀ y : S ⊗[A] E, Polynomial.aeval y (D.chiS S y) ∈ Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E))) ∧ ((D.baseChange S).CH : Set (S ⊗[A] E)) = Submodule.span S ((fun z : E => (1 : S) ⊗ₜ[A] z) '' (D.CH : Set E)) ∧ (D.IsCH → (D.baseChange S).IsCH ∧ ∀ x : E, Polynomial.aeval x (D.chi x) = 0) := by
  intro n A E _ _ _ D S _ _
  refine ⟨part1 D S, part2 D S, fun h => ?_⟩
  have hb : ∀ (T : Type) [CommRing T] [Algebra A T],
      Submodule.span T ((fun z : E => (1 : T) ⊗ₜ[A] z) '' (D.CH : Set E)) = ⊥ := by
    intro T _ _
    rw [Submodule.span_eq_bot]
    rintro _ ⟨z, hz, rfl⟩
    rw [show D.CH = ⊥ from h] at hz
    have : z = 0 := by simpa using hz
    simp [this]
  refine ⟨?_, fun x => ?_⟩
  · refine eq_bot_iff.2 fun w hw => ?_
    have : w ∈ ((D.baseChange S).CH : Set (S ⊗[A] E)) := hw
    rw [part2, hb] at this
    simpa using this
  · have h1 := part1 D A (1 ⊗ₜ x)
    rw [hb, Submodule.mem_bot] at h1
    have h2 : D.chiS A (1 ⊗ₜ x) = D.chi x := by simp [Det.chiS, Det.chi]
    rw [h2] at h1
    have h3 := congrArg (Algebra.TensorProduct.lid A E) h1
    rw [← Polynomial.aeval_algHom_apply] at h3
    simpa using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem cl_mvps_fin {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (h : Module.Finite A (S ⧸ I)) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  classical
  have toP : ∀ K : Ideal S, Module.Finite A (S ⧸ K) →
      ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K := by
    intro K hK
    obtain ⟨T, hT⟩ := hK.fg_top
    choose l hl using fun q : S ⧸ K => Ideal.Quotient.mk_surjective q
    refine ⟨T.image l, fun s => ?_⟩
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' ((T.image l : Finset S) : Set S) = (T : Set (S ⧸ K)) := by
      ext q
      simp [hl]
    have hs : Ideal.Quotient.mk K s ∈ Submodule.map (Ideal.Quotient.mkₐ A K).toLinearMap
        (Submodule.span A ((T.image l : Finset S) : Set S)) := by
      rw [Submodule.map_span, himg, hT]
      exact Submodule.mem_top
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← Ideal.Quotient.eq]
    simpa using hts.symm
  have ofP : ∀ K : Ideal S, (∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ K) →
      Module.Finite A (S ⧸ K) := by
    rintro K ⟨F, hF⟩
    refine ⟨⟨F.image (Ideal.Quotient.mk K), ?_⟩⟩
    rw [eq_top_iff]
    rintro q -
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨t, ht, hst⟩ := hF s
    have h1 : Ideal.Quotient.mk K s = (Ideal.Quotient.mkₐ A K).toLinearMap t := by
      simpa [Ideal.Quotient.eq] using hst
    have h2 := Submodule.mem_map_of_mem (f := (Ideal.Quotient.mkₐ A K).toLinearMap) ht
    have himg : (Ideal.Quotient.mkₐ A K).toLinearMap '' (F : Set S) = ((F.image (Ideal.Quotient.mk K) : Finset (S ⧸ K)) : Set (S ⧸ K)) := by
      ext q
      simp
    rw [Submodule.map_span, himg] at h2
    rw [h1]
    exact h2
  obtain ⟨F1, hF1⟩ := toP I h
  have hpow : ∀ n : ℕ, ∃ F : Finset S, ∀ s : S, ∃ t ∈ Submodule.span A (F : Set S), s - t ∈ I ^ n := by
    intro n
    induction n with
    | zero => exact ⟨∅, fun s => ⟨0, Submodule.zero_mem _, by simp⟩⟩
    | succ n ih =>
      obtain ⟨Fn, hFn⟩ := ih
      obtain ⟨G, hG⟩ := (IsNoetherian.noetherian (I ^ n) : (I ^ n).FG)
      refine ⟨Fn ∪ (F1 ×ˢ G).image (fun p => p.1 * p.2), fun s => ?_⟩
      obtain ⟨t, ht, hst⟩ := hFn s
      rw [← hG, Submodule.mem_span_finset] at hst
      obtain ⟨c, -, hc⟩ := hst
      choose u hu hcu using fun g => hF1 (c g)
      refine ⟨t + ∑ g ∈ G, u g * g, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.span_mono ?_ ht) (Submodule.sum_mem _ fun g hg => ?_)
        · exact Finset.coe_subset.mpr Finset.subset_union_left
        · have h3 := Submodule.mem_map_of_mem (f := LinearMap.mulRight A g) (hu g)
          rw [Submodule.map_span] at h3
          refine Submodule.span_mono ?_ h3
          rintro _ ⟨f, hf, rfl⟩
          rw [Finset.coe_union, Finset.coe_image]
          right
          exact ⟨(f, g), Finset.mem_product.mpr ⟨hf, hg⟩, by simp⟩
      · have hct : s - t = ∑ g ∈ G, c g * g := by
          rw [← hc]
          simp [smul_eq_mul]
        have he : s - (t + ∑ g ∈ G, u g * g) = ∑ g ∈ G, (c g - u g) * g := by
          calc s - (t + ∑ g ∈ G, u g * g) = (s - t) - ∑ g ∈ G, u g * g := by ring
            _ = ∑ g ∈ G, c g * g - ∑ g ∈ G, u g * g := by rw [hct]
            _ = ∑ g ∈ G, (c g - u g) * g := by
              rw [← Finset.sum_sub_distrib]
              simp [sub_mul]
        rw [he, pow_succ']
        refine Ideal.sum_mem _ fun g hg => Ideal.mul_mem_mul (hcu g) ?_
        rw [← hG]
        exact Submodule.subset_span hg
  obtain ⟨F, hF⟩ := hpow N
  exact ofP J ⟨F, fun s => (hF s).imp fun t ⟨ht, hst⟩ => ⟨ht, hN hst⟩⟩

private theorem cl_mvps_max {O σ : Type} [CommRing O] [IsLocalRing O] (g : MvPowerSeries σ O) :
    g ∈ maximalIdeal (MvPowerSeries σ O) ↔ MvPowerSeries.constantCoeff g ∈ maximalIdeal O := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

theorem UpperTheory.V.CA.cl_mvps :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → ∀ (σ : Type) [Finite σ] (a : σ → R), (∀ s, a s ∈ maximalIdeal R) → maximalIdeal R ≤ (Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R)).radical → ∃ φ : MvPowerSeries σ O →ₐ[O] R, (∀ s, φ (MvPowerSeries.X s) = a s) ∧ φ.toRingHom.Finite ∧ IsLocalHom φ := by
  intro O _ _ _ _ R _ _ _ hR σ _ a ha hrad
  haveI := hR.noeth
  haveI := hR.complete
  haveI := hR.isLocalHom
  let φ : MvPowerSeries σ O →ₐ[O] R := GlobalTheory.mvEvalAdic O (maximalIdeal R) a ha
  have hX : ∀ s, φ (MvPowerSeries.X s) = a s := GlobalTheory.mvEvalAdic_X _ a ha
  have hXm : ∀ s, φ (MvPowerSeries.X s) ∈ maximalIdeal R := fun s => (hX s).symm ▸ ha s
  refine ⟨φ, hX, ?_, ?_⟩
  · letI : Algebra (MvPowerSeries σ O) R := φ.toRingHom.toAlgebra
    show Module.Finite (MvPowerSeries σ O) R
    haveI hOO : IsCO O O := ⟨inferInstance, ⟨fun x hx => by simpa using hx⟩, fun x => ⟨x, by simp⟩⟩
    haveI hCO := co_mvps O O σ
    haveI := hCO.complete
    haveI : IsScalarTower O (MvPowerSeries σ O) R :=
      IsScalarTower.of_algebraMap_eq (fun c => (φ.commutes c).symm)
    have hJ : Ideal.span (Set.range a) ⊔ (maximalIdeal O).map (algebraMap O R) ≤
        (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) := by
      refine sup_le ?_ ?_
      · rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        rw [← hX s]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max]
        simp
      · rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, ← φ.commutes c]
        refine Ideal.mem_map_of_mem (algebraMap (MvPowerSeries σ O) R) ?_
        rw [cl_mvps_max, MvPowerSeries.algebraMap_apply]
        simpa using hc
    have hJm : (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R) ≤ maximalIdeal R := by
      rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap]
      rw [cl_mvps_max] at hg
      have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => ((IsLocalRing.mem_maximalIdeal _).mp hg) (isUnit_of_map_unit (algebraMap O R) _ hu)
      have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
      have h3 := Ideal.add_mem _ h2 h1
      have h4 : φ g ∈ maximalIdeal R := by simpa using h3
      exact h4
    haveI : IsHausdorff ((maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) R :=
      IsHausdorff.of_isLocalRing _ R (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm)
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
      (hrad.trans (Ideal.radical_mono hJ)) (IsNoetherian.noetherian (maximalIdeal R))
    haveI : Module.Finite O (R ⧸ maximalIdeal R) := hR.res_fin
    haveI : Module.Finite (MvPowerSeries σ O) (R ⧸ maximalIdeal R) :=
      Module.Finite.of_restrictScalars_finite O _ _
    haveI : Module.Finite (MvPowerSeries σ O)
        (R ⧸ (maximalIdeal (MvPowerSeries σ O)).map (algebraMap (MvPowerSeries σ O) R)) :=
      cl_mvps_fin (A := MvPowerSeries σ O) inferInstance hN
    exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal (MvPowerSeries σ O))
  · constructor
    intro g hg
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    by_contra hc
    have h1 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hc (isUnit_of_map_unit (algebraMap O R) _ hu)
    have h2 := GlobalTheory.algHom_sub_constantCoeff_mem φ (K := maximalIdeal R) hXm g
    have h3 : φ g ∈ maximalIdeal R := by simpa using Ideal.add_mem _ h2 h1
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FChars
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private noncomputable def piB {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] : MonoidAlgebra B G →ₐ[B] (Fin n → B) :=
  MonoidAlgebra.lift B (Fin n → B) G
    { toFun := fun g i => algebraMap k B (χ i g)
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp }

private theorem piB_single {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (g : G) (b : B) (i : Fin n) :
    piB χ B (MonoidAlgebra.single g b) i = b * algebraMap k B (χ i g) := by
  simp [piB]

private theorem piB_map {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (y : MonoidAlgebra k G) (i : Fin n) :
    piB χ B (MonoidAlgebra.mapRingHom G (algebraMap k B) y) i = algebraMap k B (piB χ k y i) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
  | single g r => rw [MonoidAlgebra.mapRingHom_single, piB_single, piB_single]; simp

private theorem D_eq {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ)
    (B : Type) [CommRing B] [Algebra k B] (x : MonoidAlgebra B G) :
    (GDet.ofChars χ).D B x = ∏ i, piB χ B x i := by
  change (GDet.repAlg (GDet.diagRep χ) B x).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [Pi.zero_def]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, Matrix.diagonal_add]; rfl
  | single g r =>
    ext i j
    by_cases h : i = j
    · subst h; simp [GDet.repAlg, GDet.diagRep, piB_single]
    · simp [GDet.repAlg, GDet.diagRep, Matrix.diagonal_apply_ne _ h]

theorem UpperTheory.V.CA.f_chars :
    ∀ {n : ℕ} {k G : Type} [Field k] [Group G] (χ : Fin n → G →* kˣ), Function.Injective χ → ∃ π : MonoidAlgebra k G →ₐ[k] (Fin n → k), Function.Surjective π ∧ (∀ g i, π (MonoidAlgebra.single g 1) i = χ i g) ∧ (∀ y, (GDet.ofChars χ).Kills y ↔ π y = 0) ∧ ∀ y, (GDet.ofChars χ).chi y = ∏ i, (X - C (π y i)) := by
  intro n k G _ _ χ hχ
  have hs : ∀ g i, piB χ k (MonoidAlgebra.single g 1) i = χ i g := fun g i => by simp [piB_single]
  have hsurj : Function.Surjective (piB χ k) := by
    have hinj : Function.Injective fun i => (Units.coeHom k).comp (χ i) := fun i j h =>
      hχ (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
    have hli : LinearIndependent k fun i (g : G) => (χ i g : k) :=
      (linearIndependent_monoidHom G k).comp _ hinj
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range (piB χ k).toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, funext (hs g)⟩
    exact LinearMap.range_eq_top.1 this
  refine ⟨piB χ k, hsurj, hs, fun y => ⟨fun h => ?_, fun h B _ _ z => ?_⟩, fun y => ?_⟩
  · ext i
    by_contra hi
    obtain ⟨z, hz⟩ := hsurj fun _ => -(piB χ k y i)⁻¹
    have := h k z
    rw [D_eq, Finset.prod_eq_zero (Finset.mem_univ i)] at this
    · exact zero_ne_one this
    · rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, hz]
      have hi' : piB χ k y i ≠ 0 := hi
      simp [hi']
  · rw [D_eq]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [map_add (f := _), map_mul, map_one, Pi.add_apply, Pi.mul_apply, piB_map, h]
    simp
  · unfold GDet.chi
    rw [D_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, Pi.sub_apply, piB_single]
    have := piB_map χ k[X] y i
    rw [Polynomial.algebraMap_eq] at this
    rw [this]
    simp
end

