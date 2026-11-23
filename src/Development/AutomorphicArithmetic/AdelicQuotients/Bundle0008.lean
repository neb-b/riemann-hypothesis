module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0005
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdeleBaseChangeLocalIsClosedEmbedding
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal Topology Filter

private theorem ce_of_comp {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y]
    {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) (h : IsClosedEmbedding (g ∘ f)) :
    IsClosedEmbedding f :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap hf (Function.Injective.of_comp h.injective)
    (isProperMap_of_comp_of_t2 hf hg h.isProperMap).isClosedMap

private theorem ce_reindex {V : Type*} {A : V → Type*} [∀ v, TopologicalSpace (A v)] (φ : V → V) (h : ∀ v, φ v = v) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => x (φ v)) := by
  obtain rfl : φ = id := funext h
  exact (Homeomorph.refl _).isClosedEmbedding

private theorem ce_piMap {V : Type*} {A B : V → Type*} [∀ v, TopologicalSpace (A v)] [∀ v, TopologicalSpace (B v)]
    (ι : ∀ v, A v → B v) (h : ∀ v, IsClosedEmbedding (ι v)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (v : V) => ι v (x v)) :=
  IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_pi fun v => (h v).continuous.comp (continuous_apply v))
    (fun _ _ e => funext fun v => (h v).injective (congrFun e v))
    (IsProperMap.pi_map fun v => (h v).isProperMap).isClosedMap

private theorem ce_pi {V W : Type*} (c : W → V) (hc : Function.Surjective c) {A : V → Type*} {B : W → Type*}
    [∀ v, TopologicalSpace (A v)] [∀ w, TopologicalSpace (B w)] [∀ w, T2Space (B w)]
    (ι : ∀ w, A (c w) → B w) (h : ∀ w, IsClosedEmbedding (ι w)) :
    IsClosedEmbedding (fun (x : ∀ v, A v) (w : W) => ι w (x (c w))) := by
  choose s hs using hc
  refine ce_of_comp (g := fun (y : ∀ w, B w) (v : V) => y (s v))
    (continuous_pi fun w => (h w).continuous.comp (continuous_apply _))
    (continuous_pi fun v => continuous_apply _) ?_
  exact (ce_piMap (fun v => ι (s v)) fun v => h (s v)).comp (ce_reindex (A := A) (fun v => c (s v)) hs)

private theorem ce_gl {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    [IsTopologicalRing R] [IsTopologicalRing S] [T2Space R] [T2Space S] (n : ℕ) (f : R →+* S) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (mapGL n f) := by
  have h1 : IsClosedEmbedding (fun (x : Fin n → R) (j : Fin n) => f (x j)) := ce_piMap (fun _ => f) fun _ => hf
  have hM : IsClosedEmbedding (f.mapMatrix.toMonoidHom : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) S) :=
    ce_piMap (fun _ => fun (x : Fin n → R) (j : Fin n) => f (x j)) fun _ => h1
  exact @IsClosedEmbedding.units_map (Matrix (Fin n) (Fin n) R) (Matrix (Fin n) (Fin n) S)
    _ _ _ _ _ _ f.mapMatrix.toMonoidHom hM

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem exists_small (v : HeightOneSpectrum (𝓞 F)) (g : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ a : v.adicCompletion F, a ≠ 0 ∧ Valued.v a < (g : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have h1 : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    simpa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hπ
  have h2 : Valued.v (algebraMap F (v.adicCompletion F) π) < 1 := by
    rw [h1, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  obtain ⟨k, hk⟩ := exists_pow_lt₀ h2 g
  refine ⟨algebraMap F (v.adicCompletion F) π ^ k, pow_ne_zero _ ?_, by rwa [map_pow]⟩
  intro h0
  rw [h0, map_zero] at h1
  exact (WithZero.exp_ne_zero) h1.symm

private theorem ce_compl (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] :
    IsClosedEmbedding (completionMap v w) := by
  have he0 : w.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.asIdeal).ne'
  have hind : IsInducing (completionMap v w) := by
    rw [IsTopologicalAddGroup.isInducing_iff_nhds_zero]
    refine le_antisymm ?_ ?_
    · have := (continuous_completionMap v w).tendsto 0
      rw [map_zero] at this
      exact this.le_comap
    · intro s hs
      obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
      let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
      let emb : ν.ValueGroup₀ →*₀ WithZero (Multiplicative ℤ) :=
        MonoidWithZeroHom.ValueGroup₀.embedding (f := ν.toMonoidWithZeroHom)
      obtain ⟨a, ha0, ha⟩ := exists_small v (Units.map emb.toMonoidHom γ)
      have hfa : completionMap v w a ≠ 0 := (map_ne_zero_iff _ (completionMap v w).injective).2 ha0
      have hopen := Valued.isOpen_ball (w.adicCompletion E) ((Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a))
      have hmem : (0 : w.adicCompletion E) ∈ {x | (Valued.v : Valuation (w.adicCompletion E) _).restrict x < (Valued.v : Valuation (w.adicCompletion E) _).restrict (completionMap v w a)} := by
        simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff, map_zero]
        exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hfa)
      refine Filter.mem_comap.2 ⟨_, hopen.mem_nhds hmem, fun x hx => hγ ?_⟩
      have h1 : Valued.v (completionMap v w x) < Valued.v (completionMap v w a) := by
        simpa [Valuation.restrict_lt_iff] using hx
      rw [valued_completionMap, valued_completionMap] at h1
      have h2 := lt_of_pow_lt_pow_left₀ _ zero_le h1
      rw [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      exact h2.trans ha
  have hu : IsUniformInducing (completionMap v w) := AddMonoidHom.isUniformInducing_of_isInducing hind
  exact (IsUniformEmbedding.mk hu (completionMap v w).injective).isClosedEmbedding

omit [NumberField F] [NumberField E] in
private theorem ce_infComp (v : InfinitePlace F) (w : InfinitePlace E) [w.LiesOver v] :
    IsClosedEmbedding (AbsoluteValue.Completion.map v.1 w.1) :=
  (AbsoluteValue.Completion.isometry_map v.1 w.1).isClosedEmbedding

private theorem ce_incFin (v : HeightOneSpectrum (𝓞 F)) : IsClosedEmbedding (incFin E v) := by
  obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := 𝓞 E) v.asIdeal
  let w : PlacesOver E v := (placesOverEquiv E v).symm P
  exact ce_of_comp (g := fun y : CompletionsOver E v => y w)
    (continuous_pi fun u => continuous_completionMap v u.1) (continuous_apply w) (ce_compl v w.1)

open scoped NumberField.LiesOver in
private theorem ce_infMap : IsClosedEmbedding (infMap F E) := by
  have hs : Function.Surjective (fun w : InfinitePlace E => w.comap (algebraMap F E)) := InfinitePlace.comap_surjective
  have hmap : (infMap F E : InfiniteAdeleRing F → InfiniteAdeleRing E) =
      fun (x : InfiniteAdeleRing F) (w : InfinitePlace E) =>
        AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1 (x (w.comap (algebraMap F E))) := by
    funext x w
    exact (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w).trans
      (AbsoluteValue.Completion.algebraMap_apply_of_liesOver (w.comap (algebraMap F E)).1 w.1 _)
  rw [hmap]
  exact ce_pi (A := fun v : InfinitePlace F => v.Completion) (B := fun w : InfinitePlace E => w.Completion)
    (fun w : InfinitePlace E => w.comap (algebraMap F E)) hs
    (fun w => AbsoluteValue.Completion.map (w.comap (algebraMap F E)).1 w.1) fun w => ce_infComp _ w
end

theorem UpperTheory.adele_baseChange_local_isClosedEmbedding :
    LocEmb := by
  intro F E _ _ _ _ _ n
  exact ⟨ce_gl n _ ce_infMap, fun v => ce_gl n _ (ce_incFin v)⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionBaseChangeCompat
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped NumberField.AdeleRing TensorProduct

open PositivityTheory.Rg.Tf.Loc

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul' {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_fst (l : E) (x : 𝔸[F]) :
    (adeleTensorEquiv F E (l ⊗ₜ x)).1 =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) (l ⊗ₜ x.1) := by
  rw [adeleTensorEquiv_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
  rfl

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem gal_fst (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : (galAd σ a).1 = galInf σ a.1 := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_fst, tensor_fst, galInf, galOf_tmul']
  | add s t hs ht =>
    rw [map_add (f := _), map_add (f := _)]
    change ((galAd σ) _).1 + ((galAd σ) _).1 = galInf σ (_ + _)
    rw [map_add (f := _), hs, ht]

private theorem gal_atFin (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    rw [galAd, galOf_tmul', tensor_atFin, tensor_atFin, galFin, galOf_tmul']
  | add s t hs ht =>
    simp only [map_add (f := _), hs, ht]

private theorem adele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem gal_adele (σ : E ≃ₐ[F] E) (a : 𝔸[F]) : galAd σ (adeleMap F E a) = adeleMap F E a := by
  have h : adeleMap F E a = adeleTensorEquiv F E ((1 : E) ⊗ₜ a) := by
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h, galAd, galOf_tmul', map_one]

private theorem gal_inf (σ : E ≃ₐ[F] E) (x : InfiniteAdeleRing F) :
    galInf σ (infMap F E x) = infMap F E x := by
  have h : infMap F E x =
      GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ x) := by
    rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
  rw [h, galInf, galOf_tmul', map_one]

private theorem gal_algebraMap (σ : E ≃ₐ[F] E) (l : E) :
    galAd σ (algebraMap E 𝔸[E] l) = algebraMap E 𝔸[E] (σ l) := by
  have h (m : E) : algebraMap E 𝔸[E] m = adeleTensorEquiv F E (m ⊗ₜ (1 : 𝔸[F])) := by
    rw [adeleTensorEquiv_tmul, map_one, mul_one]
  rw [h l, galAd, galOf_tmul', ← h]

private theorem mapGL_square {A B C D : Type*} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (n : ℕ) (f : A →+* B) (g : B →+* D) (h : A →+* C) (k : C →+* D) (H : ∀ a, g (f a) = k (h a))
    (x : GL (Fin n) A) : mapGL n g (mapGL n f x) = mapGL n k (mapGL n h x) :=
  Units.ext (by ext i j; simpa using H _)

end

theorem UpperTheory.adele_galois_action_baseChange_compat :
    Compat := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun g => ?_, fun v g => ?_, fun g => ?_, fun v g => ?_, fun g => ?_, fun g => ?_, fun δ => ?_, fun γ => ?_⟩
  · exact mapGL_square n _ _ _ _ (gal_fst σ) g
  · exact mapGL_square n _ _ _ _ (gal_atFin σ v) g
  · exact mapGL_square n _ _ _ _ (fun _ => rfl) g
  · refine Units.ext (Matrix.ext fun i j => ?_)
    change atFin v (adeleMap F E ((g : Matrix (Fin n) (Fin n) 𝔸[F]) i j)) = incFin E v ((finAt v g : Matrix (Fin n) (Fin n) _) i j)
    rw [finAt_apply]
    exact adele_atFin v _
  · refine Units.ext ?_
    ext i j
    simpa using gal_adele σ _
  · refine Units.ext ?_
    ext i j
    simpa using gal_inf σ _
  · refine Units.ext ?_
    ext i j
    exact gal_algebraMap σ ((δ : Matrix (Fin n) (Fin n) E) i j)
  · refine Units.ext ?_
    ext i j
    exact adeleMap_algebraMap (K := F) (L := E) ((γ : Matrix (Fin n) (Fin n) F) i j)
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdeleGaloisActionContinuous
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct NumberField.AdeleRing

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_cont {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B] (e : E ⊗[F] A ≃ₐ[E] B)
    (σ : E ≃ₐ[F] E) {ι : Type*} [Fintype ι] (b : ι → E) (c : ι → B → A)
    (hc : ∀ i, Continuous (c i)) (hs : ∀ y, e.symm y = ∑ i, b i ⊗ₜ[F] c i y)
    (hm : Continuous fun a : A => e (1 ⊗ₜ a)) : Continuous (galOf e σ) := by
  have h : ∀ y, galOf e σ y = ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := by
    intro y
    change e (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F A) (e.symm y)) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have h' : (galOf e σ : B → B) = fun y => ∑ i, e (σ (b i) ⊗ₜ 1) * e (1 ⊗ₜ c i y) := funext h
  rw [h']
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (hm.comp (hc i))

private theorem galAd_cont (σ : E ≃ₐ[F] E) : Continuous (galAd σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (adeleTensorEquiv F E) σ (Module.finBasis F E) (coord (Module.finBasis F E))
    (continuous_coord _) (adeleTensorEquiv_symm_apply _) ?_
  have h : (fun a : 𝔸[F] => adeleTensorEquiv F E ((1 : E) ⊗ₜ a)) = adeleMap F E := by
    funext a
    rw [adeleTensorEquiv_tmul, map_one, one_mul]
  rw [h]
  exact continuous_adeleMap

private theorem galInf_cont (σ : E ≃ₐ[F] E) : Continuous (galInf σ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine galOf_cont (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)) σ
    (Module.finBasis F E) (GroundTheory.Global.InfinitePlace.adeleCoord (Module.finBasis F E))
    (GroundTheory.Global.InfinitePlace.continuous_adeleCoord _) (fun y => ?_) ?_
  · rw [AlgEquiv.symm_apply_eq]
    exact (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord _ y).symm
  · have h : (fun a : InfiniteAdeleRing F =>
        GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E) ((1 : E) ⊗ₜ a)) =
        GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) := by
      funext a
      rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one, one_mul]
    rw [h]
    exact GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap

private theorem galFin_mul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F)
    (y : CompletionsOver E v) :
    galFin σ v (algebraMap (v.adicCompletion F) (CompletionsOver E v) a * y) =
      algebraMap (v.adicCompletion F) (CompletionsOver E v) a * galFin σ v y := by
  obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
  rw [← tensorEquiv'_tmul_mul]
  change tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v ((1 ⊗ₜ a) * t)))) =
    _ * tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F _)
      ((tensorEquiv' E v).symm (tensorEquiv' E v t)))
  rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, ← tensorEquiv'_tmul_mul, map_mul,
    Algebra.TensorProduct.map_tmul]
  simp

private theorem galFin_cont (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (galFin σ v) := by
  let L : CompletionsOver E v →ₗ[v.adicCompletion F] CompletionsOver E v :=
    { toFun := galFin σ v
      map_add' := map_add _
      map_smul' := fun a y => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        exact galFin_mul σ v a y }
  exact IsModuleTopology.continuous_of_linearMap L

private theorem mapGL_cont {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (n : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (mapGL n f) :=
  Continuous.units_map _ (continuous_id.matrix_map hf)

end

theorem UpperTheory.adele_galois_action_continuous :
    Compat → RPE → GalCont := by
  intro _ _ F E _ _ _ _ _ σ n
  exact ⟨mapGL_cont n _ (galAd_cont σ), mapGL_cont n _ (galInf_cont σ),
    fun v => mapGL_cont n _ (galFin_cont σ v)⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdelicBoundOfCentralizerLocalization
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace UpperTheory.Bnd

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

private def emb : GL (Fin n) (InfiniteAdeleRing E) →* GA E n where
  toFun x := (AdelicGLn.prodEquiv E n).symm (x, 1)
  map_one' := map_one (AdelicGLn.prodEquiv E n).symm
  map_mul' x y := by
    rw [← map_mul (AdelicGLn.prodEquiv E n).symm]
    simp

private theorem emb_apply (x : GL (Fin n) (InfiniteAdeleRing E)) :
    emb E n x = (AdelicGLn.prodEquiv E n).symm (x, 1) := rfl

private theorem continuous_emb : Continuous (emb E n) :=
  (AdelicGLn.prodEquiv E n).symm.continuous.comp (continuous_id.prodMk continuous_const)

private theorem prod_emb (x : GL (Fin n) (InfiniteAdeleRing E)) :
    AdelicGLn.prodEquiv E n (emb E n x) = (x, 1) := by
  rw [emb_apply]; exact (AdelicGLn.prodEquiv E n).apply_symm_apply _

private theorem pI_emb (x : GL (Fin n) (InfiniteAdeleRing E)) : pI E n (emb E n x) = x := by
  refine Units.ext ?_
  ext a b
  have h := AdelicGLn.prodEquiv_apply_fst E n (emb E n x) a b
  rw [prod_emb] at h
  exact h.symm

private theorem pE_emb {F : Type} [Field F] [NumberField F] [Algebra F E] (v : Pl F)
    (x : GL (Fin n) (InfiniteAdeleRing E)) : pE E n v (emb E n x) = 1 := by
  refine Units.ext (Matrix.ext fun a b => funext fun w => ?_)
  have h := AdelicGLn.prodEquiv_apply_snd E n (emb E n x) a b
  rw [prod_emb] at h
  change (((emb E n x : GL _ _) a b).2 : FiniteAdeleRing (𝓞 E) E) w.1 = _
  rw [← h]
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> rfl

end UpperTheory.Bnd

open UpperTheory.Bnd in
theorem UpperTheory.adelicBound_of_centralizer_localization :
    N5 → Compat → CentLoc → RPE → BoundE := by
  intro hN hC hCL hR F E _ _ _ _ _ _ σ hσ n hn δ D hD
  have hRP := hR F E n
  obtain ⟨hC1, hC2, -⟩ := hC F E σ n

  have hz : ∀ s : ℝ, emb E n (pI E n (zA E n s)) = zA E n s := fun s =>
    hRP.ext _ _ (pI_emb E n _) fun v => by
      rw [pE_emb E n v]
      exact ((hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v).symm

  have hg : ∀ x, emb E n (mapGL n (galInf σ) x) = mapGL n (galAd σ) (emb E n x) := fun x =>
    hRP.ext _ _ (by rw [pI_emb, hC1, pI_emb]) fun v => by
      rw [pE_emb E n v, hC2, pE_emb E n v, map_one]
  have hm := (hN F E σ hσ n hn).2.2
  set d : GL (Fin n) (InfiniteAdeleRing E) →* {r : ℝ // 0 < r} := (detModule E n).comp (emb E n) with hd
  have hdc : Continuous fun y => (d y : ℝ) :=
    continuous_subtype_val.comp (continuous_detModule.comp (continuous_emb E n))
  have hdz : ∀ s : ℝ, (d (pI E n (zA E n s)) : ℝ) = Real.exp s := fun s => by
    simp only [hd, MonoidHom.comp_apply, hz]
    rw [zA, detModule_centralSection hn]
  have hds : ∀ x, d (mapGL n (galInf σ) x) = d x := fun x => by
    simp only [hd, MonoidHom.comp_apply, hg, hm]
  have hp : ∀ y, (d y : ℝ) ≠ 0 := fun y => (d y).2.ne'
  have hcont : Continuous fun y => Real.log ((d y : ℝ) / (d δ : ℝ)) :=
    (hdc.div_const _).log fun y => div_ne_zero (hp y) (hp δ)
  refine ⟨(fun y => Real.log ((d y : ℝ) / (d δ : ℝ))) '' D, hD.image hcont, fun s x hx => ⟨_, hx, ?_⟩⟩
  have e : d (pI E n (zA E n s) * (x⁻¹ * δ * mapGL n (galInf σ) x)) = d (pI E n (zA E n s)) * d δ := by
    rw [map_mul, map_mul, map_mul, hds, map_inv]
    congr 1
    rw [mul_comm (d x)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  change Real.log ((d _ : ℝ) / (d δ : ℝ)) = s
  rw [e, Positive.val_mul, hdz, mul_div_cancel_right₀ _ (hp δ), Real.log_exp]
end
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdicCompletionIntegersBaseChangeIff
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal GroundTheory.Automorphic ValuativeRel

private theorem mem_integers_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : x ∈ 𝒪[v.adicCompletion K] ↔ Valued.v x ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion K)) Valued.v).le_one_iff_le_one

private theorem completionMap_mem_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E v) (x : v.adicCompletion F) :
    completionMap v w.1 x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := by
  rw [mem_integers_iff, mem_integers_iff, valued_completionMap]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'

theorem UpperTheory.adicCompletion_integers_baseChange_iff :
    UnitIff := by
  intro F E _ _ _ _ _ n v t
  have key : ∀ w : PlacesOver E v,
      mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) t) ∈
        GLnLocal.integralGL (w.1.adicCompletion E) n ↔ t ∈ KF F n v := by
    intro w
    have hc : ∀ s : GL (Fin n) (v.adicCompletion F),
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) (mapGL n (incFin E v) s) =
          mapGL n (completionMap v w.1) s := fun s => Units.ext (Matrix.ext fun i j => rfl)
    rw [hc, GLnLocal.mem_integralGL_iff, GLnLocal.mem_integralGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => completionMap_mem_iff v w _)
      (forall₂_congr fun i j => completionMap_mem_iff v w _)
  constructor
  · intro h
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    let w : PlacesOver E v := ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv⟩
    exact (key w).1 (h w)
  · intro h w
    exact (key w).2 h
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.BaseChangeTrivialExtension
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped TensorProduct

private theorem galOf_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B] (e : E ⊗[F] A ≃ₐ[E] B) :
    galOf e (1 : E ≃ₐ[F] E) = RingHom.id _ := by
  ext x
  have h : Algebra.TensorProduct.map (((1 : E ≃ₐ[F] E) : E →ₐ[F] E)) (AlgHom.id F A) = AlgHom.id F _ := by
    ext <;> simp
  simp only [galOf, RingHom.comp_apply, h]
  simp

private theorem infMap_self (F : Type) [Field F] [NumberField F] : infMap F F = RingHom.id _ := by
  have hd := InfiniteAdeleRing.denseRange_algebraMap F
  have h1 : Continuous (infMap F F) := InfinitePlace.continuous_infiniteAdeleRingMap
  have := hd.equalizer h1 continuous_id (funext fun k => by
    simpa using InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := F) k)
  exact RingHom.ext fun x => congrFun this x

private theorem incFin_bij (F : Type) [Field F] [NumberField F] (v : Pl F) : Function.Bijective (incFin F v) := by
  have h : ∀ x, incFin F v x = tensorEquiv' F v ((1 : F) ⊗ₜ[F] x) := by
    intro x
    rw [tensorEquiv'_tmul, map_one, one_mul]
    rfl
  have hb : Function.Bijective (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) :=
    (TensorProduct.lid F (v.adicCompletion F)).symm.bijective
  have : (incFin F v : _ → _) = tensorEquiv' F v ∘ (fun x : v.adicCompletion F => (1 : F) ⊗ₜ[F] x) := funext h
  rw [this]
  exact (tensorEquiv' F v).bijective.comp hb

theorem UpperTheory.baseChange_trivial_extension :
    Triv := by
  intro F _ _
  refine ⟨galOf_one' _, infMap_self F, fun v => ⟨galOf_one' _, incFin_bij F v⟩⟩
end

