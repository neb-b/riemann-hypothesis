module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.SplitEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLSplitEquiv
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.adelicGL_split_equiv :
    SplitEquiv := by
  intro G₁ R G _ _ _ _ _ _ _ i d c hi hd hc hs hcomm hk
  have hd1 : ∀ x, d (i x) = 1 := fun x => (hk _).2 ⟨x, rfl⟩
  have h : ∀ g, ∃ x, i x = g * (c (d g))⁻¹ := fun g => by
    have h1 : d (g * (c (d g))⁻¹) = 1 := by
      rw [map_mul, map_inv, hs, mul_inv_cancel]
    exact (hk _).1 h1
  choose f hf using h
  have hfc : Continuous f := by
    refine hi.continuous_iff.2 ?_
    have h2 : (i ∘ f) = fun g => g * (c (d g))⁻¹ := funext hf
    rw [h2]
    exact continuous_id.mul (hc.comp hd).inv
  let E : G₁ × R ≃* G :=
    { toFun := fun x => i x.1 * c x.2
      invFun := fun g => (f g, d g)
      left_inv := by
        rintro ⟨x, r⟩
        have hdr : d (i x * c r) = r := by rw [map_mul, hd1, hs, one_mul]
        refine Prod.ext (hi.injective ?_) hdr
        show i (f (i x * c r)) = i x
        rw [hf, hdr, mul_inv_cancel_right]
      right_inv := by
        intro g
        show i (f g) * c (d g) = g
        rw [hf, inv_mul_cancel_right]
      map_mul' := by
        rintro ⟨x, r⟩ ⟨y, s⟩
        show i (x * y) * c (r * s) = i x * c r * (i y * c s)
        rw [map_mul, map_mul, mul_assoc (i x) (c r), ← mul_assoc (c r), hcomm r (i y)]
        simp only [mul_assoc] }
  exact ⟨{ E with
    continuous_toFun := (hi.continuous.comp continuous_fst).mul (hc.comp continuous_snd)
    continuous_invFun := hfc.prodMk hd }, fun x => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem coord_comm {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (φ : R →ₗ[F] F) (s : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s) :
    Commute (s.map φ) γ := by
  have hl : ∀ (r : R) (x : F), φ (r * algebraMap F R x) = φ r * x := by
    intro r x
    rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  have hr : ∀ (r : R) (x : F), φ (algebraMap F R x * r) = x * φ r := by
    intro r x
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  show s.map φ * γ = γ * s.map φ
  ext a c
  have h := congrArg φ (congrFun (congrFun hs a) c)
  set_option synthInstance.maxHeartbeats 100000 in
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, hl, hr] using h

private theorem coord_sum {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (b : Module.Basis ι F R) (B : Finset ι) (s : Matrix (Fin n) (Fin n) R)
    (hB : ∀ a c, (b.repr (s a c)).support ⊆ B) :
    s = ∑ i ∈ B, b i • (s.map (b.coord i)).map (algebraMap F R) := by
  ext a c
  rw [Matrix.sum_apply]
  conv_lhs => rw [← b.linearCombination_repr (s a c)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_of_support_subset _ (hB a c) _ (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

private theorem sum_comm_of {F R ι : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (e : ι → R) (B : Finset ι) (S T : ι → Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, S i * T j = T j * S i) :
    (∑ i ∈ B, e i • (S i).map (algebraMap F R)) * (∑ j ∈ B, e j • (T j).map (algebraMap F R)) =
      (∑ j ∈ B, e j • (T j).map (algebraMap F R)) * (∑ i ∈ B, e i • (S i).map (algebraMap F R)) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (e i), ← Matrix.map_mul, ← Matrix.map_mul, h]

private theorem comm_alg {F R : Type} [Field F] [CommRing R] [Algebra F R] {n : ℕ}
    (γ : Matrix (Fin n) (Fin n) F) (hγ : γ.charpoly.Separable) (s t : Matrix (Fin n) (Fin n) R)
    (hs : s * γ.map (algebraMap F R) = γ.map (algebraMap F R) * s)
    (ht : t * γ.map (algebraMap F R) = γ.map (algebraMap F R) * t) : s * t = t * s := by
  classical
  let b := Module.Basis.ofVectorSpace F R
  let B := Finset.univ.biUnion fun a => Finset.univ.biUnion fun c =>
    (b.repr (s a c)).support ∪ (b.repr (t a c)).support
  have hsB : ∀ a c, (b.repr (s a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_left _ hi⟩⟩
  have htB : ∀ a c, (b.repr (t a c)).support ⊆ B := fun a c i hi =>
    Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _,
      Finset.mem_union_right _ hi⟩⟩
  have h := sum_comm_of (R := R) (fun i => b i) B (fun i => s.map (b.coord i))
    (fun i => t.map (b.coord i)) fun i j =>
      (UpperTheory.V.Z.Tf.Orb.centComm F n γ _ _ hγ (coord_comm γ _ s hs) (coord_comm γ _ t ht)).eq
  rwa [← coord_sum b B s hsB, ← coord_sum b B t htB] at h

theorem UpperTheory.centralizer_commutative_of_separable_charpoly :
    CentComm := by
  intro F R _ _ _ f n γ hγ s t hs ht
  letI : Algebra F R := f.toAlgebra
  exact comm_alg γ hγ s t hs ht
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CharpolySeparableUnitSmul
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Polynomial

private theorem charpoly_unit_smul {R : Type} [CommRing R] {n : ℕ} (r : Rˣ)
    (M : Matrix (Fin n) (Fin n) R) :
    ((r : R) • M).charpoly =
      C ((r : R) ^ n) * M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) := by
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  have hmat : Matrix.charmatrix ((r : R) • M) =
      (C (r : R) : R[X]) • (Matrix.charmatrix M).map
        (compRingHom (C ((r⁻¹ : Rˣ) : R) * X)) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [Matrix.charmatrix_apply_eq, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        coe_compRingHom_apply, sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, hc, one_mul,
        ← C_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ h, Matrix.smul_apply, Matrix.map_apply,
        smul_eq_mul, coe_compRingHom_apply, neg_comp, C_comp, mul_neg, ← C_mul]
  have hdet : M.charpoly.comp (C ((r⁻¹ : Rˣ) : R) * X) =
      ((Matrix.charmatrix M).map (compRingHom (C ((r⁻¹ : Rˣ) : R) * X))).det := by
    rw [Matrix.charpoly, ← coe_compRingHom_apply, RingHom.map_det]
    rfl
  rw [Matrix.charpoly, hmat, Matrix.det_smul, Fintype.card_fin, hdet, C_pow]

private theorem separable_comp_unit {R : Type} [CommRing R] (r : Rˣ) {p : R[X]}
    (hp : p.Separable) : (p.comp (C ((r⁻¹ : Rˣ) : R) * X)).Separable := by
  obtain ⟨a, b, hab⟩ := hp
  set L : R[X] := C ((r⁻¹ : Rˣ) : R) * X with hL
  have hd : derivative (p.comp L) = C ((r⁻¹ : Rˣ) : R) * (derivative p).comp L := by
    rw [derivative_comp, hL, derivative_C_mul, derivative_X, mul_one]
  have hc : (C (r : R) : R[X]) * C ((r⁻¹ : Rˣ) : R) = 1 := by
    rw [← C_mul, Units.mul_inv, C_1]
  refine ⟨a.comp L, b.comp L * C (r : R), ?_⟩
  have h := congrArg (fun q : R[X] => q.comp L) hab
  simp only [add_comp, mul_comp, one_comp] at h
  rw [hd, ← h]
  linear_combination ((b.comp L) * (derivative p).comp L) * hc

theorem UpperTheory.charpoly_separable_unit_smul :
    SepSc := by
  intro R _ n r M h
  rw [charpoly_unit_smul, Polynomial.separable_def, derivative_C_mul]
  exact (isCoprime_mul_unit_left (isUnit_C.2 (r.isUnit.pow n)) _ _).2
    (separable_comp_unit r h)
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.EulerProductOfQuotientPushforwardSupport
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.eulerProduct_of_quotient_pushforward_support :
    QPush → EulerSupp → Euler := by
  intro hQ hS V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv h1 h2 h3 μ μi m ν νi nv
    hP hPi hPv S a b ha hb hE hET Fi Fv hFi hFii hFv hloc
  obtain ⟨hM, hSupp, hVal⟩ := hS V G Gi Gv q p K T Ti Tv qT pT KT hR hRT j ji jv h1 h2 h3 S Fi Fv
    hFi hFii hFv hloc
  refine ⟨hM, ?_⟩
  have lin := quotLin_of normEx quotEq
  have prd := quotProd_of normEx quotEq
  have pie := quotPi_of normEx quotEq
  let J : (∀ v : S, Tv v) →* ∀ v : S, Gv v :=
    Pi.monoidHom fun v : S => (jv v).comp (Pi.evalMonoidHom _ v)
  have hJ : ∀ (t : ∀ v : S, Tv v) (v : S), J t v = jv v (t v) := fun _ _ => rfl
  obtain ⟨pairPi, valPi⟩ := pie S (fun v : S => Gv v) (fun v : S => Tv v) (fun v : S => m v)
    (fun v : S => jv v) (fun v : S => nv v) (fun v => hPv v) J hJ
  obtain ⟨pairPr, valPr⟩ := prd Gi Ti (∀ v : S, Gv v) (∀ v : S, Tv v) μi ji νi hPi _ J _ pairPi
  obtain ⟨pairL, valL⟩ := (lin _ _ _ _ _ pairPr).2 a b ha hb
  have pullbackMapSquare : Measurable fun g : ∀ v : S, Gv v => ∏ v : S, Fv v (g v) :=
    Finset.measurable_fun_prod _ fun v _ => (hFv v).1.comp (measurable_pi_apply v)
  have indexFSecond : ∀ (t : ∀ v : S, Tv v) (g : ∀ v : S, Gv v),
      ∏ v : S, Fv v ((J t * g) v) = ∏ v : S, Fv v (g v) := fun t g =>
    Finset.prod_congr rfl fun v _ => (hFv v).2 (t v) (g v)
  have mF' : Measurable fun x : Gi × ∀ v : S, Gv v => Fi x.1 * ∏ v : S, Fv v (x.2 v) :=
    (hFi.comp measurable_fst).mul (pullbackMapSquare.comp measurable_snd)
  have iF' : ∀ (t : Ti × ∀ v : S, Tv v) (g : Gi × ∀ v : S, Gv v),
      Fi ((ji.prodMap J t * g).1) * ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) =
        Fi g.1 * ∏ v : S, Fv v (g.2 v) := fun t g => by
    have e1 : Fi ((ji.prodMap J t * g).1) = Fi g.1 := hFii t.1 g.1
    have e2 : ∏ v : S, Fv v ((ji.prodMap J t * g).2 v) = ∏ v : S, Fv v (g.2 v) := indexFSecond t.2 g.2
    rw [e1, e2]
  have hpre : j ⁻¹' (US p K S : Set G) = (US pT KT S : Set T) := by
    ext t
    constructor
    · intro ht v hv
      have := ht v hv
      rw [h2] at this
      exact (h3 v _).2 this
    · intro ht v hv
      show p v (j t) ∈ K v
      rw [h2]
      exact (h3 v _).1 (ht v hv)
  have hET' : (ν.restrict (j ⁻¹' (US p K S : Set G))).map (prS qT pT S) =
      b • νi.prod (Measure.pi fun v : S => nv v) := by
    rw [hpre]; exact hET
  have cπ : Continuous (prS q p S) :=
    hR.cq.prodMk (continuous_pi fun v : S => hR.cp v)
  have cπT : Continuous (prS qT pT S) :=
    hRT.cq.prodMk (continuous_pi fun v : S => hRT.cp v)
  have comm : ∀ t, prS q p S (j t) = ji.prodMap J (prS qT pT S t) := fun t => by
    refine Prod.ext (h1 t) (funext fun v => h2 v t)
  have iF : ∀ t g, Fi (q (j t * g)) * ∏ᶠ v, Fv v (p v (j t * g)) =
      Fi (q g) * ∏ᶠ v, Fv v (p v g) := fun t g => by
    have e1 : Fi (q (j t * g)) = Fi (q g) := by rw [map_mul, h1, hFii]
    have e2 : ∀ v, Fv v (p v (j t * g)) = Fv v (p v g) := fun v => by
      rw [map_mul, h2, (hFv v).2]
    simp only [e1, e2]
  have push := hQ G T (Gi × ∀ v : S, Gv v) (Ti × ∀ v : S, Tv v) μ j ν _ (ji.prodMap J) _ hP pairL
    (US p K S) (hR.opnU S) (prS q p S) (prS qT pT S) cπ cπT comm hE hET'
    (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g))
    (fun x => Fi x.1 * ∏ v : S, Fv v (x.2 v)) hM iF mF' iF' hSupp hVal
  rw [push, (valL _ mF' iF').2, (valPr Fi _ hFi hFii pullbackMapSquare indexFSecond).2, (valPi fun v : S => Fv v)
    (fun v => hFv v) |>.2, Finset.prod_coe_sort S fun v => qI (m v) (jv v) (nv v) (Fv v), mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.EulerProductSupportFinite
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.euler_product_support_finite :
    EulerSupp := by
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv hq hp hK S Fi Fv hFi hFii hFv hS
  classical
  have hKA : ∀ v x, x ∈ K v → ∃ t, ∃ y ∈ K v, x = jv v t * y :=
    fun v x hx => ⟨1, x, hx, by simp⟩
  have hfin : ∀ g, (Function.mulSupport fun v => Fv v (p v g)).Finite := by
    intro g
    refine ((Filter.eventually_cofinite.1 (hR.ae g)).union S.finite_toSet).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hc
    exact hv ((hS v hc.2 _).1 (hKA v _ hc.1))
  obtain ⟨W, hW⟩ : ∃ W : Set G, W = {g | ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y} := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ W ↔ ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y := by
    intro g; rw [hW]; rfl
  have hoff : ∀ g, g ∉ W → ∏ᶠ v, Fv v (p v g) = 0 := by
    intro g hg
    rw [hmem] at hg
    push_neg at hg
    obtain ⟨v, hv, hx⟩ := hg
    refine finprod_eq_zero _ v ((hS v hv _).2 ?_) (hfin g)
    rintro ⟨t, y, hy, e⟩
    exact hx t y hy e
  have hon : ∀ g ∈ W, ∏ᶠ v, Fv v (p v g) = ∏ v ∈ S, Fv v (p v g) := by
    intro g hg
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hc
    exact hv ((hS v hc _).1 ((hmem g).1 hg v hc))
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (US p K S : Set G), ?_,
      (continuous_const.mul continuous_id).isOpen_preimage _ (hR.opnU S), ?_⟩
    · intro x hx
      refine (hmem x).2 fun v hv => ?_
      obtain ⟨t, y, hy, e⟩ := (hmem g).1 hg v hv
      have hx' : p v (g⁻¹ * x) ∈ K v := hx v hv
      refine ⟨t, y * p v (g⁻¹ * x), mul_mem hy hx', ?_⟩
      rw [← mul_assoc, ← e, ← map_mul, mul_inv_cancel_left]
    · simp only [Set.mem_preimage, inv_mul_cancel]
      exact one_mem (US p K S)
  have hqm : Measurable q := hR.cq.measurable
  have hpm : ∀ v, Measurable (p v) := fun v => (hR.cp v).measurable
  have hmeas : Measurable fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g) :=
    (hFi.comp hqm).mul (Finset.measurable_prod _ fun v _ => (hFv v).1.comp (hpm v))
  have hEq : (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      W.indicator (fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g)) := by
    funext g
    by_cases hg : g ∈ W
    · rw [Set.indicator_of_mem hg, hon g hg]
    · rw [Set.indicator_of_notMem hg, hoff g hg, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact hmeas.indicator hWopen.measurableSet
  · intro g h
    have hgW : g ∈ W := by
      by_contra hc
      exact h (by rw [hoff g hc, mul_zero])
    have hch : ∀ v, ∃ t : Tv v, (p v g ∈ K v → t = 1) ∧ (v ∉ S → (jv v t)⁻¹ * p v g ∈ K v) := by
      intro v
      by_cases hk : p v g ∈ K v
      · exact ⟨1, fun _ => rfl, fun _ => by simpa using hk⟩
      · by_cases hv : v ∈ S
        · exact ⟨1, fun h => absurd h hk, fun h => absurd hv h⟩
        · obtain ⟨t, y, hy, e⟩ := (hmem g).1 hgW v hv
          exact ⟨t, fun h => absurd h hk, fun _ => by rw [e]; simpa using hy⟩
    choose tv ht1 ht2 using hch
    obtain ⟨t, -, ht⟩ := hRT.surj 1 tv
      ((hR.ae g).mono fun v hv => by rw [ht1 v hv]; exact one_mem _)
    refine Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, (j t)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    refine SetLike.mem_coe.2 (mem_US.2 fun v hv => ?_)
    rw [map_mul, map_inv, hp, ht]
    exact ht2 v hv
  · intro u hu
    have huW : u ∈ W := (hmem u).2 fun v hv => hKA v _ (hu v hv)
    rw [hon u huW, Finset.prod_coe_sort S (fun v => Fv v (p v u))]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsHaarMeasureAdelicGL
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology Filter

theorem UpperTheory.exists_haarMeasure_adelicGL :
    HaarEx := by
  unfold HaarEx
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hR μ μi m hμ hμi hm S
  classical
  haveI : ∀ v, (m v).IsHaarMeasure := hm
  have cf : Continuous (prS q p S) := by
    have h : ⇑(prS q p S) = fun g => (q g, fun v : S => p v g) := rfl
    rw [h]
    exact hR.cq.prodMk (continuous_pi fun v => hR.cp v)
  have mf : Measurable (prS q p S) := cf.measurable
  have hs : ∀ h : Gi × ∀ v : S, Gv v, ∃ u ∈ US p K S, prS q p S u = h := by
    rintro ⟨gi, gv⟩
    obtain ⟨g, h1, h2⟩ := hR.surj gi (fun v => if hv : v ∈ S then gv ⟨v, hv⟩ else 1) (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      rw [dif_neg hv']
      exact one_mem _)
    refine ⟨g, ?_, ?_⟩
    · intro v hv
      rw [h2, dif_neg hv]
      exact one_mem _
    · rw [prS_apply, h1]
      congr 1
      funext v
      rw [h2, dif_pos v.2]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (US p K S : Set G)).map (prS q p S) := ⟨_, rfl⟩
  haveI inv : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hs h
    ext A hA
    have hA' : MeasurableSet ((fun x => prS q p S u * x) ⁻¹' A) := measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA, hν, Measure.map_apply mf hA',
      Measure.map_apply mf hA, Measure.restrict_apply (mf hA'), Measure.restrict_apply (mf hA)]
    have hset : prS q p S ⁻¹' ((fun x => prS q p S u * x) ⁻¹' A) ∩ (US p K S : Set G) =
        (fun x => u * x) ⁻¹' (prS q p S ⁻¹' A ∩ (US p K S : Set G)) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe,
        Subgroup.mul_mem_cancel_left _ hu]
    rw [hset, measure_preimage_mul]
  haveI fin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun D hD => ?_⟩
    rw [hν, Measure.map_apply mf hD.measurableSet, Measure.restrict_apply (mf hD.measurableSet)]
    let C : ∀ v, Set (Gv v) := fun v =>
      if hv : v ∈ S then (fun h : Gi × ∀ v : S, Gv v => h.2 ⟨v, hv⟩) '' D else K v
    have hC : ∀ v, IsCompact (C v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [C, dif_pos hv]
        exact hD.image (by fun_prop)
      · simp only [C, dif_neg hv]
        exact hR.cpt v
    have hW := hR.prop (Prod.fst '' D) C (hD.image continuous_fst) hC (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp only [C, dif_neg hv']
      exact subset_rfl)
    refine lt_of_le_of_lt (measure_mono ?_) hW.measure_lt_top
    rintro g ⟨h1, h2⟩
    refine ⟨⟨_, h1, rfl⟩, fun v => ?_⟩
    by_cases hv : v ∈ S
    · simp only [C, dif_pos hv]
      exact ⟨_, h1, rfl⟩
    · simp only [C, dif_neg hv]
      exact h2 v hv
  have e := Measure.isMulLeftInvariant_eq_smul ν (μi.prod (Measure.pi fun v : S => m v))
  refine ⟨Measure.haarScalarFactor ν (μi.prod (Measure.pi fun v : S => m v)), ?_, ?_⟩
  · intro h0
    rw [h0, zero_smul] at e
    have h1 : ν Set.univ = 0 := by rw [e]; rfl
    rw [hν, Measure.map_apply mf MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] at h1
    exact (hR.opnU S).measure_ne_zero μ ⟨1, one_mem _⟩ h1
  · unfold Eul
    rw [← hν]
    exact e
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.HaarUnimodularCriterion
section
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal NNReal

private theorem haar_inv_eq_self {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] : μ.inv = μ := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ.inv = c • μ :=
    ⟨Measure.haarScalarFactor μ.inv μ, Measure.isMulLeftInvariant_eq_smul _ _⟩
  have hinv : μ.inv.inv = μ := Measure.inv_inv μ
  have hsq : μ = (c * c) • μ := by
    calc μ = μ.inv.inv := hinv.symm
      _ = (c • μ).inv := by rw [hc]
      _ = c • μ.inv := by
        simpa only [Measure.inv_def] using Measure.map_smul c (μ := μ) measurable_inv.aemeasurable
      _ = c • (c • μ) := by rw [hc]
      _ = (c * c) • μ := by rw [smul_smul]
  have K : TopologicalSpace.PositiveCompacts G := Classical.arbitrary _
  have hpos : μ K ≠ 0 :=
    ((isOpen_interior.measure_pos μ K.interior_nonempty).trans_le
      (measure_mono interior_subset)).ne'
  have hfin : μ K ≠ ∞ := K.isCompact.measure_lt_top.ne
  have h3 : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    rw [one_mul]
    conv_rhs => rw [hsq]
    simp
  have h4 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h3
  have h5 : c = 1 := by
    rw [ENNReal.coe_eq_one, ← pow_two] at h4
    exact (pow_eq_one_iff_of_nonneg (zero_le : (0 : ℝ≥0) ≤ c) two_ne_zero).1 h4
  rw [hc, h5, one_smul]

theorem UpperTheory.haar_unimodular_criterion :
    UniOf := by
  intro G _ _ _ _ _ _ _ _ μ hμ
  have key : μ.IsMulRightInvariant → Uni μ := fun hr => ⟨hμ, ⟨haar_inv_eq_self μ⟩⟩
  refine ⟨key, fun hcomm => key ⟨fun g => ?_⟩⟩
  have h : (fun x : G => x * g) = fun x => g * x := funext fun x => hcomm x g
  rw [h]
  exact map_mul_left_eq_self μ g
end

