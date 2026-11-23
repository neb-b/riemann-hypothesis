module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CardQuotEqNatAbsNorm
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

theorem card_quot_eq_natAbs_norm {S : Type*} [CommRing S] [IsDomain S] [Module.Free ℤ S]
    [Module.Finite ℤ S] (f : S) (hf : f ≠ 0) :
    Nat.card (S ⧸ Ideal.span {f}) = (Algebra.norm ℤ f).natAbs := by
  classical
  let N : Submodule ℤ S := (Ideal.span {f}).restrictScalars ℤ
  have hmem : ∀ x : S, f * x ∈ N := fun x => Ideal.mul_mem_right x _ (Ideal.subset_span rfl)
  let g : S →+ N :=
    { toFun := fun x => ⟨f * x, hmem x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [mul_add] }
  have hbij : Function.Bijective g := by
    constructor
    · intro x y hxy
      have h1 : f * x = f * y := congrArg Subtype.val hxy
      exact mul_left_cancel₀ hf h1
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      exact ⟨a, by ext; simp [g, mul_comm]⟩
  let e : S ≃+ N := AddEquiv.ofBijective g hbij
  have h := Submodule.natAbs_det_equiv N e
  have hlin : N.subtype ∘ₗ (e : S →+ N).toIntLinearMap = Algebra.lmul ℤ S f := by
    ext x
    rfl
  rw [hlin, ← Algebra.norm_apply] at h
  rw [h]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ (Ideal.span {f})).toEquiv.symm

theorem norm_int_eq_norm_rat {K : Type*} [Field K] [NumberField K] (O : Subring K)
    [Module.Free ℤ O] [Module.Finite ℤ O] (h : Module.finrank ℤ O = Module.finrank ℚ K)
    (f : O) : ((Algebra.norm ℤ f : ℤ) : ℚ) = Algebra.norm ℚ (f : K) := by
  classical
  let b := Module.Free.chooseBasis ℤ O
  have hli : LinearIndependent ℚ (fun i => ((b i : O) : K)) := by
    have h1 : LinearIndependent ℤ (fun i => ((b i : O) : K)) :=
      b.linearIndependent.map' (O.subtype.toIntAlgHom.toLinearMap)
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℚ K := by
    rw [← h, Module.finrank_eq_card_chooseBasisIndex]
  haveI : Nonempty (Module.Free.ChooseBasisIndex ℤ O) := by
    apply Fintype.card_pos_iff.mp
    rw [hcard]
    exact Module.finrank_pos
  let b' := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb' : ∀ i, b' i = ((b i : O) : K) := fun i => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank]
  rw [Algebra.norm_eq_matrix_det b f, Algebra.norm_eq_matrix_det b' (f : K)]
  have hm := RingHom.map_det (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f)
  rw [show ((Algebra.leftMulMatrix b f).det : ℚ) = (Int.castRingHom ℚ) (Algebra.leftMulMatrix b f).det from rfl, hm]
  congr 1
  ext i j
  have hx : (f : K) * b' j = ∑ k, ((b.repr (f * b j) k : ℤ) : ℚ) • b' k := by
    have e1 := congrArg (O.subtype.toIntAlgHom.toLinearMap) (b.sum_repr (f * b j))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at e1
    simp only [map_zsmul] at e1
    simp only [hb', Int.cast_smul_eq_zsmul]
    exact e1.symm
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, eq_intCast]
  rw [hx, b'.repr_sum_self]

theorem abs_norm_eq_prod {K : Type*} [Field K] [NumberField K] (x : K) :
    |(Algebra.norm ℚ x : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast, Complex.norm_ratCast] at h2
  exact h2.trans (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)).symm

theorem index_thm : IndexStatement := by
  intro K _ _ O hfree hfin hrank f hf
  haveI := hfree
  haveI := hfin
  have hc := card_quot_eq_natAbs_norm f hf
  have hn := norm_int_eq_norm_rat O hrank f
  have hprod := abs_norm_eq_prod (f : K)
  have h1 : (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| := by
    rw [hc, ← hn]
    simp [Nat.cast_natAbs, Int.cast_abs, Rat.cast_intCast]
  refine ⟨h1, ?_⟩
  rw [h1, hprod, Real.log_prod (fun σ _ => ?_)]
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (fun h0 => hf (Subtype.ext h0)))

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.HeightOneIffDimOne
section
namespace ReciprocityTheory.ChartRestriction.G.AI

open Module

universe u v

section general

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ord_ringEquiv (e : R ≃+* S) (x : R) : Ring.ord R x = Ring.ord S (e x) := by
  unfold Ring.ord
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  let q := Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {e x}) e
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  let g : (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) :=
    { q.toAddEquiv with
      map_smul' := fun r m => by
        obtain ⟨m', rfl⟩ := Ideal.Quotient.mk_surjective m
        simp only [AddEquiv.toFun_eq_coe, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv]
        rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq,
          ← map_mul]
        show q (Ideal.Quotient.mk _ (r * m')) = Ideal.Quotient.mk _ (e r) * q (Ideal.Quotient.mk _ m')
        simp [q] }
  have iso : Submodule R (R ⧸ Ideal.span {x}) ≃o Submodule S (S ⧸ Ideal.span {e x}) :=
    Submodule.orderIsoMapComap g
  have h : Order.krullDim (Submodule R (R ⧸ Ideal.span {x})) =
      Order.krullDim (Submodule S (S ⧸ Ideal.span {e x})) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
  unfold Module.length
  first
    | simp only [h]
    | congr 1

theorem length_self_ringEquiv (e : R ≃+* S) : Module.length R R = Module.length S S := by
  haveI : RingHomInvPair (e : R →+* S) (e.symm : S →+* R) := RingHomInvPair.of_ringEquiv e
  haveI : RingHomInvPair (e.symm : S →+* R) (e : R →+* S) := RingHomInvPair.symm _ _
  have iso : Submodule R R ≃o Submodule S S := Submodule.orderIsoMapComap e.toSemilinearEquiv
  have h : Order.krullDim (Submodule R R) = Order.krullDim (Submodule S S) := by
    first
      | exact le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
          (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
      | exact Order.krullDim_eq_of_orderIso iso
      | exact iso.krullDim_eq
  unfold Module.length
  first
    | simp only [h]
    | congr 1

end general

section quot

variable {A : Type u} [CommRing A]

noncomputable def quotQuotComapEquiv (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    (A ⧸ Ideal.span {a}) ⧸ P.asIdeal ≃+*
      A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal :=
  have hle : Ideal.span {a} ≤
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal := by
    intro x hx
    show Ideal.Quotient.mk _ x ∈ P.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  have hP : P.asIdeal = (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.map
      (Ideal.Quotient.mk (Ideal.span {a})) :=
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
  (Ideal.quotEquivOfEq hP).trans (DoubleQuot.quotQuotEquivQuotOfLE hle)

theorem quotQuotComapEquiv_mk (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    quotQuotComapEquiv a P (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ b)) =
      Ideal.Quotient.mk _ b := by
  first
    | rfl
    | simp [quotQuotComapEquiv]
    | fail

end quot

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]

theorem height_one_iff_dim_one (h2 : ringKrullDim A = 2) {a : A} (ha : a ≠ 0) (p : PrimeSpectrum A)
    (hap : a ∈ p.asIdeal) : p.asIdeal.height = 1 ↔ ringKrullDim (A ⧸ p.asIdeal) = 1 := by
  have hs : PrimeSpectrum.zeroLocus (p.asIdeal : Set A) = Set.Ici p := by
    ext q
    simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_Ici]
    rfl
  have hdim : ringKrullDim (A ⧸ p.asIdeal) = (Order.coheight p : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici, hs]
  have hsum : Order.height p + Order.coheight p ≤ 2 := by
    have h := Order.krullDim_eq_iSup_height_add_coheight_of_nonempty (α := PrimeSpectrum A)
    have h2' : Order.krullDim (PrimeSpectrum A) = 2 := h2
    rw [h2'] at h
    have h3 : (⨆ q : PrimeSpectrum A, Order.height q + Order.coheight q) = 2 := by
      have h' := h.symm
      rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h'
      exact WithBot.coe_injective h'
    rw [← h3]
    exact le_iSup (fun q : PrimeSpectrum A => Order.height q + Order.coheight q) p
  have h1 : 1 ≤ Order.height p := by
    have hb : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < p := by
      show (⊥ : Ideal A) < p.asIdeal
      exact bot_lt_iff_ne_bot.mpr (fun h => ha (Ideal.mem_bot.mp (h ▸ hap)))
    exact le_trans le_add_self (Order.height_add_one_le hb)
  have hm : Order.height (IsLocalRing.closedPoint A) = 2 := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    show (IsLocalRing.maximalIdeal A).height = 2
    have := (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A)).trans h2
    rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at this
    exact WithBot.coe_injective this
  have hpm : Order.height p = 2 ∨ 1 ≤ Order.coheight p := by
    by_cases hp : p = IsLocalRing.closedPoint A
    · left; rw [hp]; exact hm
    · right
      have hle : p ≤ IsLocalRing.closedPoint A := by
        show p.asIdeal ≤ IsLocalRing.maximalIdeal A
        exact IsLocalRing.le_maximalIdeal p.isPrime.ne_top
      exact le_trans le_add_self (Order.coheight_add_one_le (lt_of_le_of_ne hle hp))
  rw [PrimeSpectrum.height_eq_orderHeight, hdim]
  clear hm hdim hs
  generalize Order.height p = h at *
  generalize Order.coheight p = c at *
  have hc : c ≠ ⊤ := by rintro rfl; simp at hsum
  have hh : h ≠ ⊤ := by rintro rfl; simp at hsum
  lift c to ℕ using hc
  lift h to ℕ using hh
  norm_cast at *
  omega

theorem dim_quot_comap (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) =
      ringKrullDim (A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal) := by
  first
    | exact ringKrullDim_eq_of_ringEquiv (quotQuotComapEquiv a P)
    | exact (quotQuotComapEquiv a P).ringKrullDim
    | exact RingEquiv.ringKrullDim (quotQuotComapEquiv a P)

theorem length_loc_quot (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    length (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) a := by
  have hM : Algebra.algebraMapSubmonoid (A ⧸ Ideal.span {a})
      (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal.primeCompl =
      P.asIdeal.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨y, hx, rfl⟩
  have hloc : IsLocalization P.asIdeal.primeCompl
      (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸
        (Ideal.span {a}).map (algebraMap A (Localization.AtPrime
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal))) :=
    hM ▸ inferInstance
  let e := IsLocalization.algEquiv P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
      (Localization.AtPrime (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal ⧸
        (Ideal.span {a}).map (algebraMap A (Localization.AtPrime
          (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal)))
  let f := (IsLocalizedModule.linearEquiv P.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap P.asIdeal.primeCompl (A ⧸ Ideal.span {a}))
      (Algebra.linearMap (A ⧸ Ideal.span {a}) (Localization.AtPrime P.asIdeal))).extendScalarsOfIsLocalization
      P.asIdeal.primeCompl (Localization.AtPrime P.asIdeal)
  rw [f.length_eq, length_self_ringEquiv e.toRingEquiv,
    ← Module.length_eq_of_surjective Ideal.Quotient.mk_surjective, ordLoc, Ring.ord,
    Ideal.map_span, Set.image_singleton]

theorem ordMod_quot (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b) =
      ordMod (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) b := by
  unfold ordMod
  rw [ord_ringEquiv (quotQuotComapEquiv a P), quotQuotComapEquiv_mk]

theorem length_quot_restrict (a : A) (N : Type v) [AddCommGroup N] [Module (A ⧸ Ideal.span {a}) N]
    [Module A N] [IsScalarTower A (A ⧸ Ideal.span {a}) N] :
    length (A ⧸ Ideal.span {a}) N = length A N := by
  have hsmul : ∀ (r : A) (n : N), Ideal.Quotient.mk (Ideal.span {a}) r • n = r • n := fun r n => by
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul (A ⧸ Ideal.span {a})]
  let g : Submodule A N → Submodule (A ⧸ Ideal.span {a}) N := fun p =>
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun c n hn => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hsmul]
        exact p.smul_mem r hn }
  let iso : Submodule (A ⧸ Ideal.span {a}) N ≃o Submodule A N :=
    { toFun := fun p => p.restrictScalars A
      invFun := g
      left_inv := fun p => by ext; rfl
      right_inv := fun p => by ext; rfl
      map_rel_iff' := by
        intro p q
        exact Submodule.restrictScalars_le A }
  have h : Order.krullDim (Submodule (A ⧸ Ideal.span {a}) N) = Order.krullDim (Submodule A N) :=
    le_antisymm (Order.krullDim_le_of_strictMono iso iso.strictMono)
      (Order.krullDim_le_of_strictMono iso.symm iso.symm.strictMono)
  unfold Module.length
  first
    | simp only [h]
    | congr 1

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaA
section
open MeasureTheory Set
open scoped Pointwise

namespace ReciprocityTheory.ChartRestriction.G.AI

theorem cone_preimage (L : E3 ≃ₗᵢ[ℝ] E3) (s : Set S2) :
    Ioo (0 : ℝ) 1 • ((↑) '' ((fun n : S2 => (⟨L n, by simp⟩ : S2)) ⁻¹' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E3)) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
  constructor
  · rintro ⟨r, hr, _, ⟨n, hn, rfl⟩, rfl⟩
    exact ⟨r, hr, _, ⟨_, hn, rfl⟩, by simp⟩
  · rintro ⟨r, hr, _, ⟨m, hm, rfl⟩, hx⟩
    refine ⟨r, hr, _, ⟨⟨L.symm m, by simp⟩, ?_, rfl⟩, ?_⟩
    · convert hm using 1
      ext
      simp
    · apply L.injective
      rw [← hx]
      simp

theorem measurable_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    Measurable (fun n : S2 => (⟨L n, by simp⟩ : S2)) := ((L.continuous.comp continuous_subtype_val).subtype_mk _).measurable

theorem toSphere_measurePreserving (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2))
      (volume : Measure E3).toSphere (volume : Measure E3).toSphere := by
  refine ⟨measurable_sphereMap L, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_sphereMap L) hs, Measure.toSphere_apply' _ hs,
    Measure.toSphere_apply' _ (measurable_sphereMap L hs), cone_preimage]
  congr 1
  have hmp : MeasurePreserving (L.toHomeomorph.toMeasurableEquiv) (volume : Measure E3) volume :=
    L.measurePreserving
  exact hmp.measure_preimage_equiv _

theorem sphereInv_thm : SphereInvStatement := by
  refine ⟨?_, fun L => ?_⟩
  · have h1 : (volume : Measure E3).toSphere Set.univ ≠ 0 := by
      rw [Measure.toSphere_apply_univ]
      refine mul_ne_zero (by simp) ?_
      exact (Metric.measure_ball_pos _ _ one_pos).ne'
    have h2 : (volume : Measure E3).toSphere Set.univ ≠ ⊤ := measure_ne_top _ _
    constructor
    rw [sphereMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h1 h2]
  · have hL := toSphere_measurePreserving L
    refine ⟨hL.measurable, ?_⟩
    rw [sphereMeasure, Measure.map_smul _ hL.measurable.aemeasurable, hL.map_eq]

end ReciprocityTheory.ChartRestriction.G.AI
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthEqOfSurjOfKerEq
section
namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

theorem length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq

theorem mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rfl

theorem length_ker_swap {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring

theorem length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩

theorem length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by
  apply length_ne_top_of_killed (Ideal.span {a, b}) _ hfin
  rintro r hr ⟨k, hk⟩
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hr
  have hbk : b • k = 0 := by simpa using hk
  have hak : a • k = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  rw [add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]

end ReciprocityTheory.ChartRestriction.G.AI
end

