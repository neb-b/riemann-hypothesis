module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem ctr_algebraMap' (v : Derivation R B B) (b : B) : ctr v (algebraMap B (DR R B) b) = 0 :=
  CliffordAlgebra.contractLeft_algebraMap _ _ b

theorem ctr_ι' (v : Derivation R B B) (ω : Ω[B⁄R]) :
    ctr v (ι1 ω) = algebraMap B (DR R B) (v.liftKaehlerDifferential ω) :=
  CliffordAlgebra.contractLeft_ι _ _ ω

theorem ctr_mul' (v : Derivation R B B) (x y : DR R B) :
    ctr v (x * y) = ctr v x * y + sgn x * ctr v y := by
  induction x using indDR generalizing y with
  | h b =>
    rw [← Algebra.smul_def, map_smul, ctr_algebraMap', zero_mul, zero_add, AlgHom.commutes, Algebra.smul_def]
  | hd b =>
    rw [ctr_ι', sgn_ι]
    rw [show ctr v (ι1 (D R B b) * y) = _ from CliffordAlgebra.contractLeft_ι_mul _ _ _]
    rw [Algebra.smul_def, neg_mul, sub_eq_add_neg]
    rfl
  | hm x z hx hz =>
    rw [mul_assoc, hx, hz, hx, map_mul]
    simp only [mul_add, add_mul, mul_assoc]
    abel
  | ha x z hx hz =>
    rw [add_mul, map_add (f := _), hx, hz, map_add (f := _), map_add (f := _), add_mul, add_mul]
    abel

theorem ctr_mem_of_span (v : Derivation R B B) {S : Set (DR R B)} {T : Ideal (DR R B)}
    (hST : Ideal.span S ≤ T) (hS : ∀ s ∈ S, ctr v s ∈ T) : ∀ x ∈ Ideal.span S, ctr v x ∈ T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, ctr_mul']
    exact add_mem (Ideal.mul_mem_left _ _ (hST hx))
      (Ideal.mul_mem_left _ _ ih)

end GlobalTheory.CtrFil

namespace GlobalTheory.CtrFil

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)
  (v : Derivation R B B)

theorem lie_apply' (x : DR R B) : lie v x = dDR R B (ctr v x) + ctr v (dDR R B x) := rfl

theorem ctr_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : ctr v x ∈ rel R δ := by
  refine ctr_mem_of_span v le_rfl ?_ x hx
  rintro _ ⟨n, a, ha, rfl⟩
  rw [ctr_ι', map_sub, map_smul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, hv n a ha, sub_self, map_zero]
  exact zero_mem _

theorem lie_mem_rel (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) {x : DR R B}
    (hx : x ∈ rel R δ) : lie v x ∈ rel R δ := by
  rw [lie_apply']
  exact add_mem (dDR_mem_rel R δ (ctr_mem_rel δ v hv hx)) (ctr_mem_rel δ v hv (dDR_mem_rel R δ hx))

theorem fil_succ_le' (n : ℕ) : fil δ (n + 1) ≤ fil δ n :=
  Ideal.span_mono fun _ ⟨l, h1, h2, h3⟩ ↦ ⟨l, h1, by omega, h3⟩

theorem filDR_succ_le' (n : ℕ) : filDR R δ (n + 1) ≤ filDR R δ n :=
  sup_le_sup_right (Ideal.span_mono (Set.image_mono (fil_succ_le' δ n))) _

theorem rel_le_filDR' (n : ℕ) : rel R δ ≤ filDR R δ n := le_sup_right

theorem span_le_filDR' (n : ℕ) : Ideal.span (algebraMap B (DR R B) '' fil δ n) ≤ filDR R δ n := le_sup_left

theorem ctr_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ n) : ctr v x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  refine add_mem (ctr_mem_of_span v (span_le_filDR' δ n) ?_ y hy) (rel_le_filDR' δ n (ctr_mem_rel δ v hv hz))
  rintro _ ⟨b, _, rfl⟩
  rw [ctr_algebraMap']
  exact zero_mem _

theorem ι_mem_filDR (n : ℕ) {ω : Ω[B⁄R]} (hω : ω ∈ fil δ n • (⊤ : Submodule B Ω[B⁄R]) ⊔ N1 R δ) :
    ι1 ω ∈ filDR R δ n := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hω
  rw [map_add (f := _)]
  refine add_mem ?_ (rel_le_filDR' δ n hw)
  refine span_le_filDR' δ n ?_
  refine Submodule.smul_induction_on hu (fun c hc ω _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul, Algebra.smul_def, Algebra.commutes]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨c, hc, rfl⟩)
  · rw [map_add (f := _)]; exact add_mem hx hy

theorem dDR_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : dDR R B x ∈ filDR R δ n := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  refine add_mem ?_ (rel_le_filDR' δ n (dDR_mem_rel R δ hz))
  clear hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    rw [dDR_algebraMap]
    refine ι_mem_filDR δ n (_root_.GlobalTheory.DerFil.deriv_fil_succ_le R B Ω[B⁄R] J δ (D R B) (N1 R δ) ?_ n b hb)
    intro m a ha
    exact Ideal.subset_span ⟨m, a, ha, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact add_mem hx hy
  | smul r x hx ih =>
    rw [smul_eq_mul, dDR_mul]
    refine add_mem (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_left _ _ ?_)
    exact filDR_succ_le' δ n (span_le_filDR' δ (n + 1) hx)

theorem lie_mem_filDR (hv : ∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) (n : ℕ) {x : DR R B}
    (hx : x ∈ filDR R δ (n + 1)) : lie v x ∈ filDR R δ n := by
  rw [lie_apply']
  exact add_mem (dDR_mem_filDR δ v hv n (ctr_mem_filDR δ v hv (n + 1) hx))
    (ctr_mem_filDR δ v hv n (dDR_mem_filDR δ v hv n hx))

end GlobalTheory.CtrFil


open GlobalTheory.CtrFil in
theorem GlobalTheory.PDForm.ctr_lie_rel_filDR : (∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B)
    (δ : DividedPowers J) (v : Derivation R B B), (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) →
    ∀ x ∈ rel R δ, ctr v x ∈ rel R δ ∧ lie v x ∈ rel R δ) ∧ ∀ (R B : Type) [CommRing R] [CommRing B]
    [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (v : Derivation R B B),
    (∀ n, ∀ a ∈ J, v (δ.dpow (n + 1) a) = δ.dpow n a * v a) → ∀ n, (∀ x ∈ filDR R δ n, ctr v x ∈ filDR R δ n) ∧
    (∀ x ∈ filDR R δ (n + 1), dDR R B x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), lie v x ∈ filDR R δ n :=
  ⟨fun _ _ _ _ _ _ δ v hv _ hx ↦ ⟨ctr_mem_rel δ v hv hx, lie_mem_rel δ v hv hx⟩,
    fun _ _ _ _ _ _ δ v hv n ↦ ⟨fun _ hx ↦ ctr_mem_filDR δ v hv n hx, fun _ hx ↦ dDR_mem_filDR δ v hv n hx,
      fun _ hx ↦ lie_mem_filDR δ v hv n hx⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordInEqOfJet
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum iterD cWt risingFactor DerivFormula)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt upIdele IsLatOf)
open GlobalTheory.ToricTransport (coordIn)
open scoped Classical

namespace GlobalTheory.LatConjOne

theorem exists_list_count {I : Type} [Fintype I] [DecidableEq I] (κ : I → ℕ) : ∃ u : List I, ∀ i, u.count i = κ i := by
  refine ⟨(∑ j, κ j • ({j} : Multiset I)).toList, fun i => ?_⟩
  rw [← Multiset.coe_count, Multiset.coe_toList, Multiset.count_sum']
  simp [Multiset.count_singleton]

theorem exists_perm {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I]
    (ι : K →+* ℂ) (φ : I → E →+* ℂ) (g : ℂ ≃+* ℂ) (hφ : IsCMType φ) (hK : ∀ i, (φ i).comp (algebraMap K E) = ι)
    (hg : ∀ x, g (ι x) = ι x) (hr : ∃ x, starRingEnd ℂ (ι x) ≠ ι x) :
    ∃ π : I ≃ I, ∀ i, (g : ℂ →+* ℂ).comp (φ i) = φ (π i) := by
  have e : ∀ i x, φ i (algebraMap K E x) = ι x := fun i x => by rw [← RingHom.comp_apply, hK]
  have h1 : ∀ i, ∃ j, (g : ℂ →+* ℂ).comp (φ i) = φ j := by
    intro i
    obtain ⟨j, hj, -⟩ := hφ ((g : ℂ →+* ℂ).comp (φ i))
    rcases hj with hj | hj
    · exact ⟨j, hj⟩
    · exfalso
      obtain ⟨x, hx⟩ := hr
      have := congrArg (fun f : E →+* ℂ => f (algebraMap K E x)) hj
      simp only [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, Function.comp_apply, e] at this
      rw [RingEquiv.coe_toRingHom, hg] at this
      exact hx this.symm
  choose π hπ using h1
  have hinj : Function.Injective π := by
    intro i i' h
    have h2 : φ i = φ i' := by
      have h3 := (hπ i).trans ((congrArg φ h).trans (hπ i').symm)
      ext x
      have := congrArg (fun f : E →+* ℂ => f x) h3
      simpa using g.injective this
    obtain ⟨j, -, hj⟩ := hφ (φ i)
    rw [hj i (Or.inl rfl), hj i' (Or.inl h2)]
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), hπ⟩

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem two_le_finrank_of_unramFin (E : Type) [Field E] [NumberField E] [IsCMField E] (h : UnramFin E) :
    2 ≤ Module.finrank ℚ (maximalRealSubfield E) := by
  by_contra hlt
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have h1 : Module.finrank ℚ (maximalRealSubfield E) = 1 := by omega
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hE : Module.finrank ℚ E = 2 := by
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h1, h2]
  have hgt := NumberField.abs_discr_gt_two (K := E) (by omega)
  have hbt : (⊥ : Subalgebra ℚ (maximalRealSubfield E)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  let f : (maximalRealSubfield E) ≃ₐ[ℚ] ℚ :=
    AlgEquiv.trans (Subalgebra.topEquiv (R := ℚ) (A := maximalRealSubfield E)).symm
      ((Subalgebra.equivOfEq _ _ hbt.symm).trans (Algebra.botEquiv ℚ (maximalRealSubfield E)))
  have hF : NumberField.discr (maximalRealSubfield E) = 1 := by
    rw [NumberField.discr_eq_discr_of_algEquiv _ f, Rat.numberField_discr]
  have key := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := maximalRealSubfield E) (𝒪 := 𝓞 (maximalRealSubfield E)) E (𝓞 E)
  have hU : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := h
  rw [hU, Ideal.absNorm_top, hF] at key
  simp at key
  rw [Int.abs_eq_natAbs, key] at hgt
  norm_num at hgt

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

theorem gamma_nat_add (k m : ℕ) (hk : 1 ≤ k) :
    Real.Gamma ((k : ℝ) + m) = ((k - 1).factorial : ℝ) * ∏ j ∈ Finset.range m, ((k : ℝ) + j) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.prod_empty, mul_one]
    have := Real.Gamma_nat_eq_factorial (k - 1)
    rwa [Nat.cast_sub hk, Nat.cast_one, sub_add_cancel] at this
  | succ m ih =>
    have h0 : (k : ℝ) + m ≠ 0 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : (0 : ℝ) ≤ m := m.cast_nonneg
      exact ne_of_gt (by linarith)
    rw [Finset.prod_range_succ, Nat.cast_succ, ← add_assoc, Real.Gamma_add_one h0, ih]; ring

theorem cmPeriodConstant_eq_of_card_cmType (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E)) (κ : I → ℕ) :
    (C0 E d k κ : ℂ) = (cWt E k : ℂ) * risingFactor k κ * (-1) ^ (∑ i, κ i) *
      ((2 * Real.pi / Real.sqrt d : ℝ) : ℂ) ^ (∑ i, κ i) := by
  rw [cmValueConst_eq]
  simp only [cWt, risingFactor, gamma_nat_add _ _ hk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard,
    Finset.prod_pow_eq_pow_sum]
  have h1 : ((-1 : ℂ)) ^ (∑ i, κ i) * (-1) ^ (∑ i, κ i) = 1 := by rw [← mul_pow]; norm_num
  push_cast
  linear_combination (-(((|(discr (maximalRealSubfield E) : ℝ)| ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) *
    ((k - 1).factorial : ℂ) ^ Module.finrank ℚ (maximalRealSubfield E) * (∏ x, ∏ j ∈ Finset.range (κ x), ((k : ℂ) + j)) *
    (Real.pi : ℂ) ^ (∑ i, κ i) * ((Real.sqrt d : ℝ) : ℂ)⁻¹ ^ (∑ i, κ i) * 2 ^ (∑ i, κ i))) * h1

end GlobalTheory.LatConjOne

namespace GlobalTheory.LatConjOne

end GlobalTheory.LatConjOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassSecondSystemEqNegDefect
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem connForm_sub_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hC : Const s₀) (S : Sys I π s₀)
    (Q : ∀ U : AffOp X₀, S.thickObj hI U ⟶
      (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)))
    (hQ : ∀ U b, (Q U).φ b = S.p U b) (f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π))) (g : C0 S.F)
    (hg : d0 S.F g = ((S.coef hI).pullbackOneCocycle f).1) (F : Form s₀) (h : C0 (O (dp0 R₀) s₀))
    (hh : d0 _ h = ((redMor hI hk s₀).coef.pullbackOneCocycle f).1 - F.1.1) (U : AffOp X₀) :
    connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
        D R₀ (Sec s₀ U.unop.1) (ev f (Q U) : Sec s₀ U.unop.1) =
      connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) + D R₀ (Sec s₀ U.unop.1) (S.p U (g U)) := by
  set f₀ := (redMor hI hk s₀).coef.pullbackOneCocycle f with hf₀
  have e : f₀ = F.1 + ⟨d0 _ h, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ h⟩ := by
    apply Subtype.ext
    change f₀.1 = F.1.1 + d0 _ h
    rw [hh]; abel
  let hU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦
    @id (Sec s₀ U.unop.1) <| h (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))
  let qU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦ @id (Sec s₀ U.unop.1) <| ev f (Q U)
  let k : C0 (OAff s₀) := fun U ↦ hU U - S.p U (g U) - qU U
  have hk0 : d0 _ k = 0 := by
    funext U V a
    let tr := Thick.trivHom (hx := affPt_w s₀ U.unop) (T := Thick.triv _ _ (affPt_w s₀ V.unop))
      (Sec.res s₀ (leOfHom a.unop)) (affPt_res s₀ (leOfHom a.unop))
    have h1 := congrArg (fun q ↦ q _ _ tr) hh
    simp only [amitsur_d0_apply, Pi.sub_apply] at h1
    have h0 : F.1.1 _ _ tr = 0 := F.2 tr rfl rfl
    rw [h0, sub_zero] at h1
    have h1' : hU V - Sec.res s₀ (leOfHom a.unop) (hU U) = (f₀.1 _ _ tr : Sec s₀ V.unop.1) := h1
    have h2 := ev_sq f (Q U) ((redMor hI hk s₀).functor.map tr) ((S.thick hI).map a) (Q V) fun c ↦ by
      change Sec.res s₀ (leOfHom a.unop) ((Q U).φ c) = (Q V).φ (mp S.F a c)
      rw [hQ, hQ, S.nat]; rfl
    have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
      have := congrArg (fun q ↦ q U V a) hg
      simp only [amitsur_d0_apply] at this
      exact this.symm
    have h2' : Sec.res s₀ (leOfHom a.unop) (qU U) + (f₀.1 _ _ tr : Sec s₀ V.unop.1) =
        @id (Sec s₀ V.unop.1) ((Q V).φ (ev f ((S.thick hI).map a))) + qU V := h2
    rw [hQ, id] at h2'
    erw [h3] at h2'
    have nat' : S.p V (mp S.F a (g U)) = Sec.res s₀ (leOfHom a.unop) (S.p U (g U)) := S.nat a (g U)
    rw [map_sub, nat'] at h2'
    change k V - Sec.res s₀ (leOfHom a.unop) (k U) = 0
    simp only [k, map_sub]
    linear_combination h1' + h2'
  obtain ⟨r, hr⟩ := hC k hk0
  have hD : D R₀ (Sec s₀ U.unop.1) (k U) = 0 := by rw [hr U]; exact (D R₀ _).map_algebraMap r
  simp only [k, map_sub] at hD
  rw [e, connForm_add, crystallineConnectionForm_coboundaryZero, ← sub_eq_zero]
  change connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (hU U) - D R₀ (Sec s₀ U.unop.1) (qU U) -
    (connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (S.p U (g U))) = 0
  rw [← hD]; abel

theorem r_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hC S S' Φ θ hΘ c hc w hw z hz
  have T := fun (U V : AffOp X₀) ↦ _root_.GlobalTheory.LiftSys.Taylor.ev_sub_ev_eq R R₀ I hI π hπ hk X₀ s₀ S S' U V
  choose Q hQ using fun U ↦ (T U U).1
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (LinearMap.mem_ker.1 hc)
  obtain ⟨F, hF, hFw⟩ := hw
  obtain ⟨h, hh⟩ := H1.mk_eq_mk.1
    (show H1.mk _ ((redMor hI hk s₀).coef.pullbackOneCocycle f) = H1.mk _ F.1 from hF.symm)
  let ΦU : ∀ U : AffOp X₀, S.thickObj hI U ⟶ S'.thickObj hI U := fun U ↦
    S.thickHom S' hI (𝟙 U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) fun b ↦
      (Φ.red U b).trans (mp_id (OAff s₀) U (S.p U b)).symm
  change H1.mk _ ((S'.coef hI).pullbackOneCocycle f) = -H1.mk _ z
  rw [← map_neg, H1.mk_eq_mk]
  refine ⟨fun U ↦ Φ.φ U (g U) + ev f (ΦU U), ?_⟩
  funext U V a
  let α : S.thickObj hI U ⟶ S'.thickObj hI V := ΦU U ≫ (S'.thick hI).map a
  let β : S.thickObj hI U ⟶ S'.thickObj hI V := (S.thick hI).map a ≫ ΦU V
  have hθ : IsTheta I (S.p U) α.φ β.φ (θ U V a) := hΘ U V a
  have tay := (T U V).2 (Q U) (hQ U) α β (θ U V a) hθ f
  rw [connForm_sub_eq hI hk hC S Q hQ f g hg F h hh U, map_add (f := _)] at tay
  erw [hθ.der (g U)] at tay
  have hw' : connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) = w.1 U := by
    rw [← hFw, cmpForm_apply]
  rw [hw', ← hz] at tay
  have E1 : ev f α = mp S'.F a (ev f (ΦU U)) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) := ev_comp f _ _
  have E2 : ev f β = Φ.φ V (ev f ((S.thick hI).map a)) + ev f (ΦU V) := ev_comp f _ _
  have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
    have := congrArg (fun q ↦ q U V a) hg
    simp only [amitsur_d0_apply] at this
    exact this.symm
  rw [h3, map_sub] at E2
  have E3 : α.φ (g U) = mp S'.F a (Φ.φ U (g U)) := rfl
  have E4 : β.φ (g U) = Φ.φ V (mp S.F a (g U)) := rfl
  erw [E3, E4] at tay
  change Φ.φ V (g V) + ev f (ΦU V) - mp S'.F a (Φ.φ U (g U) + ev f (ΦU U)) =
    @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) - -z.1 U V a
  rw [map_add (f := _)]
  have key : ∀ x y z' p q r s t u : S'.F.obj V, x - y = z' + (p - q) → y = r + s → x = t - q + u →
      t + u - (p + r) = s - -z' := by
    intro x y z' p q r s t u h₁ h₂ h₃
    linear_combination h₁ + h₂ - h₃
  exact key _ _ _ _ _ _ _ _ _ tay E1 E2

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem ev_eq_fv_of_triv {R : Type} [CommRing R] {X : Over (Sp R)} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (x : Pt X D) (x' : Pt X D')
    (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x') (h : ∀ r : D, a.φ r = φ r) :
    spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  have e : spOver φ ≫ x = x' := by
    have h0 : a.φ₀ = (φ : D →+* D') := RingHom.ext fun r ↦ (a.comm r).trans (h r)
    have hp := a.pt
    rw [h0] at hp
    exact Over.OverMorphism.ext hp
  subst x'
  refine ⟨rfl, ?_⟩
  have ha : a = trivMap φ x := Thick.Hom.ext' (AlgHom.ext h)
  exact congrArg (ev f) ha

theorem fv_isCoc_and_ev_eq :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))),
      IsCoc (whole X) (fv f) ∧
        ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
          (x : Pt X D) (x' : Pt X D') (φ : D →ₐ[R] D') (a : trivAt x ⟶ trivAt x'),
          (∀ r : D, a.φ r = φ r) → spOver φ ≫ x = x' ∧ ev f a = fv f D D' φ x := by
  intro R _ X f
  refine ⟨?_, fun D _ _ D' _ _ x x' φ a h ↦ ev_eq_fv_of_triv f D D' x x' φ a h⟩
  intro D _ _ D' _ _ D'' _ _ φ ψ x _
  let y : Pt X D' := spOver φ ≫ x
  let z : Pt X D'' := spOver ψ ≫ y
  have h := (ev_eq_fv_of_triv f D D'' x z (ψ.comp φ)
    (trivMap φ x ≫ trivMap ψ y) (fun _ ↦ rfl)).2
  exact h.symm.trans (ev_comp f (trivMap φ x) (trivMap ψ y))

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorCenterProperLift
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Discrepancy.DivOver

theorem exists_through_of_isProper : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → IsProper s → ∀ (E' : DivOver (s ≫ p)) (E : DivOver p), DivOver.Over s E' E → ∀ x : X, E.Through x → ∃ y : Y, s y = x ∧ E'.Through y := by
  intro k _ X Y _ _ p s _ _ hprop E' E hOver x hx
  haveI := hprop
  have hmem : ∀ a : X.presheaf.stalk x,
      functionFieldMap s (algebraMap _ X.functionField a) ∈ E'.ring :=
    fun a => (hOver _).1 (hx _ ⟨a, rfl⟩)
  let ψ : X.presheaf.stalk x →+* E'.ring :=
    ((functionFieldMap s).comp (algebraMap _ X.functionField)).codRestrict E'.ring.toSubring hmem
  have hc : genericFieldPoint Y ≫ s = specAlgebraMap E'.ring Y.functionField ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) := by
    rw [← specMap_functionFieldMap, ← specAlgebraMap_fromSpecStalk x]
    simp only [specAlgebraMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  obtain ⟨b, hb1, hb2⟩ := exists_valuativeExtension s _ (genericFieldPoint Y) hc
  have hdom : DominatesStalk E'.ring (b (IsLocalRing.closedPoint E'.ring)) :=
    dominatesStalk_iff_exists_hom.mpr ⟨b, hb1, rfl⟩
  have hw : E'.Through (b (IsLocalRing.closedPoint E'.ring)) := by
    rintro f ⟨c, rfl⟩
    exact hdom.1 c
  have hz : s (b (IsLocalRing.closedPoint E'.ring)) ⤳ x := by
    have e : s (b (IsLocalRing.closedPoint E'.ring)) = X.fromSpecStalk x
        (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring)) := by
      have := congrArg (fun l : Spec (CommRingCat.of E'.ring) ⟶ X =>
        l (IsLocalRing.closedPoint E'.ring)) hb2
      exact this
    rw [e]
    have := (IsLocalRing.specializes_closedPoint
      (Spec.map (CommRingCat.ofHom ψ) (IsLocalRing.closedPoint E'.ring))).map
        (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  obtain ⟨y, hwy, hy⟩ := s.isClosedMap.specializingMap hz
  exact ⟨y, hy, hw.of_specializes hwy⟩

end GlobalTheory.Discrepancy.DivOver
end
end

