module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsMulMulConjTransposeEqOne
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.ExistsPrimeAbsNormOfHasDirichletDensity
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0487
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0319
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIso

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestriction
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem res_defect : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (V U : Scheme.{0}) (g : V ⟶ U) (v : (Γ(U, ⊤))ˣ),
    IsUnit (Q : Γ(U, ⊤)) → Sec.res g (GlobalTheory.EtC.RedChern.defect Q q U v) =
      GlobalTheory.EtC.RedChern.defect Q q V (Units.map g.appTop.hom.toMonoidHom v) := by
  intro Q q _ hqQ V U g v hQ
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact NeZero.ne Q (zero_dvd_iff.mp hqQ)
  haveI : NeZero q := ⟨hq0⟩
  have hqU : IsUnit (q : Γ(U, ⊤)) := by
    obtain ⟨k, hk⟩ := hqQ
    rw [hk, Nat.cast_mul] at hQ
    exact isUnit_of_mul_isUnit_left hQ
  unfold defect
  rw [Sec.res, map_sub]
  change Sec.res g _ - Sec.res g _ = _
  rw [(redMap Q q 1).nat g 0, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).1 V U g v hQ, (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).1 V U g _ hqU, map_pow]

end GlobalTheory.EtC.RedChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplaceIntegralEntireBoundedInVerticalStripsStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips : ∀ {α : Type} [MeasurableSpace α] (μ : MeasureTheory.Measure α) (ℓ : α → ℝ) (g : α → ℂ), Measurable ℓ → MeasureTheory.AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, 0 ≤ ℓ x) → (∀ σ : ℝ, MeasureTheory.Integrable (fun x => ‖g x‖ * Real.exp (σ * ℓ x)) μ) → Differentiable ℂ (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips (fun s : ℂ => ∫ x, g x * Complex.exp (s * (ℓ x : ℂ)) ∂μ) := by
  first | exact @GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | exact GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips | (intros; apply GlobalTheory.LaplaceStrip.laplace_entire_boundedInStrips <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletionStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_congruence_iff_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (β : GL (Fin n) E), 1 ≤ M → (∀ v, fv F v ∈ hat F (Λ : Set (Fin n → E)) ↔ v ∈ Λ) → (((∀ x, x ∈ Λ ↔ (β : Matrix (Fin n) (Fin n) E) *ᵥ x ∈ Λ) ∧ ∀ x ∈ Λ, ∃ y ∈ Λ, (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ↔ ((∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F (Λ : Set (Fin n → E)), ∃ y ∈ hat F (Λ : Set (Fin n → E)), ratM F (β : Matrix (Fin n) (Fin n) E) *ᵥ y = x)) := by
  first | exact @GlobalTheory.LocGlob.stab_cong_iff_hat | exact GlobalTheory.LocGlob.stab_cong_iff_hat | (intros; apply GlobalTheory.LocGlob.stab_cong_iff_hat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralTransportHermitianFrameChartMeasureStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ), X.p0 = X'.p0 → ∀ (φ : Frame X'.Ψ r → ℝ≥0∞), Measurable φ → ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) = ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := by
  first | exact @GlobalTheory.FlagTransport.lintegral_trF_cpt | exact GlobalTheory.FlagTransport.lintegral_trF_cpt | (intros; apply GlobalTheory.FlagTransport.lintegral_trF_cpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.EulerLocVol

noncomputable def invPowHom (i : ℕ) : ℕ →* ℝ where
  toFun n := ((n : ℝ) ^ i)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

theorem inv_zeta_le_prod_primes : ∀ (i : ℕ), 2 ≤ i → ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
    (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := by
  intro i hi P hP
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hs' : Summable (invPowHom i) := by
    have := Real.summable_one_div_nat_pow.2 (by omega : 1 < i)
    simpa [invPowHom] using this
  have hlt : ∀ {p : ℕ}, p.Prime → ‖invPowHom i p‖ < 1 := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast hp.one_lt) (by omega)
    simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk, norm_inv, norm_pow, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ h1
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hlt P).2
  have hfilt : P.filter Nat.Prime = P := Finset.filter_true_of_mem hP
  rw [hfilt] at hE
  have hfac : ∀ p ∈ P, 0 < 1 - ((p : ℝ) ^ i)⁻¹ := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ i := one_lt_pow₀ (by exact_mod_cast (hP p hp).one_lt) (by omega)
    exact sub_pos.2 (inv_lt_one_of_one_lt₀ h1)
  have hpos : 0 < ∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹) := Finset.prod_pos hfac
  have hle : ∏ p ∈ P, (1 - invPowHom i p)⁻¹ ≤ ∑' n : ℕ, invPowHom i n := by
    rw [← hE.tsum_eq]
    exact Summable.tsum_subtype_le (⇑(invPowHom i)) _ (fun n => by change 0 ≤ ((n : ℝ) ^ i)⁻¹; positivity) hs'
  have hz : ∑' n : ℕ, invPowHom i n = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    rw [hs'.tsum_eq_zero_add]
    simp [invPowHom, show i ≠ 0 by omega]
  rw [hz, Finset.prod_inv_distrib] at hle
  simp only [invPowHom, MonoidHom.coe_mk, OneHom.coe_mk] at hle
  calc (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i)⁻¹ ≤ ((∏ p ∈ P, (1 - ((p : ℝ) ^ i)⁻¹))⁻¹)⁻¹ :=
        inv_anti₀ (inv_pos.2 hpos) hle
    _ = _ := inv_inv _

theorem le_locFactor_of_not_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), 1 ≤ r →
    ¬ (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime →
    ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) ≤ locFactor E r v := by
  intro E _ _ _ r v hr hnp
  let _ : Field (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hc : Nat.card (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h := GlobalTheory.FiniteOrders.card_specialLinearGroup hc (Fin r) (Fintype.card_fin r) hr
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  unfold locFactor resOrder
  rw [if_neg hnp]
  have h' : (Nat.card (Matrix.SpecialLinearGroup (Fin r) (𝓞 (maximalRealSubfield E) ⧸ v.asIdeal)) : ℝ) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (r ^ 2 - 1) * ∏ i ∈ Finset.Icc 2 r, (1 - ((Ideal.absNorm v.asIdeal : ℝ) ^ i)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) h
    push_cast at this
    exact this
  rw [h', mul_div_cancel_left₀ _ (pow_ne_zero _ hq.ne')]

theorem tprod_locFactor_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ), 2 ≤ r →
    Multipliable (locFactor E r) → 0 < ∏' v, locFactor E r v ∧
      (∏' v, locFactor E r v)⁻¹ ≤ (∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E := by
  intro E _ _ _ r hr hm
  let g : ℝ → ℝ := fun x => ∏ i ∈ Finset.Icc 2 r, (1 - (x ^ i)⁻¹)
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZdef
  have hzeta : ∀ i ∈ Finset.Icc 2 r, 1 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i := by
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs.le_tsum 0 (fun j _ => by positivity)
    simpa using this
  have hZ : 0 < Z := Finset.prod_pos fun i hi => lt_of_lt_of_le one_pos (hzeta i hi)
  have hf : fdeg E = Module.finrank ℚ (maximalRealSubfield E) := by
    have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
      Algebra.IsQuadraticExtension.finrank_eq_two _ _
    unfold fdeg
    rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E), h2]
    omega
  have g_nonneg : ∀ x : ℝ, 1 ≤ x → 0 ≤ g x := fun x hx =>
    Finset.prod_nonneg fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx))
  have g_le_one : ∀ x : ℝ, 1 ≤ x → g x ≤ 1 := fun x hx =>
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_self _ (by positivity)
  have g_mono : ∀ x y : ℝ, 1 ≤ x → x ≤ y → g x ≤ g y := fun x y hx hxy =>
    Finset.prod_le_prod₀ (fun i _ => sub_nonneg.2 (inv_le_one_of_one_le₀ (one_le_pow₀ hx)))
      fun i _ => sub_le_sub_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by linarith) hxy i)) _
  have hloc : ∀ v, g (Ideal.absNorm v.asIdeal) ≤ locFactor E r v := by
    intro v
    by_cases hp : (v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))).IsPrime
    · exact GlobalTheory.T.local_factor_lower_bound E r v (by omega) hp
    · exact le_locFactor_of_not_prime E r v (by omega) hp
  let pv : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ℕ := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow
  have hN : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      (pv v).Prime ∧ pv v ≤ Ideal.absNorm v.asIdeal := by
    intro v
    have hp := ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime v
    obtain ⟨f, hfv⟩ := ReciprocityTheory.Neutral.Bridge.absNorm_eq_ratPrimeBelow_pow v
    have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
    have hf0 : f ≠ 0 := by rintro rfl; rw [pow_zero] at hfv; exact h1 hfv
    refine ⟨hp, ?_⟩
    rw [hfv]
    exact Nat.le_self_pow hf0 _
  have key : ∀ s : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
      (Z ^ fdeg E)⁻¹ ≤ ∏ v ∈ s, locFactor E r v := by
    intro s
    set T := s.image pv
    have hp1 : ∀ p ∈ T, (1 : ℝ) ≤ p := by
      intro p hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact_mod_cast (hN v).1.one_lt.le
    have s1 : ∏ v ∈ s, g (pv v) ≤ ∏ v ∈ s, locFactor E r v := by
      refine Finset.prod_le_prod₀ (fun v _ => g_nonneg _ (by exact_mod_cast (hN v).1.one_lt.le))
        fun v _ => (g_mono _ _ (by exact_mod_cast (hN v).1.one_lt.le) (by exact_mod_cast (hN v).2)).trans (hloc v)
    have s2 : ∏ v ∈ s, g (pv v) = ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      rw [Finset.prod_comp (fun p : ℕ => g p) pv]
    have s3 : ∏ p ∈ T, g p ^ fdeg E ≤ ∏ p ∈ T, g p ^ (s.filter fun v => pv v = p).card := by
      refine Finset.prod_le_prod₀ (fun p hp => pow_nonneg (g_nonneg _ (hp1 p hp)) _) fun p hp => ?_
      refine pow_le_pow_of_le_one (g_nonneg _ (hp1 p hp)) (g_le_one _ (hp1 p hp)) ?_
      rw [hf]
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le id Function.injective_id s (pv v) (hN v).1
    have s4 : Z⁻¹ ≤ ∏ p ∈ T, g p := by
      rw [Finset.prod_comm, hZdef, ← Finset.prod_inv_distrib]
      refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i hi => ?_
      refine inv_zeta_le_prod_primes i (Finset.mem_Icc.1 hi).1 T fun p hp => ?_
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
      exact (hN v).1
    calc (Z ^ fdeg E)⁻¹ = (Z⁻¹) ^ fdeg E := (inv_pow Z _).symm
      _ ≤ (∏ p ∈ T, g p) ^ fdeg E := pow_le_pow_left₀ (by positivity) s4 _
      _ = ∏ p ∈ T, g p ^ fdeg E := (Finset.prod_pow _ _ _).symm
      _ ≤ _ := s3
      _ = _ := s2.symm
      _ ≤ _ := s1
  have hle : (Z ^ fdeg E)⁻¹ ≤ ∏' v, locFactor E r v :=
    ge_of_tendsto hm.hasProd (Filter.Eventually.of_forall key)
  have hpos : 0 < (Z ^ fdeg E)⁻¹ := by positivity
  refine ⟨hpos.trans_le hle, ?_⟩
  calc (∏' v, locFactor E r v)⁻¹ ≤ ((Z ^ fdeg E)⁻¹)⁻¹ := inv_anti₀ hpos hle
    _ = Z ^ fdeg E := inv_inv _

end GlobalTheory.EulerLocVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.MapComapIso

theorem map_eq_comap_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by
  apply le_antisymm
  · calc K.map f = (K.map f).comap (inv f ≫ f) := by simp
      _ = ((K.map f).comap f).comap (inv f) := by rw [Scheme.IdealSheafData.comap_comp]
      _ ≤ K.comap (inv f) :=
          Scheme.IdealSheafData.comap_mono (inv f) ((Scheme.IdealSheafData.map_gc f).l_u_le K)
  · calc K.comap (inv f) ≤ ((K.comap (inv f)).comap f).map f :=
          (Scheme.IdealSheafData.map_gc f).le_u_l _
      _ = (K.comap (f ≫ inv f)).map f := by rw [Scheme.IdealSheafData.comap_comp]
      _ = K.map f := by simp

theorem map_comap_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by
  rw [map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp]
  simp

theorem map_comap_ideal_eq_of_isIso_restrict :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by
  intro W W' π U hq hiso τ V hVU
  have hpb := (isPullback_morphismRestrict π U).flip
  have hres : ((τ.comap π).map π).comap U.ι = τ.comap U.ι := by
    rw [_root_.GlobalTheory.FlatBaseChangeIdeal.map_comap_flat W W' U (π ⁻¹ᵁ U) π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) hpb inferInstance hq (τ.comap π),
      ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      map_comap_of_isIso]
  have hle : V.1 ≤ Scheme.Hom.opensRange U.ι := by rw [Scheme.Opens.opensRange_ι]; exact hVU
  let V' : U.toScheme.affineOpens := ⟨U.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion U.ι hle⟩
  have himg : (⟨U.ι ''ᵁ V'.1, (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).2 V'.2⟩ :
      W.affineOpens) = V := by
    apply Subtype.ext
    change U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion ((τ.comap π).map π) U.ι V'
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion τ U.ι V'
  rw [hres, h2] at h1
  have h3 := Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso U.ι V'.1).inv).2 h1
  have h4 : ∀ A B : W.affineOpens, A = B →
      ((τ.comap π).map π).ideal A = τ.ideal A → ((τ.comap π).map π).ideal B = τ.ideal B := by
    rintro A B rfl h; exact h
  exact h4 _ V himg h3.symm

end GlobalTheory.MapComapIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisExactEtale
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section
namespace GlobalTheory.EtC.ExcisionNat

abbrev C (R : Type) [CommRing R] (B : Type) [CommRing B] : Cx R := (chains R).obj (sp B)

abbrev Cm (R : Type) [CommRing R] {B B' : Type} [CommRing B] [CommRing B'] (g : B →+* B') : C R B' ⟶ C R B :=
  (chains R).map (spMap g)

theorem spMap_comp {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B) (g : B →+* B') :
    spMap g ≫ spMap h = spMap (g.comp h) := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, CommRingCat.ofHom_comp]

theorem Cm_comp (R : Type) [CommRing R] {B₀ B B' : Type} [CommRing B₀] [CommRing B] [CommRing B'] (h : B₀ →+* B)
    (g : B →+* B') : Cm R g ≫ Cm R h = Cm R (g.comp h) := by
  rw [← Functor.map_comp, spMap_comp]

theorem awayMap_comp_algebraMap {A A' : Type} [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (Localization.awayMap (algebraMap A A') f).comp (algebraMap A (Localization.Away f)) =
      (algebraMap A' (Localization.Away (algebraMap A A' f))).comp (algebraMap A A') :=
  IsLocalization.map_comp _

theorem awayHom_comp_awayMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (Localization.awayMap (algebraMap A A') f) = Localization.awayMap (algebraMap A A'') f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  rw [RingHom.comp_assoc, awayMap_comp_algebraMap, ← RingHom.comp_assoc, awayHom_comp_algebraMap,
    awayMap_comp_algebraMap, RingHom.comp_assoc]
  congr 1
  exact RingHom.ext fun a => φ.commutes a

def exSC (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    ShortComplex (Cx R) :=
  ShortComplex.mk
    (biprod.lift (Cm R (Localization.awayMap (algebraMap A A') f))
      (-Cm R (algebraMap A' (Localization.Away (algebraMap A A' f)))))
    (biprod.desc (Cm R (algebraMap A (Localization.Away f))) (Cm R (algebraMap A A')))
    (by rw [biprod.lift_desc, Preadditive.neg_comp, Cm_comp, Cm_comp, awayMap_comp_algebraMap, add_neg_cancel])

theorem exSC_shortExact (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']
    [Algebra.Etale A A'] (f : A) (hN : IsNbhd A A' f) : (exSC R A A' f).ShortExact := by
  refine GlobalTheory.T.chain_complex_exact_square R _ _ _ _ ?_ (exSC R A A' f).zero (GlobalTheory.T.freeEtaleSheaf_excision_shortExact R A A' f hN ?_)
  all_goals
    simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      awayMap_comp_algebraMap, add_neg_cancel]

def exMap (R : Type) [CommRing R] {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) : exSC R A A'' f ⟶ exSC R A A' f where
  τ₁ := Cm R (awayHom φ f)
  τ₂ := biprod.map (𝟙 _) (Cm R φ.toRingHom)
  τ₃ := 𝟙 _
  comm₁₂ := by
    apply biprod.hom_ext
    · simp only [exSC, Category.assoc, biprod.lift_fst, biprod.map_fst, Category.comp_id, Cm_comp, awayHom_comp_awayMap]
    · simp only [exSC]
      rw [Category.assoc, Category.assoc, biprod.lift_snd, biprod.map_snd, ← Category.assoc, biprod.lift_snd,
        Preadditive.comp_neg, Preadditive.neg_comp, Cm_comp, Cm_comp, awayHom_comp_algebraMap]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [exSC, biprod.inl_map_assoc, Category.id_comp, biprod.inl_desc, Category.comp_id]
    · simp only [exSC, biprod.inr_map_assoc, biprod.inr_desc, Category.comp_id, Cm_comp]
      congr 2
      exact RingHom.ext fun a => φ.commutes a

theorem excision_natural : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), IsNbhd A A' f → ∀ n i : ℤ, ∃ δ : Ht q (sp (Localization.Away (algebraMap A A' f))) n i →+ Ht q (sp A) (n + 1) i, Function.Exact δ (fun x : Ht q (sp A) (n + 1) i => (pull _ (spMap (algebraMap A (Localization.Away f))) _ _ x, pull _ (spMap (algebraMap A A')) _ _ x)) ∧ ∀ (A'' : Type) [CommRing A''] [Algebra A A''] [Algebra.Etale A A''] (φ : A' →ₐ[A] A''), IsNbhd A A'' f → ∀ z, pull _ (spMap (awayHom φ f)) _ _ z = 0 → δ z = 0 := by
  intro q A A' _ _ _ _ f hN n i
  have hI : ∀ k, Injective ((res (ZMod q) (tw q i)).X k) := fun k =>
    inferInstanceAs (Injective ((injectiveResolution (tw q i)).cochainComplex.X k))
  obtain ⟨d, hex, hnat⟩ := longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) hI
  have hS := exSC_shortExact (ZMod q) A A' f hN
  refine ⟨d (exSC (ZMod q) A A' f) hS n, ?_, ?_⟩
  · intro x
    refine Iff.trans ?_ ((hex _ hS n).2.2 x)
    have hb := (cpull_biprod_bijective (ZMod q) (C (ZMod q) (Localization.Away f)) (C (ZMod q) A')
      (res (ZMod q) (tw q i)) (n + 1)).1
    have e1 : pull (ZMod q) (spMap (algebraMap A (Localization.Away f))) (tw q i) (n + 1) x =
        cpull (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inl : C (ZMod q) (Localization.Away f) ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A (Localization.Away f)) := biprod.inl_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    have e2 : pull (ZMod q) (spMap (algebraMap A A')) (tw q i) (n + 1) x =
        cpull (biprod.inr : C (ZMod q) A' ⟶ _) (res (ZMod q) (tw q i)) (n + 1)
          (cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x) := by
      have hc : (biprod.inr : C (ZMod q) A' ⟶ C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') ≫ (exSC (ZMod q) A A' f).g = Cm (ZMod q) (algebraMap A A') := biprod.inr_desc _ _
      refine Eq.trans ?_ ((ZcFun.main (ZMod q)).2.1 _ (exSC (ZMod q) A A' f).g _ _ x)
      exact (congrArg (fun m => cpull m (res (ZMod q) (tw q i)) (n + 1) x) hc).symm
    change (_, _) = ((0, 0) : _ × _) ↔ _
    rw [e1, e2]
    obtain ⟨y, hy⟩ : ∃ y : CohomologyClass (C (ZMod q) (Localization.Away f) ⊞ C (ZMod q) A') (res (ZMod q) (tw q i)) (n + 1),
      y = cpull (exSC (ZMod q) A A' f).g (res (ZMod q) (tw q i)) (n + 1) x := ⟨_, rfl⟩
    rw [← hy]
    constructor
    · intro h
      apply hb
      dsimp only
      rw [h]
      exact Prod.ext (map_zero _).symm (map_zero _).symm
    · intro h
      rw [h]
      exact Prod.ext (map_zero _) (map_zero _)
  · intro A'' _ _ _ φ hN'' z hz
    have hS'' := exSC_shortExact (ZMod q) A A'' f hN''
    have h := hnat _ _ hS'' hS (exMap (ZMod q) φ f) n z
    have hz' : cpull (exMap (ZMod q) φ f).τ₁ (res (ZMod q) (tw q i)) n z = 0 := hz
    rw [hz', map_zero] at h
    have hid : cpull (exMap (ZMod q) φ f).τ₃ (res (ZMod q) (tw q i)) (n + 1) (d _ hS n z) = d _ hS n z :=
      ZcFun.cpull_id _ _ _ _
    rw [hid] at h
    exact h

end GlobalTheory.EtC.ExcisionNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MellinIntegralSplitFunctionalEquationStatement
section
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mellin_integral_split_functional_equation : ∀ (I : Type) [Fintype I] [Nonempty I] (p : (I → ℝ) → ℝ) (θ θ' : (I → ℝ) → ℂ) (κ s : ℂ), (∀ y, θ y = κ * (Real.exp (-∑ i, y i) : ℂ) * θ' (-y)) → MeasureTheory.Integrable (fun y => (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → MeasureTheory.Integrable (fun y => (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ))) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) → ∫ y, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) = (∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p y : ℂ) * θ y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ))) + κ * ∫ y in {y : I → ℝ | 0 ≤ ∑ i, y i}, (p (-y) : ℂ) * θ' y * Complex.exp ((1 - s) * ((∑ i, y i : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.mellinSplit_neg | exact GlobalTheory.mellinSplit_neg | (intros; apply GlobalTheory.mellinSplit_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEndLatticeOfTraceDualStatement
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_end_lattice_of_trace_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E), SelfDualLat G Λ → (∀ Z ∈ endLat Λ, IsIntegral ℤ (Y * Z).trace) → Y ∈ endLat Λ := by
  first | exact @GlobalTheory.LieDisc.mem_endLat_of_trace_integral | exact GlobalTheory.LieDisc.mem_endLat_of_trace_integral | (intros; apply GlobalTheory.LieDisc.mem_endLat_of_trace_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPFlatStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mulP_flat' : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ :=
    GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  let B := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1)
  let f : G.A n →ₐ[R] B := AlgHom.codRestrict
    (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B (fun a => G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => GlobalTheory.PDivGroup.Test.mulP_injective G n
      (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨a, ha⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨a, Subtype.ext ha⟩
  have hB : RingHom.Flat (algebraMap B (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat : RingHom.Flat (f : G.A n →+* B) := RingHom.Flat.of_bijective hf
  convert RingHom.Flat.comp hflat hB using 1
  exact RingHom.ext fun a => rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_complex_preserves_quasiIso : ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u := by
  first | (exact @GlobalTheory.EtC.tensor_quasiIso) | (exact GlobalTheory.EtC.tensor_quasiIso) | (intros; apply GlobalTheory.EtC.tensor_quasiIso  <;> assumption)
end

