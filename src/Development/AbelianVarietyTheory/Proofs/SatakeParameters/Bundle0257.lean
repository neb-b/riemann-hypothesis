module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicLatticeSmulMemOfAgreeAwayFromPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DeterminantCharacterUnitaryApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Formalism.LocalToGlobal.Columns.KOneCharacterTrivialNearOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0013
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
section
noncomputable section

namespace GlobalTheory.LiftTypePrime.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta

section Integral

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem intAt_iff {x : ℂ} : IntAt lam x ↔ ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ ≤ 1 := by
  unfold IntAt lamC
  exact ⟨fun ⟨h, h1⟩ => ⟨h, by rwa [dite_eq_left h] at h1⟩, fun ⟨h, h1⟩ => ⟨h, by rwa [dite_eq_left h]⟩⟩

theorem intAt_mul {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x * y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨mul_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ * ⟨y, h'⟩)‖ ≤ 1
  rw [map_mul, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem intAt_add {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x + y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨add_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ + ⟨y, h'⟩)‖ ≤ 1
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem intAt_of_isIntegral {x : ℂ} (hx : IsIntegral ℤ x) : IntAt lam x := by
  have h : x ∈ Qbar := mem_algebraicClosure_iff'.2 hx.tower_top
  refine intAt_iff.2 ⟨h, ?_⟩
  have h1 : IsIntegral ℤ (⟨x, h⟩ : Qbar) :=
    (isIntegral_algHom_iff ((algebraMap Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx
  exact norm_le_one_of_isIntegral (map_isIntegral_int lam h1)

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntAt lam (f i)) : IntAt lam (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt lam) (fun _ _ => intAt_add) (intAt_of_isIntegral isIntegral_zero) h

end Integral

theorem isIntegral_exp (k : ℤ) (x : ℝ) (n : ℕ) (hn : 0 < n) (m : ℤ) (h : (n : ℝ) * x = m) :
    IsIntegral ℤ (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ))) := by
  have h' : (n : ℂ) * (x : ℂ) = m := by exact_mod_cast h
  refine IsIntegral.of_pow (n := 2 * n) (by omega) ?_
  rw [← Complex.exp_nat_mul]
  have : ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ)) =
      ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (2 * (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) * h'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
  exact isIntegral_one

variable {D : D7} {N N' : ℕ}

theorem taylor_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem applyAt0_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (P : MvPolynomial (Idx D N N') ℂ) :
    applyAt0 D P (fun z => ∑ i ∈ s, c i * f i z) = ∑ i ∈ s, c i * applyAt0 D P (f i) := by
  unfold applyAt0
  simp only [taylor_sum s c f hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring

end GlobalTheory.LiftTypePrime.Jets

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta Jets

end GlobalTheory.LiftTypePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeEqAwayFromPrimeOfAgreeOffPlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem sameOff_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} {x y : GL (Fin N) (AfE F E)} (h : SameOff w x y) : SameOff w y x :=
  fun w' hw => (h w' hw).symm


set_option maxHeartbeats 1000000 in
theorem normConj_mem_pow : ∀ (D : D7) (n p : ℕ) (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (m : ℕ) (a b : 𝓞 D.host.E), (b : D.host.E) = D.host.conj (a : D.host.E) → a ∈ P.asIdeal ^ m → ∃ c : 𝓞 D.host.F, c ∈ (A.pl v).1.asIdeal ^ m ∧ algebraMap D.host.F D.host.E (c : D.host.F) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
  intro D n p G A hInt hSpl v P hP m a b hb ha

  let T : ℕ → Ideal (𝓞 D.host.E) := fun k =>
    { carrier := {x | ∃ y : G.P.W v, A.iw v (x : D.host.E) = algebraMap _ _ y ∧ (p : G.P.W v) ^ k ∣ y}
      add_mem' := by
        rintro x x' ⟨y, hy, hdy⟩ ⟨y', hy', hdy'⟩
        exact ⟨y + y', by simp [hy, hy'], dvd_add hdy hdy'⟩
      zero_mem' := ⟨0, by simp, dvd_zero _⟩
      smul_mem' := by
        rintro r x ⟨y, hy, hdy⟩
        obtain ⟨yr, hyr, -⟩ := hP r
        exact ⟨yr * y, by simp [hy, hyr], dvd_mul_of_dvd_right hdy _⟩ }
  have hT : ∀ k, P.asIdeal ^ k ≤ T k := by
    intro k
    induction k with
    | zero =>
      intro x _
      obtain ⟨y, hy, -⟩ := hP x
      exact ⟨y, hy, by simp⟩
    | succ k ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun x hx z hz => ?_
      obtain ⟨y, hy, hdy⟩ := ih hx
      obtain ⟨yz, hyz, hdz⟩ := hP z
      exact ⟨y * yz, by simp [hy, hyz], by rw [pow_succ]; exact mul_dvd_mul hdy (hdz.1 hz)⟩
  obtain ⟨ya, hya, hda⟩ := hT m ha
  obtain ⟨yb, hyb, -⟩ := hP b
  have hcc : ∀ x : D.host.E, D.host.φ₀ (D.host.conj x) = starRingEnd ℂ (D.host.φ₀ x) :=
    fun x => D.host.conjE_apply D.host.φ₀ x
  have hcc2 : ∀ x : D.host.E, D.host.conj (D.host.conj x) = x := fun x =>
    D.host.φ₀.injective (by rw [hcc, hcc, Complex.conj_conj])
  have hfix : D.host.conj (((a * b : 𝓞 D.host.E) : D.host.E)) = ((a * b : 𝓞 D.host.E) : D.host.E) := by
    show D.host.conj ((a : D.host.E) * (b : D.host.E)) = (a : D.host.E) * (b : D.host.E)
    rw [map_mul, hb, hcc2, mul_comm]
  have hF : ((a * b : 𝓞 D.host.E) : D.host.E) ∈ D.host.F :=
    (D.host.conjE_mem_hostF_iff _).2 hfix
  have hint : IsIntegral ℤ (⟨_, hF⟩ : D.host.F) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ D.host.F D.host.E) (algebraMap D.host.F D.host.E).injective).1
      (a * b).isIntegral_coe
  let c : 𝓞 D.host.F := ⟨⟨_, hF⟩, hint⟩
  refine ⟨c, ?_, rfl⟩
  obtain ⟨t, ht⟩ := hda
  have hiw : A.iw v ((a * b : 𝓞 D.host.E) : D.host.E) = (p : G.P.Qq v) ^ m * algebraMap _ _ (t * yb) := by
    show A.iw v ((a : D.host.E) * (b : D.host.E)) = _
    rw [map_mul, hya, hyb, ht]
    simp only [map_mul, map_pow, map_natCast]
    ring
  have hph : A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) =
      algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
    have h1 : (inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E) =
        (1 : D.host.E) ⊗ₜ[D.host.F] algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F) := by
      show (algebraMap D.host.F D.host.E (c : D.host.F)) ⊗ₜ[D.host.F] (1 : (A.pl v).1.adicCompletion D.host.F) = _
      rw [← Algebra.TensorProduct.algebraMap_apply (R := D.host.F) (S := D.host.F), Algebra.TensorProduct.algebraMap_apply']
    show ((A.spl v) ((inclE (F := D.host.F) ((A.pl v).1.adicCompletion D.host.F)) ((a * b : 𝓞 D.host.E) : D.host.E))).1 = _
    refine (congrArg (fun z => ((A.spl v) z).1) h1).trans ?_
    simp only [hSpl v]
  have heQ : A.eQ v (A.iw v ((a * b : 𝓞 D.host.E) : D.host.E)) = A.phE v ((a * b : 𝓞 D.host.E) : D.host.E) := by
    simp [LocAt.iw]
  have hu : A.eQ v (algebraMap _ _ (t * yb)) ∈ (A.pl v).1.adicCompletionIntegers D.host.F :=
    (hInt v _).1 ⟨_, rfl⟩
  rw [hiw, map_mul, map_pow, map_natCast, hph] at heQ
  have hval : ∀ k : D.host.F, Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) k) =
      (A.pl v).1.valuation D.host.F k := by
    intro k
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (A.pl v).1 k
  have hp1 : Valued.v ((p : ℕ) : (A.pl v).1.adicCompletion D.host.F) ≤ WithZero.exp (-1 : ℤ) := by
    have h := (HeightOneSpectrum.intValuation_le_pow_iff_mem (A.pl v).1 ((p : ℕ) : 𝓞 D.host.F) 1).2
      (by simpa using (A.pl v).2)
    rw [← map_natCast (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F)), hval,
      ← map_natCast (algebraMap (𝓞 D.host.F) D.host.F), HeightOneSpectrum.valuation_of_algebraMap]
    simpa using h
  have hu' : Valued.v (A.eQ v (algebraMap _ _ (t * yb))) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hu
  have hv : Valued.v (algebraMap D.host.F ((A.pl v).1.adicCompletion D.host.F) (c : D.host.F)) ≤
      WithZero.exp (-(m : ℤ)) := by
    rw [← heQ, map_mul, map_pow]
    calc _ ≤ WithZero.exp (-1 : ℤ) ^ m * 1 := mul_le_mul' (pow_le_pow_left' hp1 m) hu'
      _ = WithZero.exp (-(m : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]
        congr 1
        simp
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F),
    ← hval]
  exact hv

theorem smul_latK_of_smul_latAd : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (x x' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) (c : 𝓞 E), (c : E) ∈ (algebraMap F E).range → (∀ y ∈ latAd x Lb, c • y ∈ latAd x' Lb) → (∀ y ∈ latAd x' Lb, c • y ∈ latAd x Lb) → ∀ z ∈ latK sp J a x Lb, c • z ∈ latK sp J a x' Lb := by
  intro R F E _ _ _ _ _ _ sp N J a x x' Lb c hc h1 h2
  obtain ⟨c0, hc0⟩ := hc
  have hsig : (sp.cm.sig : E →+* E) (c : E) = c := by
    rw [← hc0]; exact (sp.cm.sig).commutes c0
  have hsm : ∀ y : Fin N → E, c • y = (c : E) • y := fun y => rfl
  have hd : ∀ y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x Lb),
      c • y ∈ dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb) := by
    intro y hy z hz
    have key := hy _ (h2 z hz)
    have e1 : hform (sp.cm.sig : E →+* E) J z (c • y) = hform (sp.cm.sig : E →+* E) J (c • z) y := by
      rw [hsm, hsm]
      simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, hsig]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e1]; exact key
  have hc' : compan (sp := sp) J a (latAd x Lb) ≤
      (compan (sp := sp) J a (latAd x' Lb)).comap (LinearMap.lsmul (𝓞 E) (Fin N → E) c) := by
    unfold compan
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun r hr n hn => ?_)
    · exact Submodule.mem_sup_left (h1 y hy)
    · have hn' : c • n ∈ Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb)) := by
        have : Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x Lb)) ≤
            (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J (latAd x' Lb))).comap
              (LinearMap.lsmul (𝓞 E) (Fin N → E) c) :=
          Submodule.span_le.2 fun y hy => Submodule.subset_span (hd y hy)
        exact this hn
      rw [Submodule.mem_comap]
      show c • (r • n) ∈ _
      rw [smul_comm]
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hn')
  intro z hz
  unfold latK toStd at hz ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
  refine Submodule.mem_map.2 ⟨c • w, hc' hw, ?_⟩
  rw [LinearMap.map_smul]

theorem eqOff_latK_of_sameOff : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (n p : ℕ) [Fact p.Prime] (G : GAtP p) (A : LocAt D.host.F D.host.E n G), LocInt A → SplAlg A → ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf p (G.P.W v) (A.iw v) P → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) D.host.E) (a : 𝓞 D.host.E) (Lb : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Module.Finite (𝓞 D.host.E) Lb → Submodule.span D.host.E (Lb : Set (Fin N → D.host.E)) = ⊤ → ∀ x x' : GL (Fin N) (AfE D.host.F D.host.E), SameOff (A.pl v).1 x x' → GL3Theta.EqOff D P (latK D.sp J a x Lb) (latK D.sp J a x' Lb) := by
  intro D n p _ G A hInt hSpl v P hP N J a Lb hfin hspan x x' hoff
  obtain ⟨m1, h1⟩ := _root_.GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x x' hoff
  obtain ⟨m2, h2⟩ := _root_.GlobalTheory.TwV.Xc.latAd_smul_mem_of_sameOff D.host.F D.host.E N Lb hfin hspan (A.pl v).1 x' x (sameOff_symm _ hoff)
  refine ⟨max m1 m2, fun a' b hb ha => ?_⟩
  obtain ⟨c, hc, hcab⟩ := normConj_mem_pow D n p G A hInt hSpl v P hP (max m1 m2) a' b hb ha
  have hr : ((a' * b : 𝓞 D.host.E) : D.host.E) ∈ (algebraMap D.host.F D.host.E).range := ⟨_, hcab⟩
  have e1 : ∀ y ∈ latAd x Lb, (a' * b) • y ∈ latAd x' Lb := by
    intro y hy
    have := h1 c (Ideal.pow_le_pow_right (le_max_left _ _) hc) y hy
    rw [hcab] at this
    exact this
  have e2 : ∀ y ∈ latAd x' Lb, (a' * b) • y ∈ latAd x Lb := by
    intro y hy
    have := h2 c (Ideal.pow_le_pow_right (le_max_right _ _) hc) y hy
    rw [hcab] at this
    exact this
  exact ⟨smul_latK_of_smul_latAd D.sp J a x x' Lb _ hr e1 e2, smul_latK_of_smul_latAd D.sp J a x' x Lb _ hr e2 e1⟩

end GlobalTheory.TwV.Xc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumns
section
noncomputable section

namespace GlobalTheory.Pdv.UnStd

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_frame_mul {D : D7} {C : CharFrame D} (Dt : Formalism.L2.Host.DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n)
    (hord : ξ.OrderDvd n) (mt : ℕ → D.Dt →* ℂˣ)
    (h : ∀ (j : Fin D.R.m) a, Formalism.L2.Host.IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : Formalism.L2.Host.eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [Formalism.L2.Host.eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.Pdv.UnStd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv.UnStd

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

theorem mtType_stdO {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)}
    (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) : MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_frame_mul T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

end GlobalTheory.Pdv.UnStd


open GlobalTheory.Pdv.UnStd in
theorem GlobalTheory.Pdv.unUnit_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex t hs
  exact GlobalTheory.KerJ.unUnit_of_mtType _ L hT Gi Gl K Y cX ex t (fun u μ => mtType_stdO I hok hp l Z hs.O u μ)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatBackSeamLat
section
open NumberField

namespace GlobalTheory.LatticeBackSeam

theorem latBack_seam_lat : ∀ {D : Formalism.BasicNotions.D7} {X : Formalism.L2.Col.Fields} (s : Formalism.L2.Ker.Seam D X) {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers (Formalism.L2.Col.Fields.E X)) (Formalism.L2.Col.Sp (Formalism.L2.Col.Fields.E X) n)),
    GlobalTheory.TwU.latBack s (Formalism.L2.Ker.Seam.lat s N) = N := by
  intro D X s n N
  ext y
  rw [GlobalTheory.TwU.mem_latBack]
  constructor
  · intro hy
    have key : ∀ v ∈ Formalism.L2.Ker.Seam.lat s N, ∃ x ∈ N, (fun l => s.iE (x l)) = v := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        exact ⟨x, hx, rfl⟩
      | zero => exact ⟨0, N.zero_mem, by funext l; simp⟩
      | add v w _ _ hv hw =>
        obtain ⟨x, hx, rfl⟩ := hv
        obtain ⟨x', hx', rfl⟩ := hw
        exact ⟨x + x', N.add_mem hx hx', by funext l; simp⟩
      | smul r v _ hv =>
        obtain ⟨x, hx, rfl⟩ := hv
        refine ⟨(RingOfIntegers.mapRingEquiv s.iE).symm r • x, N.smul_mem _ hx, ?_⟩
        funext l
        simp [Algebra.smul_def, RingOfIntegers.mapRingEquiv_symm_apply]
    obtain ⟨x, hx, hxy⟩ := key _ hy
    have hxe : x = y := funext fun l => s.iE.injective (congrFun hxy l)
    rw [← hxe]
    exact hx
  · intro hy
    exact Submodule.subset_span ⟨y, hy, rfl⟩

end GlobalTheory.LatticeBackSeam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelQuotientEqTwistedTopStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_quotient_eq_twisted_top : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → (∀ i, Pr.g i ∈ S) → (∀ v, Pr.T v ∈ S) → levQTop R sel mu (4 * R.m) = twTt (R := R) sel mu R.m := by
  first | exact @GlobalTheory.TopLevQ.levQTop_eq_twTt | exact GlobalTheory.TopLevQ.levQTop_eq_twTt | (intros; apply GlobalTheory.TopLevQ.levQTop_eq_twTt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCongStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n), 1 ≤ D → (∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) → ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  first | exact @GlobalTheory.CongOne.mem_glint_prinCong_of_cols | exact GlobalTheory.CongOne.mem_glint_prinCong_of_cols | (intros; apply GlobalTheory.CongOne.mem_glint_prinCong_of_cols <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedThetaCMCurveTheoremsOfAlgebraicTransla
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.ThLoc

theorem inputs_of_algT (hT : Formalism.L2.KerInert.AlgTAll) : Inputs := by
  exact
    { jInt := cm1
      modelTwo := goodOrdinaryModelAtTwo_cmLattice_seven_mod_eight
      jetsOdd := locJets_all.1
      jetsTwo := locJets_all.2.1
      jetsThree := thetaZJetsThree
      shape := locJets_all.2.2
      algT := hT
      lamExt := place_extends_to_iso }

end GlobalTheory.ThLoc
end

