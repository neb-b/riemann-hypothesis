module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsVolumeTransportOfLatticeIsometry
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelfDualCompSelfAdjoint
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem selfDual_comp_selfAdjoint : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ) (T : V ≃ₜ V) (δ : ℝ≥0), δ ≠ 0 → μ = δ • μ.map T → (∀ x y, χ x (T y) = χ (T x) y) → SelfDual μ χ → SelfDual (NNReal.sqrt δ • μ) (fun x y => χ x (T y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ T δ hδ hμ hχ hsd
  have hH := hsd.1
  have hs0 : NNReal.sqrt δ ≠ 0 := by simpa using hδ
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ hs0, ?_⟩
  intro Φ hc hcs hI z
  set s : ℝ≥0 := NNReal.sqrt δ with hs
  set F : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ with hF
  have hT : ∀ y, ∫ x, Φ x * χ x (T y) ∂(s • μ) = (s : ℂ) * F (T y) := by
    intro y
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hmap : μ.map T = μ.map T.toMeasurableEquiv := rfl
  simp only [hT] at hI ⊢
  have h1 : Integrable (fun y => F (T y)) μ := by
    have h2 : Integrable (fun y => (s : ℂ) * F (T y)) μ := by
      have := hI.smul_measure_nnreal (c := s⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
    have := h2.const_mul ((s : ℂ)⁻¹)
    simpa [← mul_assoc, inv_mul_cancel₀ hsC] using this
  have h3 : Integrable F μ := by
    rw [hμ]
    apply Integrable.smul_measure_nnreal
    rw [hmap, integrable_map_equiv]
    exact h1
  have h4 := hsd.2 Φ hc hcs h3 z
  rw [← h4]
  have h5 : ∫ y, F y * χ y z ∂μ = (δ : ℂ) * ∫ y, F (T y) * χ (T y) z ∂μ := by
    conv_lhs => rw [hμ]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, hmap, integral_map_equiv]
    rfl
  have hss : (s : ℂ) * (s : ℂ) = (δ : ℂ) := by
    have : s * s = δ := NNReal.mul_self_sqrt δ
    rw [← this]; push_cast; rfl
  change _ = ∫ y, F y * χ y z ∂μ
  rw [h5, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, ← hss, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1
  ext y
  rw [hχ, mul_assoc]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TailProdMulOfLatticeMassMul
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem summable_abs_mul_sub_one {ι : Type} {a a' : ι → ℝ} (ha : Summable fun v => |a v - 1|)
    (ha' : Summable fun v => |a' v - 1|) : Summable fun v => |a v * a' v - 1| := by
  have h1 : Summable fun v => |a v - 1| * |a' v - 1| := by
    refine Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_)
      (ha.mul_right (∑' w, |a' w - 1|))
    exact mul_le_mul_of_nonneg_left (ha'.le_tsum v fun w _ => abs_nonneg _) (abs_nonneg _)
  refine Summable.of_nonneg_of_le (fun v => abs_nonneg _) (fun v => ?_) ((h1.add ha).add ha')
  have : a v * a' v - 1 = (a v - 1) * (a' v - 1) + (a v - 1) + (a' v - 1) := by ring
  rw [this, ← abs_mul]
  exact abs_add_three _ _ _

theorem multipliable_subtype_of_summable_abs {ι : Type} {a : ι → ℝ}
    (ha : Summable fun v => |a v - 1|) (p : ι → Prop) :
    Multipliable fun v : {v // p v} => a v.1 := by
  have h : Summable fun v : {v // p v} => (a v.1 - 1) :=
    (Summable.of_abs ha).comp_injective Subtype.val_injective
  have := Real.multipliable_one_add_of_summable h
  simpa using this

theorem tprod_nonneg_of_multipliable {ι : Type} {a : ι → ℝ} (ha : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v :=
  ge_of_tendsto' ha.hasProd fun _ => Finset.prod_nonneg fun v _ => h0 v

theorem tailProd_mul_of_mass_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) (n₁ M₁ n₂ M₂ n₃ M₃ : ℕ) (mi : Measure (Fin n₁ → Fin M₁ → Ainf F ⊗[F] E)) (mv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₁ → Fin M₁ → Fv F v ⊗[F] E)) (mi' : Measure (Fin n₂ → Fin M₂ → Ainf F ⊗[F] E)) (mv' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₂ → Fin M₂ → Fv F v ⊗[F] E)) (Nv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n₃ → Fin M₃ → Fv F v ⊗[F] E)) (S₀ : Finset (HeightOneSpectrum (𝓞 F))), Conv b mi mv → Conv b mi' mv' → (∀ v ∉ S₀, Nv v (latV b v) = mv v (latV b v) * mv' v (latV b v)) → (Summable fun v => |(Nv v (latV b v)).toReal - 1|) ∧ ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S → tailProd b Nv S = tailProd b mv S * tailProd b mv' S := by
  intro F E _ _ _ _ _ d b n₁ M₁ n₂ M₂ n₃ M₃ mi mv mi' mv' Nv S₀ h h' hN
  refine ⟨?_, fun S hS => ?_⟩
  · refine (summable_abs_mul_sub_one h.2.2 h'.2.2).congr_cofinite ?_
    filter_upwards [S₀.eventually_cofinite_notMem] with v hv
    rw [hN v hv, ENNReal.toReal_mul]
  · have m := multipliable_subtype_of_summable_abs h.2.2 (fun v => v ∉ S)
    have m' := multipliable_subtype_of_summable_abs h'.2.2 (fun v => v ∉ S)
    unfold tailProd
    rw [← ENNReal.ofReal_mul (tprod_nonneg_of_multipliable m fun _ => ENNReal.toReal_nonneg),
      ← m.tprod_mul m']
    congr 1
    refine tprod_congr fun v => ?_
    rw [hN v.1 (fun hv => v.2 (hS hv)), ENNReal.toReal_mul]

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx


open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis {R S ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsOpenUnits R] [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsModuleTopology R S] [IsTopologicalRing S] [Fintype ι] (b : Module.Basis ι R S) :
    IsOpenUnits S := by
  classical
  have hR : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hLc : Continuous (fun x : S => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hopenR : IsOpen {r : R | IsUnit r} := hR.isOpen_range
  have hinvR : ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
    rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hR.continuousAt_iff]
    have h : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v => ↑v⁻¹ := by
      funext v
      simp [Ring.inverse_unit]
    rw [h]
    exact Units.continuous_coe_inv.continuousAt
  obtain ⟨g, hg⟩ : ∃ g : S → S, ∀ x, g x =
      b.equivFun.symm (Matrix.mulVec (Algebra.leftMulMatrix b x)⁻¹ (b.equivFun 1)) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ x, IsUnit (Algebra.leftMulMatrix b x).det → x * g x = 1 := by
    intro x hx
    apply b.equivFun.injective
    rw [Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr,
      ← Module.Basis.equivFun_apply, hg, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hx, Matrix.one_mulVec, Module.Basis.equivFun_apply]
  have hunit : ∀ x : S, IsUnit x ↔ IsUnit (Algebra.leftMulMatrix b x).det := by
    intro x
    constructor
    · intro h
      exact (Matrix.isUnit_iff_isUnit_det _).mp (h.map (Algebra.leftMulMatrix b))
    · intro h
      exact ⟨⟨x, g x, key x h, by rw [mul_comm]; exact key x h⟩, rfl⟩
  have hopenS : IsOpen {x : S | IsUnit x} := by
    have h : {x : S | IsUnit x} =
        (fun x : S => (Algebra.leftMulMatrix b x).det) ⁻¹' {r : R | IsUnit r} :=
      Set.ext hunit
    rw [h]
    exact hopenR.preimage hLc.matrix_det
  have hc1 : ContinuousOn (fun x : S => Ring.inverse (Algebra.leftMulMatrix b x).det)
      {x : S | IsUnit x} :=
    hinvR.comp hLc.matrix_det.continuousOn (fun x hx => (hunit x).mp hx)
  have hc2 : ContinuousOn (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) {x : S | IsUnit x} := by
    simp_rw [Matrix.inv_def]
    exact hc1.smul hLc.matrix_adjugate.continuousOn
  have hsymm : Continuous (b.equivFun.symm : (ι → R) → S) :=
    LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hc3 : ContinuousOn g {x : S | IsUnit x} := by
    have h : g = (fun M : Matrix ι ι R => b.equivFun.symm (Matrix.mulVec M (b.equivFun 1))) ∘
        (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) := by
      funext x
      exact hg x
    rw [h]
    exact (hsymm.comp (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn hc2
  have hgu : ∀ u : Sˣ, g u = ↑u⁻¹ := by
    intro u
    calc g u = ↑u⁻¹ * (↑u * g u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [key _ ((hunit _).mp u.isUnit), mul_one]
  exact ⟨⟨Units.isEmbedding_val_mk' hc3 hgu, hopenS⟩⟩


open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
theorem _root_.GlobalTheory.GaugeEx.nice_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], _root_.GlobalTheory.GaugeEx.Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  intro F E _ _ _ _ _ R _ _ _ _ _ _ _ _ _ hR
  obtain ⟨hArt, hRed, hOpen, -⟩ := hR
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, ?_, ?_⟩
  · exact IsArtinianRing.of_finite R (R ⊗[F] E)
  · exact _root_.GlobalTheory.ReducedAlg.isReduced_tensor (k := F) R E
  · haveI := _root_.GlobalTheory.GaugeEx.modTopTens (F := F) (E := E) R
    haveI := _root_.GlobalTheory.GaugeEx.topRingTens (F := F) (E := E) R
    exact _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasis F E))

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasis
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeFrameBasis

open GlobalTheory.VolTransport

theorem eq_conj {A : Type} [CommRing A] {M : ℕ} {T T' x y : Matrix (Fin M) (Fin M) A}
    (h : T * T' = 1) (k : x * T' = T' * y) : y = T * x * T' := by
  rw [Matrix.mul_assoc, k, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem conj_rel {A : Type} [CommRing A] {M : ℕ} {T T' : Matrix (Fin M) (Fin M) A}
    (h : T' * T = 1) (x : Matrix (Fin M) (Fin M) A) : x * T' = T' * (T * x * T') := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul]

theorem frame_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), J' = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E) → (∃! e : HA R σ J ≃* HA R σ J', ∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) ∧ ∀ e : HA R σ J ≃* HA R σ J', (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → Continuous e ∧ Continuous e.symm := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ M J J' P hJ
  have h0 : IsoPair (σ : E →+* E) J J' ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)
      (P : Matrix (Fin M) (Fin M) E) := by
    refine ⟨Units.inv_mul P, Units.mul_inv P, ?_, hJ.symm⟩
    rw [hJ]
    calc _ = Formalism.UG.cT (σ : E →+* E) ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) * J *
          ((P : Matrix (Fin M) (Fin M) E) * ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E)) := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have h : IsoPair (sigR R σ) (JR R J) (JR R J')
      (((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R))
      ((P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R)) :=
    h0.map (inclR (F := F) R) (fun _ => rfl)
  let e0 : HA R σ J ≃* HA R σ J' := conjE h
  have hm : ∀ g, ((HA.mat R σ J' (e0 g) : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) =
      ((P⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) *
        ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
        (P : Matrix (Fin M) (Fin M) E).map (inclR (F := F) R) := fun _ => rfl
  have hu : ∀ e : HA R σ J ≃* HA R σ J',
      (∀ g, FrameRelR R σ J J' (P : Matrix (Fin M) (Fin M) E) g (e g)) → e = e0 := by
    intro e he
    ext g
    apply Subtype.ext
    apply Units.ext
    refine Eq.trans ?_ (hm g).symm
    exact eq_conj h.1 (he g)
  refine ⟨⟨e0, fun g => ?_, hu⟩, fun e he => ?_⟩
  · exact conj_rel h.2.1 _
  · rw [hu e he]
    have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    exact ⟨conjU_continuous h, conjU_continuous h.symm⟩

end GlobalTheory.GaugeFrameBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupRealPointsEquivPiIndefiniteUnitary
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.InfGroup

section General

variable {S : Type} [CommRing S] {I : Type} {M : ℕ}

def lift (e : S ≃+* (I → ℂ)) (m : I → Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) S :=
  Matrix.of fun a b => e.symm fun i => m i a b

variable {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem lift_map (he : ∀ x i, e x i = θ i x) (m : I → Matrix (Fin M) (Fin M) ℂ) (i : I) :
    (lift e m).map (θ i) = m i := by
  ext a b
  simp [lift, ← he]

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) : (Formalism.UG.cT s X).map t = (X.map t)ᴴ := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem conj_mul {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X Y : Matrix n n ℂ) :
    A * X * B * (A * Y * B) = A * (X * Y) * B := by
  calc A * X * B * (A * Y * B) = A * X * (B * A) * Y * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem conj_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X : Matrix n n ℂ) :
    B * (A * X * B) * A = X := by
  calc B * (A * X * B) * A = (B * A) * X * (B * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem conj_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) {G X : Matrix n n ℂ} {K : Matrix m m ℂ}
    (hK : Bᴴ * G * B = K) (hX : Xᴴ * G * X = G) :
    (A * X * B)ᴴ * K * (A * X * B) = K := by
  rw [← hK]
  calc (A * X * B)ᴴ * (Bᴴ * G * B) * (A * X * B)
      = Bᴴ * (Xᴴ * ((B * A)ᴴ * G * (B * A)) * X) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hBA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (P Q : I → ℕ)
    (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ)
    (B : ∀ i, Matrix (Fin M) (Fin (P i) ⊕ Fin (Q i)) ℂ)
    (hAB : ∀ i, A i * B i = 1) (hBA : ∀ i, B i * A i = 1)
    (hA : ∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (θ i)) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (f h i) * A i =
      A i * ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hB : ∀ i, (B i)ᴴ * J.map (θ i) * B i = Formalism.UG.Jpq (P i) (Q i) := by
    intro i
    rw [← hA]
    calc (B i)ᴴ * ((A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i) * B i
        = (A i * B i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * (A i * B i) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  have hfw : ∀ (h : Formalism.UG.UJ s J) (i : I), ∃ g : UpqT (P i) (Q i),
      UpqT.mat g = A i * h.1.1.map (θ i) * B i := by
    intro h i
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    have : A i * h.1.1.map (θ i) * B i ∈ Set.range (UpqT.mat (P := P i) (Q := Q i)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact conj_unitary (hBA i) (hB i) h2
    exact this
  choose fw hfw using hfw
  have hmul : ∀ {p q : ℕ} (a b : UpqT p q), UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b :=
    fun _ _ => rfl
  have hm1 : ∀ {p q : ℕ}, UpqT.mat (1 : UpqT p q) = 1 := rfl
  have hinj : ∀ (p q : ℕ), Function.Injective (UpqT.mat (P := p) (Q := q)) :=
    fun _ _ => GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  let L : (∀ i, UpqT (P i) (Q i)) → Matrix (Fin M) (Fin M) S :=
    fun g => lift e fun i => B i * UpqT.mat (g i) * A i
  have hL : ∀ g i, (L g).map (θ i) = B i * UpqT.mat (g i) * A i := fun g i => lift_map he _ i
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL, conj_mul (hAB i), Pi.mul_apply, hmul]
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, Pi.one_apply, hm1, Matrix.mul_one, hBA, hone]
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact conj_unitary (hAB i) (hA i) (GlobalTheory.UpqTopology.mat_unitary (g i))
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : ∀ i, UpqT (P i) (Q i) => B i * UpqT.mat (g i) * A i :=
      (continuous_const.matrix_mul
        (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply i))).matrix_mul continuous_const
    exact this.matrix_elem a b
  let bw : (∀ i, UpqT (P i) (Q i)) → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  haveI : ∀ i, IsTopologicalGroup (UpqT (P i) (Q i)) := fun i => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => ?_⟩
  · refine Subtype.ext (Units.ext (ext_map he fun i => ?_))
    change (L (fw h)).map (θ i) = _
    rw [hL, hfw, conj_conj (hBA i)]
  · funext i
    apply hinj
    rw [hfw]
    change A i * (L g).map (θ i) * B i = _
    rw [hL, conj_conj (hAB i)]
  · funext i
    apply hinj
    rw [Pi.mul_apply, hmul, hfw, hfw, hfw, conj_mul (hBA i), ← Matrix.map_mul]
    rfl
  · refine continuous_pi fun i => GlobalTheory.UpqTopology.isInducing_mat.continuous_iff.2 ?_
    have : (UpqT.mat ∘ fun h => fw h i) = fun h : Formalism.UG.UJ s J => A i * h.1.1.map (θ i) * B i :=
      funext fun h => hfw h i
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).matrix_map
      (hθ i))).matrix_mul continuous_const
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _
  · change UpqT.mat (fw h i) * A i = _
    rw [hfw, Matrix.mul_assoc, hBA, Matrix.mul_one]

end General

theorem real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  intro F E _ _ _ _ _ σ M J I _ τ θ P Q A hcm hfam hθ hsig hA
  obtain ⟨e, he, hc, hc', hs⟩ := _root_.GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ I τ θ hcm hfam hθ
  choose B hAB hBA using fun i =>
    (GlobalTheory.Mem.SignatureFactor.exists_factor M (P i) (Q i) _ (hsig i)).2.2 (A i) (hA i)
  refine exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs])
    (JR (Ainf F) J) P Q A B hAB hBA fun i => ?_
  rw [hA]
  ext a b
  exact ((hθ i).1 (J a b)).symm

end GlobalTheory.Mem.InfGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramInTrans
section
open NumberField IsDedekindDomain GlobalTheory.NT GlobalTheory.Mem.Fld GlobalTheory.Published

namespace GlobalTheory.Mem.UnramTower

theorem unramIn_trans : ∀ (K L N : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field N] [NumberField N] [Algebra K L] [Algebra L N] [Algebra K N] [IsScalarTower K L N] [IsGalois K L] [IsGalois K N], (∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn L 𝔭) → (∀ P : HeightOneSpectrum (𝓞 L), GlobalTheory.NT.UnramIn N P) → ∀ 𝔭 : HeightOneSpectrum (𝓞 K), GlobalTheory.NT.UnramIn N 𝔭 := by
  intro K L N _ _ _ _ _ _ _ _ _ _ _ _ hL hN 𝔭 σ hσ
  obtain ⟨Q, hQ, hQo, hσ⟩ := hσ
  have hσ' : ∀ x : 𝓞 N, σ • x - x ∈ Q := fun x => hσ x
  have hPo : (Q.under (𝓞 L)).LiesOver 𝔭.asIdeal := inferInstance
  have hP : (Q.under (𝓞 L)).IsPrime := inferInstance
  have h1 : σ.restrictNormal L = 1 := by
    refine hL 𝔭 _ ⟨Q.under (𝓞 L), hP, hPo, ?_⟩
    intro x
    have hx := hσ' (algebraMap (𝓞 L) (𝓞 N) x)
    have e : algebraMap (𝓞 L) (𝓞 N) ((σ.restrictNormal L) • x) = σ • algebraMap (𝓞 L) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact AlgEquiv.restrictNormal_commutes σ L (x : L)
    show (σ.restrictNormal L) • x - x ∈ Ideal.comap (algebraMap (𝓞 L) (𝓞 N)) Q
    rw [Ideal.mem_comap, map_sub, e]
    exact hx
  have hfix : ∀ y : L, σ (algebraMap L N y) = algebraMap L N y := by
    intro y
    rw [← AlgEquiv.restrictNormal_commutes σ L y, h1]
    rfl
  let τ : N ≃ₐ[L] N := { σ.toRingEquiv with commutes' := hfix }
  let P : HeightOneSpectrum (𝓞 L) :=
    ⟨Q.under (𝓞 L), hP, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot _⟩
  have h2 : τ = 1 := by
    refine hN P τ ⟨Q, hQ, ⟨rfl⟩, ?_⟩
    intro x
    exact hσ' x
  ext y
  exact DFunLike.congr_fun h2 y

end GlobalTheory.Mem.UnramTower
end

