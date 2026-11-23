module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0266
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProjectiveCharts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormModEqOfRayRelPowMod
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.RayFacts

theorem absNorm_span_modEq_one {F : Type} [Field F] [NumberField F] (l m : ℕ) {a : 𝓞 F} (ha : a ≠ 0)
    (ha1 : a - 1 ∈ powMod F l m) (hpos : ∀ σ : F →+* ℝ, 0 < σ (a : F)) :
    Ideal.absNorm (Ideal.span {a}) ≡ 1 [MOD l ^ m] := by
  have hn : 0 < Algebra.norm ℤ a := by
    have h := GlobalTheory.RayRootOfUnity.norm_pos_of_pos_real (x := (a : F)) (by simpa using ha) hpos
    rw [← Algebra.coe_norm_int] at h
    exact_mod_cast h
  have hc := GlobalTheory.Mem.RayNorm.norm_cast_eq F (l ^ m) (x := a) (y := 1) (by
    have e : ((l ^ m : ℕ) : 𝓞 F) = (l : 𝓞 F) ^ m := by push_cast; rfl
    rw [e]
    exact ha1)
  rw [map_one, Int.cast_one] at hc
  have h2 := congrArg (Int.cast : ℤ → ZMod (l ^ m)) (Int.natAbs_of_nonneg hn.le)
  rw [Int.cast_natCast] at h2
  rw [← ZMod.natCast_eq_natCast_iff, Ideal.absNorm_span_singleton, h2, hc, Nat.cast_one]

theorem absNorm_modEq_of_rayRel_powMod : ∀ (F : Type) [Field F] [NumberField F] (l m : ℕ) (I J : Ideal (𝓞 F)),
    RayRel F (powMod F l m) I J → Ideal.absNorm I ≡ Ideal.absNorm J [MOD l ^ m] := by
  intro F _ _ l m I J h
  obtain ⟨a, b, ha, hb, ha1, hb1, hσ, he⟩ := h
  have h1 := absNorm_span_modEq_one l m ha ha1 fun σ => (hσ σ).1
  have h2 := absNorm_span_modEq_one l m hb hb1 fun σ => (hσ σ).2
  have h3 := congrArg Ideal.absNorm he
  rw [map_mul, map_mul] at h3
  calc Ideal.absNorm I = 1 * Ideal.absNorm I := (one_mul _).symm
    _ ≡ Ideal.absNorm (Ideal.span {a}) * Ideal.absNorm I [MOD l ^ m] := h1.symm.mul_right _
    _ = Ideal.absNorm (Ideal.span {b}) * Ideal.absNorm J := h3
    _ ≡ 1 * Ideal.absNorm J [MOD l ^ m] := h2.mul_right _
    _ = Ideal.absNorm J := one_mul _

end GlobalTheory.CompanionTheory.RayFacts
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgIntervalIntegralSwap
section
open GlobalTheory.CuspGeneric MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgSwap

private theorem integral_intervalIntegral_comm_of_continuous_norm_le {G : Type} [TopologicalSpace G]
    {mG : MeasurableSpace G} [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasure μ]
    (F : G × ℝ → ℂ) (hF : Continuous F) (t C : ℝ)
    (hC : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C) :
    ∫ x, (∫ s in (0 : ℝ)..t, F (x, s)) ∂μ = ∫ s in (0 : ℝ)..t, ∫ x, F (x, s) ∂μ := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hint : Integrable (Function.uncurry fun x s => F (x, s))
      (μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))) := by
    refine Integrable.mono' (integrable_const C) hF.aestronglyMeasurable ?_
    have hs : ∀ᵐ p ∂(μ.prod (volume.restrict (Set.uIoc (0 : ℝ) t))), p.2 ∈ Set.uIoc (0 : ℝ) t :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hs] with p hp
    exact hC p.1 p.2 (Set.uIoc_subset_uIcc hp)
  simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  rw [integral_smul]
  congr 1
  exact integral_integral_swap hint

theorem avg_intervalIntegral_swap {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G) (hΓ : IsCoLat Γ)
    (F : G × ℝ → ℂ) (hF : Continuous F) (hper : ∀ γ ∈ Γ, ∀ x s, F (γ + x, s) = F (x, s)) (t : ℝ) :
    avg Γ (fun x => ∫ s in (0 : ℝ)..t, F (x, s)) = ∫ s in (0 : ℝ)..t, avg Γ (fun x => F (x, s)) := by
  unfold GlobalTheory.CuspGeneric.IsCoLat at hΓ
  obtain ⟨-, K, hK, hKcov⟩ := hΓ
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_uIcc (a := (0 : ℝ)) (b := t))).exists_bound_of_continuousOn
    hF.continuousOn
  have hbound : ∀ x, ∀ s ∈ Set.uIcc (0 : ℝ) t, ‖F (x, s)‖ ≤ C := by
    intro x s hs
    obtain ⟨γ, hγ, hγK⟩ := hKcov x
    rw [← hper γ hγ x s]
    exact hC (γ + x, s) ⟨hγK, hs⟩
  borelize G
  unfold GlobalTheory.CuspGeneric.avg
  split_ifs with h
  · try simp only [dif_pos h]
    haveI : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      ⟨by rw [Measure.restrict_apply_univ, h.choose_spec.2.2]; exact ENNReal.one_lt_top⟩
    exact integral_intervalIntegral_comm_of_continuous_norm_le _ F hF t C hbound
  · simp only [dif_neg h, intervalIntegral.integral_zero]

end GlobalTheory.CompanionTheory.AvgSwap
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace resG)
open GlobalTheory.ProjSpace (chart formOn ratioOn ratio)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

theorem app_presheaf_map {A B : Scheme.{0}} (φ : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (h' : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U) (a : Γ(A, U)) :
    (φ.app V).hom ((A.presheaf.map (homOfLE h).op).hom a) =
      (B.presheaf.map (homOfLE h').op).hom ((φ.app U).hom a) := by
  have e := congrArg (fun g => CommRingCat.Hom.hom g a) (φ.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {R : Type} [CommRing R] {N : ℕ}

private theorem formOn_congr {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f g : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (h : f = g) :
    formOn U i hi n f hf = formOn U i hi n g hg := by
  subst h
  rfl

theorem formOn_X_pow (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hi : U ≤ chart R N i)
    (j : Fin (N + 1)) (m : ℕ) :
    formOn U i hi m (X j ^ m) (isHomogeneous_X_pow j m) = ratioOn U i hi j ^ m := by
  induction m with
  | zero =>
    rw [formOn_congr _ (isHomogeneous_C _ (1 : R)) (by simp), GlobalTheory.ProjSpace.formOn_C, map_one, pow_zero]
  | succ m ih =>
    rw [formOn_congr _ ((isHomogeneous_X_pow j m).mul (isHomogeneous_X R j)) (pow_succ _ _),
      GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow j m) (isHomogeneous_X R j), ih, GlobalTheory.ProjSpace.formOn_X, pow_succ]

theorem exists_ratio_pow_mul_eq_zero {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1))
    (h0 : (φ.app (chart R N k)).hom (formOn (chart R N k) k le_rfl n f hf) = 0)
    (j : Fin (N + 1)) :
    ∃ m : ℕ, (φ.app (chart R N j)).hom (ratio R N j k) ^ m *
      (φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf) = 0 := by
  have hW : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N j :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_left
  have hW' : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N k :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_right
  have e1 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N j) (i := j) (hi := le_rfl)
    (inf_le_left : chart R N j ⊓ chart R N k ≤ chart R N j) hf
  have e2 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N k) (i := k) (hi := le_rfl)
    (inf_le_right : chart R N j ⊓ chart R N k ≤ chart R N k) hf
  have e3 := GlobalTheory.ProjSpace.formOn_eq_ratioOn_pow_mul (U := chart R N j ⊓ chart R N k) (i := j)
    (hi := inf_le_left) (j := k) inf_le_right hf
  have key : (Y.presheaf.map (homOfLE hW).op).hom
      ((φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf)) = 0 := by
    rw [← app_presheaf_map φ inf_le_left hW]
    erw [e1]
    rw [e3, ← e2, map_mul]
    erw [app_presheaf_map φ inf_le_right hW']
    rw [h0, map_zero, mul_zero]
  have hle : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ≤ φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) := by
    rw [← Scheme.preimage_basicOpen, GlobalTheory.ProjSpace.basicOpen_ratioOn]
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y (U := φ ⁻¹ᵁ chart R N j)
    (φ.isCompact_preimage (GlobalTheory.ProjSpace.isAffineOpen_chart R N j).isCompact) _ _ ?_
  show (Y.presheaf.map (homOfLE _).op).hom _ = 0
  rw [show (homOfLE (Y.basicOpen_le _) : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ⟶ φ ⁻¹ᵁ chart R N j) =
      homOfLE hle ≫ homOfLE hW from rfl, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, key,
    map_zero]

theorem exists_killsForm_X_pow_mul :
    ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  intro R _ N Y φ _ n f hf k h0
  choose m hm using fun j => exists_ratio_pow_mul_eq_zero φ n f hf k h0 j
  refine ⟨∑ j, m j, (isHomogeneous_X_pow k _).mul hf, ?_⟩
  intro j
  rw [GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow k _) hf, formOn_X_pow, map_mul, map_pow]
  have hle : m j ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hm j, mul_zero]

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

theorem ker_inter_eq_sup {X Y A B Z : Scheme.{0}} (t : Y ⟶ X) (a : A ⟶ Y) (b : B ⟶ Y) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion t] [IsClosedImmersion a] [IsClosedImmersion b]
    (h : IsPullback f g a b) :
    Scheme.Hom.ker ((f ≫ a) ≫ t) = Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · set K := Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) with hK
    have hA : Scheme.Hom.ker (a ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have hB : Scheme.Hom.ker (b ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let u : K.subscheme ⟶ A := IsClosedImmersion.lift (a ≫ t) K.subschemeι hA
    let v : K.subscheme ⟶ B := IsClosedImmersion.lift (b ≫ t) K.subschemeι hB
    have hu : u ≫ a ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hv : v ≫ b ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have huv : u ≫ a = v ≫ b := by
      rw [← cancel_mono t, Category.assoc, Category.assoc, hu, hv]
    have hl : h.lift u v huv ≫ (f ≫ a) ≫ t = K.subschemeι := by
      rw [← Category.assoc, ← Category.assoc, h.lift_fst, Category.assoc]
      exact hu
    calc Scheme.Hom.ker ((f ≫ a) ≫ t) ≤ (h.lift u v huv ≫ (f ≫ a) ≫ t).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = K := by rw [hl, Scheme.IdealSheafData.ker_subschemeι]
  · rw [Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [h.w, Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleSectionsGlueHomogeneous
section
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.SerreVan

variable {B : Type} [CommRing B] {M : ℕ}



def V0 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ f ∈ P, f.IsHomogeneous n → (∀ i ∈ W, ∃ m : ℕ, X i ^ m * f ∈ Q) → f ∈ Q

def V1 (W : Finset (Fin M)) (P Q : Ideal (MvPolynomial (Fin M) B)) (n₀ : ℕ) : Prop :=
  ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin M → MvPolynomial (Fin M) B),
    (∀ i ∈ W, f i ∈ P ∧ (f i).IsHomogeneous (n + k)) →
    (∀ i ∈ W, ∀ j ∈ W, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ Q) →
    ∃ g ∈ P, g.IsHomogeneous n ∧ ∀ i ∈ W, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ Q

section Extension

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Extension

section Steps

variable {W : Finset (Fin M)} {P P' Q : Ideal (MvPolynomial (Fin M) B)} {n₀ : ℕ}

end Steps

section Base

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

end Base

section Main

variable {P Q : Ideal (MvPolynomial (Fin M) B)}

theorem charts [IsNoetherianRing B] (W : Finset (Fin M)) :
    ∀ P Q : Ideal (MvPolynomial (Fin M) B), HomogIdeal P → HomogIdeal Q → Q ≤ P →
      (∀ j, j ∉ W → ∃ k : ℕ, ∀ f ∈ P, X j ^ k * f ∈ Q) →
      ∃ n₀, V0 W P Q n₀ ∧ V1 W P Q n₀ :=
  _root_.UpperTheory.Reformulated.B.ProjectiveCharts.charts W

theorem serre_vanishing : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ)
    (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  intro B _ _ N P hP
  obtain ⟨n₀, -, h⟩ := charts (B := B) (M := N + 1) Finset.univ ⊤ P (fun _ _ _ => trivial) hP
    le_top (fun j hj => absurd (Finset.mem_univ j) hj)
  refine ⟨n₀, fun n hn k f hf hc => ?_⟩
  obtain ⟨g, -, hgh, hg⟩ := h n hn k f (fun i _ => ⟨trivial, hf i⟩)
    (fun i _ j _ => hc i j)
  exact ⟨g, hgh, fun i => hg i (Finset.mem_univ i)⟩

end Main

end GlobalTheory.CompanionTheory.GE.SerreVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRational
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConeLift
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeLiftEx

theorem exists_unit_lift {B : Type} [CommRing B] (J : Ideal B) (hJ : ∀ x ∈ J, IsNilpotent x) (u : (B ⧸ J)ˣ) :
    ∃ w : Bˣ, Ideal.Quotient.mk J (w : B) = (u : B ⧸ J) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ J)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (B ⧸ J)ˣ) : B ⧸ J)
  have hmem : a * b - 1 ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ha, hb, Units.mul_inv, map_one, sub_self]
  have hu : IsUnit (a * b) := by
    have := (hJ _ hmem).isUnit_one_add
    simpa using this
  exact ⟨(isUnit_of_mul_isUnit_left hu).unit, by simpa using ha⟩

theorem nonempty_cLiftK : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (s : ℕ), Nonempty (CLiftK (KS q s (𝒱D D)).ι D) := by
  intro K _ X q D s
  have hp : ∀ c : (KS q s (𝒱D D)).FullSubcategory,
      ∃ p : Spec (CommRingCat.of (c.obj.B ⧸ c.obj.J)) ⟶ D.Y, p ≫ D.f = pt c.obj := by
    intro c
    obtain ⟨V, ⟨σ, hσ⟩, hV⟩ := c.property.2
    have hr : Set.range (pt c.obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hV (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt c.obj) hr ≫ σ, ?_⟩
    rw [Category.assoc, hσ, IsOpenImmersion.lift_fac]
  choose p hp using hp
  have hw : ∀ {c c' : (KS q s (𝒱D D)).FullSubcategory} (φ : c ⟶ c'),
      ∃ w : (((KS q s (𝒱D D)).ι).obj c').Bˣ, ∀ (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
        Ideal.Quotient.mk (((KS q s (𝒱D D)).ι).obj c').J w = (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom
          (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) (p c') h) := by
    intro c c' φ
    by_cases h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (((KS q s (𝒱D D)).ι).obj c').J (((KS q s (𝒱D D)).ι).map φ).φ (((KS q s (𝒱D D)).ι).map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f
    · obtain ⟨w, hw⟩ := exists_unit_lift (((KS q s (𝒱D D)).ι).obj c').J
        (fun x hx => GlobalTheory.CompanionTheory.SiteNil.thick_J_isNilpotent _ x hx)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of ((((KS q s (𝒱D D)).ι).obj c').B ⧸ (((KS q s (𝒱D D)).ι).obj c').J))).hom.hom.toMonoidHom
          (D.u _ _ h))
      exact ⟨w, fun _ => hw⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose w hw using @hw
  exact ⟨{ p := p, hp := hp, w := fun φ => w φ, hw := fun φ h => hw φ h }⟩

end GlobalTheory.CompanionTheory.ConeLiftEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetGenerators
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LocalIntegers

theorem exists_finset_generators (l : ℕ) [Fact l.Prime]
    (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ s : Finset (OK l K), ∀ a : OK l K, ∃ c : OK l K → ℤ_[l],
      (((a : K) : PadicAlgCl l)) = ∑ i ∈ s, ((c i : ℚ_[l]) • (((i : K) : PadicAlgCl l))) := by
  classical
  haveI : Algebra.IsSeparable ℚ_[l] K := Algebra.IsSeparable.of_integral ℚ_[l] K
  haveI : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := integralClosure ℤ_[l] K)
  have hmem : ∀ x : K, x ∈ OK l K ↔ x ∈ integralClosure ℤ_[l] K := by
    intro x
    rw [OK_eq]
    rfl
  let e : integralClosure ℤ_[l] K → OK l K := fun x => ⟨x.1, (hmem x.1).2 x.2⟩
  have he : Function.Injective e := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : OK l K => (z : K)) hxy)
  refine ⟨t.image e, fun a => ?_⟩
  have ha : (⟨(a : K), (hmem _).1 a.2⟩ : integralClosure ℤ_[l] K) ∈ Submodule.span ℤ_[l] (t : Set _) := by
    rw [ht]
    trivial
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp ha
  refine ⟨fun o => f ⟨(o : K), (hmem _).1 o.2⟩, ?_⟩
  rw [Finset.sum_image fun x _ y _ hxy => he hxy]
  have h1 : (a : K) = ∑ j ∈ t, ((f j • j : integralClosure ℤ_[l] K) : K) := by
    rw [← AddSubmonoidClass.coe_finsetSum, hf]
  rw [h1, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  show (((f j • j : integralClosure ℤ_[l] K) : K) : PadicAlgCl l) = ((f j : ℚ_[l]) • ((j : K) : PadicAlgCl l))
  rw [SetLike.val_smul, ← algebraMap_smul ℚ_[l] (f j) (j : K)]
  rfl

end GlobalTheory.CompanionTheory.LocalIntegers
end

