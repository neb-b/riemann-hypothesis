module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.TwistedOrbitalIntegrals.Bundle0001
public import GroundTheory.AutomorphicForms.ContragredientTranspose.MatrixSimilarity
public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.QuotFin
section
open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.L1.quotFin :
    UpperTheory.ConvolutionTheory.L1.QuotFin := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi Φ ρ hΦ hinv hsupp hn
  obtain ⟨C, hC, hsup⟩ := hsupp
  obtain ⟨hρ, hnorm⟩ := hn
  have hnorm' : ∀ x : X, ∫⁻ t, ρ (i t * x) ∂ν = 1 := hnorm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  have hKm : MeasurableSet K := hK.measurableSet
  have hcont : Continuous (fun p : T × X => i p.1 * p.2) :=
    (hi.comp continuous_fst).mul continuous_snd
  have hopen : IsOpen ((fun p : T × X => i p.1 * p.2) ⁻¹' interior K) :=
    isOpen_interior.preimage hcont
  have hsub : ({1} : Set T) ×ˢ C ⊆ (fun p : T × X => i p.1 * p.2) ⁻¹' interior K := by
    rintro ⟨t, c⟩ ⟨ht, hc⟩
    have ht' : t = 1 := ht
    subst ht'
    simpa using hCK hc
  obtain ⟨U, V, hU, hV, h1U, hCV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hC hopen hsub
  obtain ⟨N, hN, hNU, hNc⟩ := local_compact_nhds (hU.mem_nhds (h1U rfl))
  have hNm : MeasurableSet N := hNc.measurableSet
  have hNpos : ν N ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hN).ne'
  have hNfin : ν N ≠ ⊤ := hNc.measure_lt_top.ne
  have hinK : ∀ t ∈ N, ∀ c ∈ C, i t * c ∈ K := fun t ht c hc =>
    interior_subset (hUV (Set.mk_mem_prod (hNU ht) (hCV hc)))
  haveI : ν.IsMulRightInvariant := by
    have h := (inferInstance : ν.inv.IsMulRightInvariant)
    rwa [Measure.inv_eq_self] at h
  set ind : X → ℝ≥0∞ := K.indicator 1 with hind
  have hindm : Measurable ind := measurable_one.indicator hKm
  have him : Measurable i := hi.measurable
  set M : ℝ≥0∞ := ENNReal.ofReal B with hM
  have hA : ∀ t₀ : T, ∀ c ∈ C, ν N ≤ ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν := by
    intro t₀ c hc
    have h1 : ∫⁻ t, ind (i t * (i t₀ * c)) ∂ν = ∫⁻ t, ind (i t * c) ∂ν := by
      have := lintegral_mul_right_eq_self (μ := ν) (fun t => ind (i t * c)) t₀
      rw [← this]
      simp only [map_mul, mul_assoc]
    rw [h1, ← lintegral_indicator_one hNm]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ N
    · simp [ht, hind, hinK t ht c hc]
    · simp [ht]
  have hpt : ∀ x, ‖Φ x‖ₑ ≤ M / ν N * ∫⁻ t, ind (i t * x) ∂ν := by
    intro x
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨t₀, c, hc, rfl⟩ := hsup x hx
    have hle : ‖Φ (i t₀ * c)‖ₑ ≤ M := by
      rw [hinv, hM, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB c hc)
    calc ‖Φ (i t₀ * c)‖ₑ ≤ M := hle
      _ = M / ν N * ν N := (ENNReal.div_mul_cancel hNpos hNfin).symm
      _ ≤ _ := by gcongr; exact hA t₀ c hc
  have hj1 : Measurable (fun p : X × T => ind (i p.2 * p.1) * ρ p.1) :=
    (hindm.comp ((him.comp measurable_snd).mul measurable_fst)).mul (hρ.comp measurable_fst)
  have hj2 : Measurable (fun p : T × X => ind p.2 * ρ ((i p.1)⁻¹ * p.2)) :=
    (hindm.comp measurable_snd).mul
      (hρ.comp (((him.comp measurable_fst).inv).mul measurable_snd))
  have hmain : ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ = μ K := by
    calc ∫⁻ x, (∫⁻ t, ind (i t * x) ∂ν) * ρ x ∂μ
        = ∫⁻ x, ∫⁻ t, ind (i t * x) * ρ x ∂ν ∂μ := by
          refine lintegral_congr fun x => ?_
          have hm : Measurable fun t : T => ind (i t * x) := hindm.comp (him.mul_const x)
          exact (lintegral_mul_const (ρ x) hm).symm
      _ = ∫⁻ t, ∫⁻ x, ind (i t * x) * ρ x ∂μ ∂ν :=
          lintegral_lintegral_swap hj1.aemeasurable
      _ = ∫⁻ t, ∫⁻ y, ind y * ρ ((i t)⁻¹ * y) ∂μ ∂ν := by
          refine lintegral_congr fun t => ?_
          have := lintegral_mul_left_eq_self (μ := μ) (fun y => ind y * ρ ((i t)⁻¹ * y)) (i t)
          rw [← this]
          simp
      _ = ∫⁻ y, ∫⁻ t, ind y * ρ ((i t)⁻¹ * y) ∂ν ∂μ :=
          lintegral_lintegral_swap hj2.aemeasurable
      _ = ∫⁻ y, ind y ∂μ := by
          refine lintegral_congr fun y => ?_
          have hm : Measurable fun t : T => ρ (i t * y) :=
            hρ.comp ((him).mul_const y)
          have h2 : ∫⁻ t, ρ ((i t)⁻¹ * y) ∂ν = 1 := by
            have := (Measure.measurePreserving_inv ν).lintegral_comp hm
            simp only [Pi.inv_apply, map_inv] at this
            rw [this, hnorm']
          have hm' : Measurable fun t : T => ρ ((i t)⁻¹ * y) := hρ.comp (him.inv.mul_const y)
          rw [lintegral_const_mul (ind y) hm', h2, mul_one]
      _ = μ K := by
          rw [hind, lintegral_indicator_one hKm]
  calc ∫⁻ x, ‖Φ x‖ₑ * ρ x ∂μ
      ≤ ∫⁻ x, M / ν N * ((∫⁻ t, ind (i t * x) ∂ν) * ρ x) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [← mul_assoc]
        gcongr
        exact hpt x
    _ = M / ν N * μ K := by
        rw [lintegral_const_mul' _ _ (ENNReal.div_ne_top ENNReal.ofReal_ne_top hNpos), hmain]
    _ < ⊤ := ENNReal.mul_lt_top
        (ENNReal.div_lt_top ENNReal.ofReal_ne_top hNpos) hK.measure_lt_top
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
section
open Matrix Polynomial

namespace UpperTheory.ConvolutionTheory.L1

private theorem centComm_field {k : Type} [Field k] {n : ℕ} (γ a b : GL (Fin n) k)
    (hs : (γ : Matrix (Fin n) (Fin n) k).charpoly.Separable)
    (ha : a ∈ Subgroup.centralizer {γ}) (hb : b ∈ Subgroup.centralizer {γ}) : a * b = b * a := by
  rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
  have hA : Commute (a : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val ha
  have hB : Commute (b : Matrix (Fin n) (Fin n) k) (γ : Matrix (Fin n) (Fin n) k) := by
    simpa [Commute, SemiconjBy] using congrArg Units.val hb
  exact Units.ext (UpperTheory.V.Z.Tf.Orb.centComm k n _ _ _ hs hA hB)

private theorem regOk_field (k : Type) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]
    (n : ℕ) : RegOk k n := by
  intro γ hs
  refine ⟨?_, fun a ha b hb => centComm_field γ a b hs ha hb⟩
  have e : {y : GL (Fin n) k | ∃ x : GL (Fin n) k, y = x⁻¹ * γ * x} =
      ⋂ i : ℕ, {y : GL (Fin n) k | (y : Matrix (Fin n) (Fin n) k).charpoly.coeff i =
        (γ : Matrix (Fin n) (Fin n) k).charpoly.coeff i} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨x, rfl⟩ i
      have h := Matrix.charpoly_units_conj x⁻¹ (γ : Matrix (Fin n) (Fin n) k)
      rw [← Matrix.coe_units_inv, inv_inv] at h
      rw [Units.val_mul, Units.val_mul]
      exact congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) h
    · intro h
      exact GlobalTheory.BCT.ClsFin.conj_of_charpoly γ y hs (Polynomial.ext h).symm
  rw [e]
  exact isClosed_iInter fun i => isClosed_eq
    ((GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff i).comp Units.continuous_val)
    continuous_const

section Pi

variable {I : Type} {k : I → Type} [∀ i, Field (k i)] {n : ℕ}

private abbrev ev (i : I) : GL (Fin n) (∀ i, k i) →* GL (Fin n) (k i) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom k i)

private theorem ev_val (i : I) (g : GL (Fin n) (∀ i, k i)) :
    ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) =
      (g : Matrix (Fin n) (Fin n) (∀ i, k i)).map (Pi.evalRingHom k i) := rfl

private theorem ev_ext {g h : GL (Fin n) (∀ i, k i)} (e : ∀ i, ev i g = ev i h) : g = h := by
  refine Units.ext (Matrix.ext fun a b => funext fun i => ?_)
  have h : ((ev i g : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b =
      ((ev i h : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)) a b := by rw [e i]
  exact h

private def asm (x : ∀ i, GL (Fin n) (k i)) : GL (Fin n) (∀ i, k i) where
  val := Matrix.of fun a b i => (x i : Matrix (Fin n) (Fin n) (k i)) a b
  inv := Matrix.of fun a b i => ((x i)⁻¹ : GL (Fin n) (k i)).val a b
  val_inv := by
    ext a b i
    have h := congrFun (congrFun (x i).val_inv a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  inv_val := by
    ext a b i
    have h := congrFun (congrFun (x i).inv_val a) b
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [show ((x i)⁻¹ : GL (Fin n) (k i)).val = (x i).inv from rfl, h]
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

private theorem ev_asm (x : ∀ i, GL (Fin n) (k i)) (i : I) : ev i (asm x) = x i := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rfl

end Pi

private theorem regOk_pi (I : Type) (k : I → Type) [∀ i, Field (k i)] [∀ i, TopologicalSpace (k i)]
    [∀ i, IsTopologicalRing (k i)] [∀ i, T2Space (k i)] (n : ℕ) : RegOk (∀ i, k i) n := by
  intro γ hs
  have hsi : ∀ i, ((ev i γ : GL (Fin n) (k i)) : Matrix (Fin n) (Fin n) (k i)).charpoly.Separable := fun i => by
    rw [ev_val, Matrix.charpoly_map]
    exact hs.map
  have hc : ∀ i, Continuous (ev (n := n) (k := k) i) := fun i =>
    Continuous.units_map _ ((continuous_id).matrix_map (continuous_apply i))
  refine ⟨?_, fun a ha b hb => ev_ext fun i => ?_⟩
  · have e : {y : GL (Fin n) (∀ i, k i) | ∃ x : GL (Fin n) (∀ i, k i), y = x⁻¹ * γ * x} =
        ⋂ i, (ev i) ⁻¹' {y : GL (Fin n) (k i) | ∃ x : GL (Fin n) (k i), y = x⁻¹ * ev i γ * x} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · rintro ⟨x, rfl⟩ i
        exact ⟨ev i x, by simp only [map_mul, map_inv]⟩
      · intro h
        choose x hx using h
        refine ⟨asm x, ev_ext fun i => ?_⟩
        simp only [map_mul, map_inv, ev_asm]
        exact hx i
    rw [e]
    exact isClosed_iInter fun i => ((regOk_field (k i) n (ev i γ) (hsi i)).1).preimage (hc i)
  · rw [Subgroup.mem_centralizer_singleton_iff] at ha hb
    have hA : Commute (ev i a) (ev i γ) := by
      change (ev i a) * (ev i γ) = (ev i γ) * (ev i a)
      simpa only [map_mul] using congrArg (ev i) ha
    have hB : Commute (ev i b) (ev i γ) := by
      change (ev i b) * (ev i γ) = (ev i γ) * (ev i b)
      simpa only [map_mul] using congrArg (ev i) hb
    have ha' : ev i a ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hA
    have hb' : ev i b ∈ Subgroup.centralizer {ev i γ} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hB
    have hab : ev i a * ev i b = ev i b * ev i a :=
      centComm_field (ev i γ) (ev i a) (ev i b) (hsi i) ha' hb'
    simpa only [map_mul] using hab

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.regOkPi :
    UpperTheory.ConvolutionTheory.L1.RegOkPi :=
  ⟨fun k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_field k n, fun I k _ _ _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi I k n,
    fun F _ _ n => UpperTheory.ConvolutionTheory.L1.regOk_pi (NumberField.InfinitePlace F) (fun v => v.Completion) n⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev InfD (σ : E ≃ₐ[F] E) (m : ℕ) : Type :=
  Split (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E)) (galInf σ) m

variable {σ : E ≃ₐ[F] E} {m : ℕ}

def compA (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archGroup E n →* archGroup F n :=
  (archEquiv F n).toMonoidHom.comp ((D.comp n i).comp (archEquiv E n).symm.toMonoidHom)

def glueA (D : InfD σ m) (n : ℕ) (g : Fin (m + 1) → archGroup F n) : archGroup E n :=
  archEquiv E n (D.glue n fun i => (archEquiv F n).symm (g i))

def IsTens (D : InfD σ m) {n : ℕ} (φ : Fin (m + 1) → TI F n) (β : TI E n) : Prop := ∀ g, β g = ∏ i, φ i (compA D n i g)

def IsBlockElement (D : InfD σ m) (n : ℕ) (s : Fin (m + 1) → archGroup F n →* archGroup E n) : Prop :=
  ∀ i g, s i g = glueA D n (Pi.mulSingle i g)

def InSlot (D : InfD σ m) (τ : E →+* ℂ) (k : Fin (m + 1)) : Prop :=
  ∀ z : ℂ, (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm (along τ z) =
    D.e.symm (Pi.single k ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (along (τ.comp (algebraMap F E)) z)))

structure ArchSlot (D : InfD σ m) {n : ℕ} (νE : Measure (archGroup E n)) (νF : Measure (archGroup F n)) (b a : TI F n)
    (aE : TI E n) (aF : TI F n) : Prop where
  meas : νE = Measure.map (glueA D n) (Measure.pi fun _ => νF)
  smooth : SmoothT b
  fin : LeftFin b
  norm : ∫ g, ‖b g‖ ∂νF ≤ 1
  sq : ∀ g, a g = cv νF b (fun x => conj (b x⁻¹)) g
  tens : IsTens D (fun _ => a) aE
  pow : ∀ g, aF g = cvPow νF a m g

end

def ArchBasic : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ),
    (∀ g i, compA D n i (glueA D n g) = g i) ∧ (∀ x, glueA D n (fun i => compA D n i x) = x) ∧
    (∀ g h, glueA D n (g * h) = glueA D n g * glueA D n h) ∧ Continuous (glueA D n) ∧ (∀ i, Continuous (compA D n i)) ∧
    (∃ s, IsBlockElement D n s ∧ ∀ i, Continuous (s i)) ∧
    (∀ (νF : Measure (archGroup F n)) [νF.IsHaarMeasure], (Measure.map (glueA D n) (Measure.pi fun _ => νF)).IsHaarMeasure) ∧
    ∀ φ : Fin (m + 1) → TI F n, ∃ β, IsTens D φ β

def PositionOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m), (∀ τ, ∃ k, InSlot D τ k) ∧
      ∀ (n : ℕ) (g : archGroup E n), g ∈ archCompact E n ↔ ∀ i, compA D n i g ∈ archCompact F n

def TensSmooth : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
    ((∀ i, SmoothT (φ i)) → SmoothT β) ∧ ((∀ i, LeftFin (φ i)) → LeftFin β)

def JUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (τ : K →+* ℂ),
    (∃! j, IsJ (n := n) τ j) ∧ ∀ i : Fin n, zc τ i ∈ Subalgebra.center ℂ (UC K n)

def LactLaws : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (β : TI K n), SmoothT β →
    (∀ u, SmoothT (lact u β)) ∧ lact 1 β = β ∧ (∀ u v, lact (u * v) β = lact u (lact v β)) ∧
      (∀ u v, lact (u + v) β = lact u β + lact v β) ∧ ∀ (c : ℂ) u, lact (c • u) β = c • lact u β

def LactGen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E) (m : ℕ)
    (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k → ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n),
    (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ (p q : Fin n) (z : ℂ),
      IsTens D (Function.update φ k (lact ((1 : ℂ) ⊗ₜ elem (τ.comp (algebraMap F E)) p q z) (φ k))) (lact ((1 : ℂ) ⊗ₜ elem τ p q z) β)

def LactTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] [_root_.NumberField.IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (τ : E →+* ℂ) (k : Fin (m + 1)), InSlot D τ k →
    ∀ (φ : Fin (m + 1) → TI F n) (β : TI E n), (∀ i, SmoothT (φ i)) → IsTens D φ β → ∀ i : Fin n,
      IsTens D (Function.update φ k (lact (zc (τ.comp (algebraMap F E)) i) (φ k))) (lact (zc τ i) β)

def LactCv : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (α β γ : TI K n), SmoothT α → (∀ g, γ g = cv ν α β g) → SmoothT γ ∧ (LeftFin α → LeftFin γ) ∧
      (∀ u g, lact u γ g = cv ν (lact u α) β g) ∧
      (SmoothT β → ∀ z ∈ Subalgebra.center ℂ (UC K n), ∀ g, lact z γ g = cv ν α (lact z β) g)

def TensOp : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure],
    νE = Measure.map (glueA D n) (Measure.pi fun _ => νF) →
    ∀ (s : Fin (m + 1) → archGroup F n →* archGroup E n) (hs : ∀ i, Continuous (s i)), IsBlockElement D n s →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup E n) H)
      (φ : Fin (m + 1) → TI F n) (β : TI E n), IsTens D φ β →
      π.integrated νE (UnitaryRep.ccToL1 νE β) =
        (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated νF (UnitaryRep.ccToL1 νF (φ i))).prod

def SqOp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (b a aF : TI K n) (m : ℕ),
    (∀ g, a g = cv ν b (fun x => conj (b x⁻¹)) g) → (∀ g, aF g = cvPow ν a m g) → ∫ g, ‖b g‖ ∂ν ≤ 1 →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H),
      π.integrated ν (UnitaryRep.ccToL1 ν a) =
          π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) ∧
        0 ≤ π.integrated ν (UnitaryRep.ccToL1 ν a) ∧ ‖π.integrated ν (UnitaryRep.ccToL1 ν a)‖ ≤ 1 ∧
        π.integrated ν (UnitaryRep.ccToL1 ν aF) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (m + 1)

def ArchSlotEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ)
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b : TI F n), SmoothT b → LeftFin b → ∫ g, ‖b g‖ ∂νF ≤ 1 →
    ∃ (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF

def BumpEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H) (v : H), v ≠ 0 →
    ∃ b : TI K n, SmoothT b ∧ LeftFin b ∧ ∫ g, ‖b g‖ ∂ν ≤ 1 ∧ star (π.integrated ν (UnitaryRep.ccToL1 ν b)) v ≠ 0

end UpperTheory.ConvolutionTheory.L1
end
end

