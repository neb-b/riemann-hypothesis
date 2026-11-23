module

public import Mathlib
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusEqOneOfIntegral
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound
open PositivityTheory.JacquetShalikaLocal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem div_mono {ι : Type} {c c' : ℕ} (h : c ≤ c') {A : Matrix ι ι F} (hA : Div c' A) : Div c A := by
  intro i j
  obtain ⟨y, hy, e⟩ := hA i j
  refine ⟨(uniformizer F : F) ^ (c' - c) * y,
    Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) hy, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem modulus_eq_one_of_integral {a : F} (ha : a ≠ 0) (h₁ : a ∈ 𝒪[F]) (h₂ : a⁻¹ ∈ 𝒪[F]) :
    Measures.modulus a = 1 := by
  let u : Fˣ := Units.mk0 a ha
  let g : GL (Fin 1) F := Units.map (Matrix.scalar (Fin 1) : F →+* Matrix (Fin 1) (Fin 1) F).toMonoidHom u
  have hg : ∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j = a := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have hgi : ∀ i j, ((g⁻¹ : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) i j = a⁻¹ := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have key := Measures.distribHaarChar_glEquiv g
  rw [Measures.distribHaarChar_glEquiv_eq_one (fun i j => by rw [hg]; exact h₁)
    (fun i j => by rw [hgi]; exact h₂)] at key
  have hdet : Matrix.GeneralLinearGroup.det g = u := by
    ext
    simp [g, u]
  rw [hdet] at key
  rw [show a = (u : F) from rfl, Measures.modulus_units, ← key]

theorem modulus_det_eq_one {m c : ℕ} (h : GL (Fin m) F)
    (hD : Div (c + 1) ((h : Matrix (Fin m) (Fin m) F) - 1)) :
    Measures.modulus (h : Matrix (Fin m) (Fin m) F).det = 1 := by
  classical
  choose y hy hA using hD
  let A : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨y i j, hy i j⟩
  let M : Matrix (Fin m) (Fin m) 𝒪[F] := 1 + (uniformizer F ^ (c + 1)) • A
  have hM : (𝒪[F]).subtype.mapMatrix M = (h : Matrix (Fin m) (Fin m) F) := by
    ext i j
    have := hA i j
    rw [Matrix.sub_apply, sub_eq_iff_eq_add] at this
    rw [this]
    simp [M, A, Matrix.one_apply, add_comm]
    split_ifs <;> simp
  have hdet : ((M.det : 𝒪[F]) : F) = (h : Matrix (Fin m) (Fin m) F).det := by
    rw [← hM]
    exact RingHom.map_det (𝒪[F]).subtype M
  let I : Ideal 𝒪[F] := Ideal.span {uniformizer F}
  have hq : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    have h0 : Ideal.Quotient.mk I (uniformizer F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    ext i j
    simp [M, h0, Matrix.one_apply]
  have hone : Ideal.Quotient.mk I M.det = 1 := by
    rw [RingHom.map_det, hq, Matrix.det_one]
  have hmem : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hone, map_one, sub_self]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  have hv : ValuativeRel.valuation F ((M.det : 𝒪[F]) : F) = 1 := by
    have e : ((M.det : 𝒪[F]) : F) = 1 + (z : F) * (uniformizer F : F) := by
      have := congrArg (fun w : 𝒪[F] => (w : F)) hz
      simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this
      rw [this]; ring
    rw [e]
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hz1 : ValuativeRel.valuation F (z : F) ≤ 1 := z.2
    calc ValuativeRel.valuation F (z : F) * ValuativeRel.valuation F (uniformizer F : F)
        ≤ 1 * ValuativeRel.valuation F (uniformizer F : F) := mul_le_mul_left hz1 _
      _ < 1 := by rw [one_mul]; exact valuation_uniformizer_lt_one F
  rw [← hdet]
  have hne : ((M.det : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  refine modulus_eq_one_of_integral hne ?_ ?_
  · exact (Valuation.mem_integer_iff _ _).2 hv.le
  · refine (Valuation.mem_integer_iff _ _).2 ?_
    rw [map_inv₀, hv, inv_one]

theorem div_col {n k c : ℕ} {y : Fin (k + 1) → F}
    (hy : ∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c * t) :
    Div c ((col n k y : Matrix (Fin n) (Fin n) F) - 1) := by
  intro i j
  have e : ((col n k y : Matrix (Fin n) (Fin n) F) - 1) i j = cM n k y i j := by
    show ((1 + cM n k y) - 1) i j = _
    rw [add_sub_cancel_left]
  rw [e]
  by_cases h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1
  · obtain ⟨t, ht, e'⟩ := hy ⟨i, h.2⟩
    refine ⟨t, ht, ?_⟩
    simp only [cM, Matrix.of_apply, dif_pos h]
    exact e'
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    simp only [cM, Matrix.of_apply, dif_neg h, mul_zero]

theorem stability_coefficients : L0 → L2 → ColumnsMirabolic → FormCoefficientStability := by
  intro h0 h2 h3 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hI u u'
  obtain ⟨cu, hcu⟩ := hρ u
  obtain ⟨cv, hcv⟩ := hρ u'
  obtain ⟨hadd, -, -, -, -, hext⟩ := h3 F μ ψ hψ n k hk
  have hfix : ∀ g : GL (Fin n) F, Div (max cu cv + 1) ((g : Matrix (Fin n) (Fin n) F) - 1) →
      ρ g u = u ∧ ρ g u' = u' := fun g hg =>
    ⟨hcu g (div_mono (by omega) hg), hcv g (div_mono (by omega) hg)⟩
  have hf1 : ∀ x y : Fin (k + 1) → F,
      (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (max cu cv + 1) * t) →
      B u' (ρ (col n k (x + y)) u) = B u' (ρ (col n k x) u) := by
    intro x y hy
    rw [hadd, map_mul, Module.End.mul_apply, (hfix _ (div_col hy)).1]
  have hf2 : ∀ h : GL (Fin (k + 1)) F,
      Div (max cu cv + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
      ∀ x, B u' (ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u) =
        B u' (ρ (col n k x) u) := by
    intro h hh x
    obtain ⟨g, hgP, hdet, hcomm, hdiv⟩ := hext h
    obtain ⟨gu, gu'⟩ := hfix g (hdiv _ hh)
    have hmod : Measures.modulus (g : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← hdet]
      exact modulus_det_eq_one h hh
    have e : ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u =
        ρ g (ρ (col n k x) u) := by
      have := congrArg (fun a => ρ a u) (hcomm x)
      simp only [map_mul, Module.End.mul_apply, gu] at this
      exact this.symm
    have q := hI.quasi g hgP u' (ρ (col n k x) u)
    rw [gu', hmod] at q
    rw [e, q]
    simp
  have hcont : Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
    have hϖ : ((uniformizer F : F) ^ (max cu cv + 1)) ≠ 0 := by
      refine pow_ne_zero _ fun h => ?_
      exact valuation_uniformizer_ne_zero F (by rw [h, map_zero])
    refine ⟨(fun z : Fin (k + 1) → F => ((uniformizer F : F) ^ (max cu cv + 1))⁻¹ • (z - x)) ⁻¹'
      (Measures.box F (Fin (k + 1))), Measures.isOpen_box.preimage (by fun_prop), ?_, ?_⟩
    · simpa using Measures.zero_mem_box
    · intro x' hx'
      have := hf1 x (x' - x) fun i => ⟨_, Measures.mem_box.1 hx' i, by
        simp [hϖ]⟩
      simpa using this
  exact ⟨hcont, max cu cv, fun g hg => h2 F μ ψ hψ k (max cu cv) (max cu cv + 1) _ hf1 hf2 g hg⟩

end GlobalTheory.CompanionTheory.JSBound
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationAeEqConvolution
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem mol_ae_lConv : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n))
    [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ x : Lp V 2 μ,
      (fun y : G n => Mol μ φ (⇑x) y.val) =ᵐ[μ] lConv μ V φ x := by
  intro n _ _ μ _ V _ _ _ hU φ hφ x
  obtain ⟨h1, h2⟩ := hU n μ
  have hφc : Continuous φ := hφ.1.continuous
  have hφv : Continuous (fun y : G n => φ y.val) := hφc.comp Units.continuous_val

  have hcont : Continuous (fun y : G n => φ y.val • lT μ V y x) :=
    hφv.smul (_root_.GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous n μ V hU x).2
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine ((GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n).isInducing.isCompact_preimage_iff
      ?_).2 hφ.2.1
    intro g hg
    have hd : g.det ≠ 0 := hφ.2.2 hg
    have hu : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hd)
    exact ⟨hu.unit, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val • lT μ V y x) := by
    refine HasCompactSupport.intro hK fun y hy => ?_
    have : φ y.val = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  have hint : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    hcont.integrable_of_hasCompactSupport hcs

  have hmul : Measurable (fun p : G n × G n => p.1⁻¹ * p.2) :=
    (continuous_fst.inv.mul continuous_snd).measurable
  have hF : AEStronglyMeasurable
      (Function.uncurry fun (y z : G n) => φ y.val • (x : G n → V) (y⁻¹ * z)) (μ.prod μ) := by
    refine StronglyMeasurable.aestronglyMeasurable ?_
    have a1 : StronglyMeasurable (fun p : G n × G n => φ p.1.val) :=
      (hφv.comp continuous_fst).stronglyMeasurable
    have a2 : StronglyMeasurable (fun p : G n × G n => (x : G n → V) (p.1⁻¹ * p.2)) :=
      (Lp.stronglyMeasurable x).comp_measurable hmul
    exact a1.smul a2
  have hae : ∀ᵐ y ∂μ, (φ y.val • lT μ V y x : Lp V 2 μ) =ᵐ[μ]
      fun z => φ y.val • (x : G n → V) (y⁻¹ * z) := by
    refine Eventually.of_forall fun y => ?_
    filter_upwards [Lp.coeFn_smul (φ y.val) (lT μ V y x), lT_coe μ y x] with z e1 e2
    rw [e1, Pi.smul_apply, e2]
  have key := _root_.GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq (G n) (G n) V μ μ (fun y : G n => φ y.val • lT μ V y x)
    (fun y z => φ y.val • (x : G n → V) (y⁻¹ * z)) hint hF hae
  have hconv : lConv μ V φ x = ∫ y : G n, φ y.val • lT μ V y x ∂μ := rfl
  rw [hconv]
  filter_upwards [key] with z hz
  rw [hz]

  let H : G n → V := fun u => φ (z.val * (u⁻¹ : G n).val) • (x : G n → V) u
  have e2 : ∫ u, H u ∂μ = ∫ u, H (u⁻¹ * z) ∂μ := by
    rw [integral_inv_eq_self (fun u => H (u * z)) μ, integral_mul_right_eq_self H z]
  show ∫ u, H u ∂μ = _
  rw [e2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have e3 : z.val * ((y⁻¹ * z)⁻¹ : G n).val = y.val := by
    rw [← Units.val_mul]
    congr 1
    group
  show φ (z.val * ((y⁻¹ * z)⁻¹ : G n).val) • (x : G n → V) (y⁻¹ * z) = _
  rw [e3]

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalityOfLatticeCharacter
section
open PositivityTheory.JacquetShalikaLocal
open MeasureTheory ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_integer_psi_mul_ne_one {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {b : F}
    (hb : b ∉ (valuation F).integer) :
    ∃ t ∈ (valuation F).integer, ψ (t * b) ≠ 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zero_mem _)
  have hvb : 1 < valuation F b := by
    rw [Valuation.mem_integer_iff, not_le] at hb
    exact hb
  have hvinv : valuation F b⁻¹ < 1 := ((valuation F).one_lt_val_iff hb0).mp hvb
  have hinvO : b⁻¹ ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff]
    exact hvinv.le
  have hynu : (⟨b⁻¹, hinvO⟩ : (valuation F).integer) ∈ IsLocalRing.maximalIdeal (valuation F).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (ne_of_lt hvinv) ((Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu)
  have hmax := GroundTheory.Automorphic.GLnLocal.maximalIdeal_pow_eq F 1
  rw [pow_one, pow_one] at hmax
  rw [hmax, Ideal.mem_span_singleton] at hynu
  obtain ⟨u, hu⟩ := hynu
  obtain ⟨x, hx, hψx⟩ := hψ.2.1
  refine ⟨(↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F), mul_mem hx u.2, ?_⟩
  have hu' : b⁻¹ = (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * (u : F) := by
    have h := congrArg Subtype.val hu
    simpa using h
  have hx' : (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b = x := by
    calc (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b
        = x * ((GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * u) * b := by ring
      _ = x * b⁻¹ * b := by rw [hu']
      _ = x := by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  rw [hx']
  exact hψx

theorem mem_lat_zero {m : ℕ} {x : Fin m → F} :
    x ∈ lat F m 0 ↔ ∀ i, x i ∈ (valuation F).integer := by
  simp only [lat, Set.mem_ofPred_eq, pow_zero, one_mul]

theorem orthogonality_of_lattice_character : L0 → L1 := by
  unfold L0 L1 ForF
  intro hL0 F _ _ _ _ _ _ μ _ ψ hψ m y
  have hL := hL0 F μ ψ hψ
  dsimp only at hL ⊢
  by_cases hy : ∀ i, y i ∈ (valuation F).integer
  · rw [if_pos hy]
    have hmeas : MeasurableSet (lat F m 0) := ((hL.2 m).1 0).2.2.1
    have h1 : Set.EqOn (fun ξ : Fin m → F => ψ (ξ ⬝ᵥ y)) (fun _ => (1 : ℂ)) (lat F m 0) := by
      intro ξ hξ
      rw [mem_lat_zero] at hξ
      refine hψ.1 _ ?_
      unfold dotProduct
      exact sum_mem fun j _ => mul_mem (hξ j) (hy j)
    rw [setIntegral_congr_fun hmeas h1, setIntegral_const]
    simp
  · rw [if_neg hy]
    simp only [not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    obtain ⟨t, ht, hne⟩ := exists_integer_psi_mul_ne_one hψ hi
    have hsO : ∀ j, (Pi.single i t : Fin m → F) j ∈ (valuation F).integer := by
      intro j
      by_cases hj : j = i
      · rw [hj, Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    have hinv : (fun ξ : Fin m → F => Pi.single i t + ξ) ⁻¹' lat F m 0 = lat F m 0 := by
      ext ξ
      simp only [Set.mem_preimage, mem_lat_zero, Pi.add_apply]
      constructor
      · intro h j
        have h2 := sub_mem (h j) (hsO j)
        simpa using h2
      · intro h j
        exact add_mem (hsO j) (h j)
    have hsd : (Pi.single i t : Fin m → F) ⬝ᵥ y = t * y i := by
      first
        | exact single_dotProduct t i
        | simp [dotProduct, Pi.single_apply]
    have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) (Pi.single i t : Fin m → F)
    have hemb := measurableEmbedding_addLeft (Pi.single i t : Fin m → F)
    have hshift := hmp.setIntegral_preimage_emb hemb (fun ξ => ψ (ξ ⬝ᵥ y)) (lat F m 0)
    rw [hinv] at hshift
    simp only [add_dotProduct, AddChar.map_add_eq_mul, hsd] at hshift
    rw [integral_const_mul] at hshift
    have h0 : (∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂Measure.pi fun _ => μ) * (ψ (t * y i) - 1) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)

end GlobalTheory.CompanionTheory.SatakeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightTranslateDerivativeIntegral
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA.IntForm

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n :=
  ((isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem Rd_continuousOn {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    ContinuousOn (Rd X f) (GLs n) :=
  (GlobalTheory.CompanionTheory.SobGL.Smooth.contDiffOn_fderiv_apply' (GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n) hf
    (GlobalTheory.CompanionTheory.SobGL.Smooth.mulRight' X).contDiff.contDiffOn).continuousOn

theorem hasDerivAt_curve {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) (z : G n) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (z.val * (expC X r).val)) (Rd X f (z.val * (expC X s).val)) s := by
  have hγ := (_root_.GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt n X).2 s
  let L : CLof (Mat n) (Mat n) := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z.val)
  have h1 : HasDerivAt (fun r : ℝ => z.val * (expC X r).val) (z.val * ((expC X s).val * X)) s :=
    L.hasFDerivAt.comp_hasDerivAt s hγ
  have hw : (z.val * (expC X s).val) ∈ GLs n := val_mem_GLs (z * expC X s)
  have h2 : HasFDerivAt f (fderiv ℝ f (z.val * (expC X s).val)) (z.val * (expC X s).val) :=
    ((hf.contDiffAt ((GlobalTheory.CompanionTheory.SobGL.Smooth.isOpen_GLs' n).mem_nhds hw)).differentiableAt
      (by simp)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt s h1
  have e : z.val * ((expC X s).val * X) = (z.val * (expC X s).val) * X := (Matrix.mul_assoc _ _ _).symm
  rw [e] at h3
  exact h3

theorem continuous_F {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) :
    Continuous (fun p : ℝ × G n => Rd X f (p.2.val * (expC X p.1).val)) := by
  have hc : Continuous (fun p : ℝ × G n => p.2 * expC X p.1) :=
    continuous_snd.mul ((_root_.GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt n X).1.comp continuous_fst)
  have hv : Continuous (fun p : ℝ × G n => (p.2 * expC X p.1).val) := Units.continuous_val.comp hc
  exact (Rd_continuousOn hf X).comp_continuous hv (fun p => val_mem_GLs (p.2 * expC X p.1))

section L2

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_cls_ae (hU : Unimod) {g : Mat n → V} (hg : MemLp (fun y : G n => g y.val) 2 μ) (h : G n) :
    rR μ V h (cls μ g) =ᵐ[μ] fun z => g (z.val * h.val) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have h1 := hm.quasiMeasurePreserving.ae_eq_comp (coe_cls μ hg)
  filter_upwards [rR_coe μ hU h (cls μ g), h1] with z hz1 hz2
  rw [hz1]
  simpa using hz2

theorem setIntegral_ae (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hg : MemLp (fun y : G n => Rd X f y.val) 2 μ) (a b : ℝ) :
    (⇑(∫ s in Set.Ioc a b, rR μ V (expC X s) (cls μ (Rd X f))) : G n → V) =ᵐ[μ]
      fun z => ∫ s in Set.Ioc a b, Rd X f (z.val * (expC X s).val) := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    ((_root_.GlobalTheory.CompanionTheory.PresSobA.translations_strongly_continuous n μ V hU (cls μ (Rd X f))).1).comp (_root_.GlobalTheory.CompanionTheory.PresSobA.ExpCurve.expC_continuous_hasDerivAt n X).1
  have hint : Integrable (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f)))
      (volume.restrict (Set.Ioc a b)) := hc.integrableOn_Ioc
  refine _root_.GlobalTheory.CompanionTheory.LpBochner.coe_integral_ae_eq ℝ (G n) V (volume.restrict (Set.Ioc a b)) μ _
    (fun s z => Rd X f (z.val * (expC X s).val)) hint ?_ ?_
  · have : Continuous (Function.uncurry fun (s : ℝ) (z : G n) => Rd X f (z.val * (expC X s).val)) :=
      continuous_F hf X
    exact this.aestronglyMeasurable
  · exact ae_of_all _ fun s => rR_cls_ae μ hU hg (expC X s)

end L2

theorem rR_sub_cls_eq_integral : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (f : Mat n → V) (X : Mat n), ContDiffOn ℝ ∞ f (GLs n) → MemLp (fun y : G n => f y.val) 2 μ → MemLp (fun y : G n => Rd X f y.val) 2 μ → ∀ t : ℝ, rR μ V (expC X t) (cls μ f) - cls μ f = ∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f)) := by
  intro n _ _ μ _ V _ _ _ hU f X hf hfm hg t
  apply Lp.ext
  rw [intervalIntegral]
  have hsub1 := Lp.coeFn_sub (rR μ V (expC X t) (cls μ f)) (cls μ f)
  have hsub2 := Lp.coeFn_sub (∫ s in Set.Ioc 0 t, rR μ V (expC X s) (cls μ (Rd X f)))
    (∫ s in Set.Ioc t 0, rR μ V (expC X s) (cls μ (Rd X f)))
  filter_upwards [hsub1, hsub2, rR_cls_ae μ hU hfm (expC X t), coe_cls μ hfm,
    setIntegral_ae μ hU X hf hg 0 t, setIntegral_ae μ hU X hf hg t 0] with z h1 h2 h3 h4 h5 h6
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4, h5, h6]
  have hcont : Continuous (fun s : ℝ => Rd X f (z.val * (expC X s).val)) :=
    (continuous_F hf X).comp (Continuous.prodMk continuous_id continuous_const)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (f := fun r : ℝ => f (z.val * (expC X r).val))
    (f' := fun s : ℝ => Rd X f (z.val * (expC X s).val))
    (fun s _ => hasDerivAt_curve hf X z s) (hcont.intervalIntegrable _ _)
  rw [intervalIntegral] at key
  rw [key]
  simp [expC_zero]

end GlobalTheory.CompanionTheory.PresSobA.IntForm
end
end

