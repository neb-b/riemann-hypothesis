module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import GroundTheory.LocalFields.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DefBridge
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
private theorem iw_eq (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) :
    PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) := by
  ext g
  constructor
  · rintro ⟨⟨u, rfl⟩, hl⟩
    refine ⟨u, ?_, rfl⟩
    change residueReduction F n u ∈ borel n _
    rw [mem_borel_iff]
    intro i j hij
    rw [residueReduction_apply]
    exact (residue_eq_zero_iff_valuation_lt_one F (u i j)).mpr (hl i j hij)
  · intro hg
    exact ⟨iwahori_le_integralGL F n hg, ((mem_iwahori_iff F n).1 hg).2.1⟩

open ValuativeRel in
private theorem unif (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    PositivityTheory.Rg.Tf.Loc.IsUniformiser ((uniformizerUnit F : Fˣ) : F) := by
  refine ⟨valuation_uniformizer_lt_one F, Units.ne_zero _, fun x hx => ?_⟩
  let y : 𝒪[F] := ⟨x, (Valuation.mem_integer_iff _ _).mpr hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (residue_eq_zero_iff_valuation_lt_one F y).mpr hx
  have h1 := (mem_maximalIdeal_pow_iff F (m := 1) (y := y)).1 (by rwa [pow_one])
  simpa using h1

open ValuativeRel in
private theorem diag_mem (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
    (t : Fin n → Fˣ) (ht : ∀ i, valuation F ((t i : Fˣ) : F) = 1) : diagGL F n t ∈ iwahori F n := by
  have he : ∀ i j, ((diagGL F n t : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      Matrix.diagonal (fun i => ((t i : Fˣ) : F)) i j := fun i j => rfl
  refine (mem_iwahori_iff F n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [he]
    by_cases h : i = j
    · subst h
      simp [ht]
    · simp [Matrix.diagonal_apply_ne _ h]
  · rw [he, Matrix.diagonal_apply_ne _ hij.ne']
    simp
  · rw [he]
    simp [ht]

theorem UpperTheory.ConvolutionTheory.H.defBridge :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
      PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) F = integralGL F n ∧
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F = (iwahori F n : Set (GL (Fin n) F)) ∧
      (∃ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F)) ∧
      ∀ ϖ : Fˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : F) → ∀ a : Fin n → ℤ,
        PositivityTheory.Rg.Tf.Loc.iwahoriFn F (PositivityTheory.Rg.Tf.Loc.diagPow ϖ a) = uFn F a := by
  intro F _ _ _ _ n
  have hI := iw_eq F n
  refine ⟨rfl, hI, ⟨uniformizerUnit F, unif F⟩, fun ϖ hϖ a => ?_⟩
  have h0 := unif F
  have hv : ValuativeRel.valuation F (ϖ : F) = ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) :=
    le_antisymm (h0.2.2 _ hϖ.1) (hϖ.2.2 _ h0.1)
  set u : Fˣ := ϖ * (uniformizerUnit F)⁻¹ with hu
  have hu1 : ValuativeRel.valuation F (u : F) = 1 := by
    have hne : ValuativeRel.valuation F ((uniformizerUnit F : Fˣ) : F) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
    rw [hu, Units.val_mul, map_mul, hv, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_cancel₀ hne]
  have hd : diagGL F n (fun i => u ^ a i) ∈ iwahori F n := by
    refine diag_mem F n _ fun i => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hu1, one_zpow]
  have hfac : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = torusPow F n a * diagGL F n (fun i => u ^ a i) := by
    have : PositivityTheory.Rg.Tf.Loc.diagPow ϖ a = diagGL F n (fun i => ϖ ^ a i) := Units.ext rfl
    rw [this, torusPow, ← map_mul]
    apply congrArg (diagGL F n)
    funext i
    change ϖ ^ a i = uniformizerUnit F ^ a i * u ^ a i
    rw [← mul_zpow, hu, mul_left_comm, mul_inv_cancel, mul_one]
  unfold PositivityTheory.Rg.Tf.Loc.iwahoriFn uFn dco
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, hI, SetLike.mem_coe, hfac]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, _ * y, mul_mem hd hy, by simp only [mul_assoc]⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, (diagGL F n (fun i => u ^ a i))⁻¹ * y, mul_mem (inv_mem hd) hy, by simp only [mul_assoc, mul_inv_cancel_left]⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SigInv
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

section

variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] {n : ℕ}

private theorem val_sig (σ : E ≃ₐ[k] E) (x : E) :
    ValuativeRel.valuation E (σ x) = ValuativeRel.valuation E x :=
  GroundTheory.LocalField.valuation_algEquiv_apply k E σ x

private theorem sig_apply (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) (i j : Fin n) :
    ((PositivityTheory.Rg.Tf.Loc.sigmaGL σ g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j =
      σ ((g : Matrix (Fin n) (Fin n) E) i j) := rfl

private theorem sig_symm (σ : E ≃ₐ[k] E) (g : GL (Fin n) E) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ.symm (PositivityTheory.Rg.Tf.Loc.sigmaGL σ g) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [sig_apply, sig_apply, AlgEquiv.symm_apply_apply]

private theorem sig_mem_K (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ integralGL E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ integralGL E n := by
  rw [mem_integralGL_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.1 i j
  · rw [← map_inv, sig_apply, Valuation.mem_integer_iff, val_sig]
    exact hg.2 i j

private theorem sig_mem_I (σ : E ≃ₐ[k] E) {g : GL (Fin n) E} (hg : g ∈ iwahori E n) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ iwahori E n := by
  rw [mem_iwahori_iff] at hg ⊢
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [sig_apply, val_sig]
    exact hg.1 i j
  · rw [sig_apply, val_sig]
    exact hg.2.1 i j h
  · rw [sig_apply, val_sig]
    exact hg.2.2 i

private theorem diag_mem_I {d : Fin n → Eˣ} (hd : ∀ i, ValuativeRel.valuation E (d i : E) = 1) :
    diagGL E n d ∈ iwahori E n := by
  rw [mem_iwahori_iff]
  refine ⟨fun i j => ?_, fun i j h => ?_, fun i => ?_⟩
  · rw [coe_diagGL]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, hd]
    · rw [Matrix.diagonal_apply_ne _ e, map_zero]
      exact zero_le'
  · rw [coe_diagGL, Matrix.diagonal_apply_ne _ h.ne', map_zero]
    exact zero_lt_one
  · rw [coe_diagGL, Matrix.diagonal_apply_eq, hd]

private theorem sig_torusPow (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) :
    ∃ u ∈ iwahori E n, PositivityTheory.Rg.Tf.Loc.sigmaGL σ (torusPow E n a) = torusPow E n a * u := by
  have h0 : (GLnLocal.uniformizer E : E) ≠ 0 := (uniformizerUnit E).ne_zero
  have hs : σ (GLnLocal.uniformizer E : E) ≠ 0 := by
    rwa [Ne, map_eq_zero_iff σ σ.injective]
  let v : Eˣ := Units.mk0 (σ (GLnLocal.uniformizer E : E) / (GLnLocal.uniformizer E : E)) (div_ne_zero hs h0)
  have hv : ValuativeRel.valuation E (v : E) = 1 := by
    rw [Units.val_mk0, map_div₀, val_sig, div_self]
    exact (Valuation.ne_zero_iff _).2 h0
  refine ⟨diagGL E n fun i => v ^ a i, diag_mem_I fun i => ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hv, one_zpow]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [sig_apply, Units.val_mul, coe_torusPow, coe_diagGL, Matrix.diagonal_mul_diagonal]
    by_cases e : i = j
    · subst e
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, Units.val_zpow_eq_zpow_val,
        Units.val_mk0, div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ h0)]
    · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ e, map_zero]

private theorem sig_mem_dco (σ : E ≃ₐ[k] E) (a : Fin n → ℤ) {g : GL (Fin n) E} (h : g ∈ dco E a) :
    PositivityTheory.Rg.Tf.Loc.sigmaGL σ g ∈ dco E a := by
  obtain ⟨x, hx, y, hy, rfl⟩ := h
  obtain ⟨u, hu, e⟩ := sig_torusPow σ a
  refine ⟨PositivityTheory.Rg.Tf.Loc.sigmaGL σ x, sig_mem_I σ hx, u * PositivityTheory.Rg.Tf.Loc.sigmaGL σ y,
    mul_mem hu (sig_mem_I σ hy), ?_⟩
  rw [map_mul, map_mul, e]
  simp only [mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.H.sigInv :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E) (n : ℕ) (x : GL (Fin n) E),
      oneK E n (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = oneK E n x ∧ ∀ a : Fin n → ℤ, uFn E a (PositivityTheory.Rg.Tf.Loc.sigmaGL σ x) = uFn E a x := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ n x
  have hK : PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ integralGL E n ↔ x ∈ integralGL E n :=
    ⟨fun h => by simpa only [sig_symm] using sig_mem_K σ.symm h, sig_mem_K σ⟩
  have hD : ∀ a : Fin n → ℤ, PositivityTheory.Rg.Tf.Loc.sigmaGL σ x ∈ dco E a ↔ x ∈ dco E a := fun a =>
    ⟨fun h => by simpa only [sig_symm] using sig_mem_dco σ.symm a h, sig_mem_dco σ a⟩
  refine ⟨?_, fun a => ?_⟩
  · unfold oneK
    by_cases h : x ∈ integralGL E n
    · rw [Set.indicator_of_mem (SetLike.mem_coe.2 (hK.2 h)), Set.indicator_of_mem (SetLike.mem_coe.2 h)]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h (hK.1 h')), Set.indicator_of_notMem h]
  · unfold uFn
    by_cases h : x ∈ dco E a
    · rw [Set.indicator_of_mem ((hD a).2 h), Set.indicator_of_mem h]
      rfl
    · rw [Set.indicator_of_notMem (fun h' => h ((hD a).1 h')), Set.indicator_of_notMem h]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.UnrQ
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
theorem UpperTheory.ConvolutionTheory.H.unrQ :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      qF E = qF k ^ Module.finrank k E ∧
      ∀ ϖ : kˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : k) → PositivityTheory.Rg.Tf.Loc.IsUniformiser (algebraMap k E (ϖ : k)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨π, hπ1, hπ2⟩
  have hlt : ∀ a : k, valuation E (algebraMap k E a) < 1 ↔ valuation k a < 1 := fun a =>
    Valuation.HasExtension.val_map_lt_one_iff (valuation k) (valuation E) a
  have hπk : valuation k π < 1 := (hlt π).1 hπ1
  refine ⟨?_, fun ϖ ⟨h1, h2, h3⟩ => ⟨(hlt _).2 h1, (map_ne_zero _).2 h2, fun x hx => (hπ2 x hx).trans ?_⟩⟩
  · have hmem : ∀ {F : Type} [Field F] [ValuativeRel F] (x : 𝒪[F]),
        x ∈ IsLocalRing.maximalIdeal 𝒪[F] ↔ valuation F (x : F) < 1 := fun x =>
      Valuation.mem_maximalIdeal_iff _ _
    let p : 𝒪[k] := ⟨π, hπk.le⟩
    have hle : IsLocalRing.maximalIdeal 𝒪[E] ≤
        (IsLocalRing.maximalIdeal 𝒪[k]).map (algebraMap 𝒪[k] 𝒪[E]) := by
      intro x hx
      have hd : algebraMap 𝒪[k] 𝒪[E] p ∣ x :=
        (Valuation.integer.integers (valuation E)).le_iff_dvd.1 (hπ2 x ((hmem x).1 hx))
      obtain ⟨c, rfl⟩ := hd
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem p).2 hπk))
    rw [GroundTheory.LocalField.map_maximalIdeal] at hle
    have he : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) = 1 := by
      have hpos : 0 < (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) :=
        GroundTheory.LocalField.ramificationIndex_pos k E
      by_contra hne
      have h2 : 2 ≤ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation k))) := by omega
      have h3 := hle.trans (Ideal.pow_le_pow_right h2)
      have h4 := Ideal.pow_succ_lt_pow (GroundTheory.LocalField.maximalIdeal_ne_bot E) 1
      rw [pow_one] at h4
      exact not_le_of_gt h4 h3
    have hf := (GroundTheory.LocalField.isUnramified_iff_finrank_residueField k E).1 ⟨he⟩
    rw [← hf]
    exact Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := 𝓀[E])
  · exact (Valuation.HasExtension.val_map_le_iff (valuation k) (valuation E) _ _).2 (h3 π hπk)
end

