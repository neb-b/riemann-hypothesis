module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.EventuallyNotMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0065
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0068
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CountQuadraticOfHyp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
  UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Br

private theorem bit_of_fibre {X U : Type} (R : X → X → Prop) (hs : ∀ x y, R x y → R y x)
    (ht : ∀ x y z, R x y → R y z → R x z) (Q : X → U → Prop) (hQ : ∀ x, ∃ u, Q x u)
    (h2 : ∀ u x₀ x x', Q x₀ u → Q x u → Q x' u → ¬ R x₀ x → ¬ R x₀ x' → R x x') :
    ∃ g : X → U × Bool, (∀ x x', g x = g x' → R x x') ∧ ∀ x, Q x (g x).1 := by
  classical
  choose u hu using hQ
  have hex : ∀ x : X, ∃ y, Q y (u x) := fun x => ⟨x, hu x⟩
  refine ⟨fun x => (u x, decide (R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x)), fun x x' h => ?_, hu⟩
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h
  simp only at h1 h3
  have h0 := Classical.epsilon_spec (hex x)
  rw [← h1, decide_eq_decide] at h3
  have hx' : Q x' (u x) := h1 ▸ hu x'
  by_cases hc : R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x
  · exact ht _ _ _ (hs _ _ hc) (h3.1 hc)
  · exact h2 _ _ _ _ h0 (hu x) hx' hc fun h4 => hc (h3.2 h4)

private theorem iso_symm {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r') :
    RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg s]; group⟩

private theorem iso_trans {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' r'' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (h' : RepIso r' r'') : RepIso r r'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' * g, fun s => by rw [hg' s, hg s]; group⟩

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]

private theorem exists_over (K : Type) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ), v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  haveI := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := UpperTheory.exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩

private theorem not_mem_of_coprime {F : Type} [Field F] [NumberField F] {p a : ℕ} (h : p.Coprime a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) : (a : 𝓞 F) ∉ w.asIdeal := fun ha => by
  obtain ⟨x, y, e⟩ : IsCoprime (p : 𝓞 F) (a : 𝓞 F) := Nat.Coprime.cast h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw)
    (w.asIdeal.mul_mem_left _ ha)))

private theorem exists_avoid {N : ℕ} (d : Fin (N + 1) → ℤ) (hd : ∀ i j, i ≠ j → IsCoprime (d i) (d j)) {p : ℕ} (hp : p.Prime) :
    ∃ u : Fin N → Fin (N + 1), Function.Injective u ∧ ∀ i, ¬ (p : ℤ) ∣ d (u i) := by
  by_cases h : ∃ j, (p : ℤ) ∣ d j
  · obtain ⟨j, hj⟩ := h
    refine ⟨j.succAbove, Fin.succAbove_right_injective, fun i hi => ?_⟩
    have := (hd _ _ (Fin.succAbove_ne j i)).isUnit_of_dvd' hi hj
    exact (Nat.prime_iff_prime_int.1 hp).not_unit this
  · exact ⟨Fin.succ, Fin.succ_injective _, fun i hi => h ⟨_, hi⟩⟩

private theorem map_inv_inv (B : Multiset ℂ) : (B.map (·⁻¹)).map (·⁻¹) = B := by
  rw [Multiset.map_map]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.DownZero
section
noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd
open UpperHalfPlane hiding I

namespace UpperTheory.V.Br

private theorem aff_mul' (y z : ℝˣ) (x t : ℝ) : aff y x * aff z t = aff (y * z) (x + y * t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem aff_one' : aff (1 : ℝˣ) (0 : ℝ) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_inv' (y : ℝˣ) (x : ℝ) : (aff y x)⁻¹ = aff y⁻¹ (-((y⁻¹ : ℝˣ) * x)) := by
  refine inv_eq_of_mul_eq_one_left ?_
  rw [aff_mul', inv_mul_cancel, neg_add_cancel, aff_one']

private theorem down_vadd (k : ℕ) (φ : GA ℚ 2 → ℂ) (t : ℝ) (z : ℍ) :
    down k φ (t +ᵥ z) = ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) *
      φ (upR (aff 1 t) * (1 * upR (aff (Units.mk0 z.im z.im_pos.ne') z.re))) := by
  rw [one_mul, ← map_mul, aff_mul', one_mul]
  unfold down
  have h : Units.mk0 (t +ᵥ z).im (t +ᵥ z).im_pos.ne' = Units.mk0 z.im z.im_pos.ne' := Units.ext (vadd_im t z)
  rw [h, vadd_im, vadd_re]
  simp

private theorem norm_aff (y : ℝˣ) (x B : ℝ) (h1 : 1 ≤ B) (hy : |(y : ℝ)| ≤ B) (hx : |x| ≤ B) :
    ‖TR.toL (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff y x)).val‖ ≤ B := by
  have h0 : 0 ≤ B := zero_le_one.trans h1
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j =>
    (pi_norm_le_iff_of_nonneg h0).2 fun v => ?_
  change |(aff y x).val i j| ≤ B
  fin_cases i <;> fin_cases j <;> simp [aff, *]

private theorem height_aff (N : ℕ) (hN : 0 < N) (z : ℍ) (h1 : 1 ≤ z.im) (h2 : |z.re| ≤ N) :
    TR.height (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 z.im z.im_pos.ne') z.re)) ≤
      3 * N * z.im := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hB : (1 : ℝ) ≤ N * z.im := by nlinarith
  have hB2 : (N : ℝ) ≤ N * z.im := by nlinarith
  have hi : |(z.im)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.2 z.im_pos)]; exact inv_le_one_of_one_le₀ h1
  have a1 := norm_aff (Units.mk0 z.im z.im_pos.ne') z.re (N * z.im) hB
    (by rw [Units.val_mk0, abs_of_pos z.im_pos]; nlinarith) (h2.trans hB2)
  have a2 := norm_aff (Units.mk0 z.im z.im_pos.ne')⁻¹ (-(((Units.mk0 z.im z.im_pos.ne')⁻¹ : ℝˣ) * z.re)) (N * z.im) hB
    (by rw [Units.val_inv_eq_inv_val, Units.val_mk0]; exact hi.trans hB)
    (by
      rw [Units.val_inv_eq_inv_val, Units.val_mk0, abs_neg, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hi).trans (h2.trans hB2))
  unfold TR.height
  rw [← map_inv, aff_inv']
  linarith

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.downZero :
    UpperTheory.V.Br.DownZero := by
  intro k φ hc hl
  obtain ⟨N, hN, hm⟩ := cuspMean φ hc 1
  obtain ⟨C, m, hg⟩ := hc.1.growth 1
  refine perZero _ N hN (downHol k φ hl) (fun z => ?_) ⟨|C| * (3 * N) ^ m, m, fun z h1 h2 => ?_⟩ fun z => ?_
  · have h := (hm (aff (Units.mk0 z.im z.im_pos.ne') z.re)).1 0
    have h0 := down_vadd k φ.1 0 z
    rw [zero_vadd] at h0
    rw [down_vadd, h0]
    simp only [zero_add] at h
    rw [h]
  · have h := hg (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ)) (aff (Units.mk0 z.im z.im_pos.ne') z.re))
    rw [one_mul] at h
    have h3 := height_aff N hN z h1 h2
    have h4 : 0 ≤ TR.height (Matrix.GeneralLinearGroup.map (algebraMap ℝ (TR.Rinf ℚ))
        (aff (Units.mk0 z.im z.im_pos.ne') z.re)) := by
      unfold TR.height; positivity
    have h5 : z.im ^ (-((k : ℝ) / 2)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (neg_nonpos.2 (by positivity))
    unfold down
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg z.im_pos.le _)]
    refine (mul_le_of_le_one_left (norm_nonneg _) h5).trans (h.trans ?_)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ h4 h3 m) (pow_nonneg h4 m) (abs_nonneg C)
  · simp only [down_vadd]
    rw [intervalIntegral.integral_const_mul, (hm _).2, mul_zero]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.FinOfKer
section
open NumberField IsDedekindDomain MeasureTheory Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Eis

private theorem fin_of_ker {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Finite ι] (P Q : Set V) (h0 : (0 : V) ∈ P)
    (hP : ∀ x y (z : ℂ), x ∈ P → y ∈ P → x + z • y ∈ P) (hQ : FiniteDimensional ℂ (Submodule.span ℂ Q)) (L : V → ι → ℂ)
    (hL0 : L 0 = 0) (hL : ∀ x y (z : ℂ), x ∈ P → y ∈ P → L (x + z • y) = L x + z • L y) (hk : ∀ x ∈ P, L x = 0 → x ∈ Q) :
    FiniteDimensional ℂ (Submodule.span ℂ P) := by
  let W : Submodule ℂ V :=
    { carrier := P
      zero_mem' := h0
      add_mem' := fun {x y} hx hy => by simpa using hP x y 1 hx hy
      smul_mem' := fun z y hy => by simpa using hP 0 y z h0 hy }
  have hW : Submodule.span ℂ P = W := Submodule.span_eq W
  rw [hW]
  let f : W →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun x => L x.1
      map_add' := fun x y => by simpa using hL x.1 y.1 1 x.2 y.2
      map_smul' := fun z y => by simpa [hL0] using hL 0 y.1 z h0 y.2 }
  let j : LinearMap.ker f →ₗ[ℂ] Submodule.span ℂ Q :=
    LinearMap.codRestrict _ (W.subtype.comp (LinearMap.ker f).subtype) fun x =>
      Submodule.subset_span (hk _ x.1.2 x.2)
  have hj : Function.Injective j := fun x y h => by
    have e := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext e)
  haveI : Module.Finite ℂ (LinearMap.ker f) := Module.Finite.of_injective j hj
  haveI : Module.Finite ℂ (W ⧸ LinearMap.ker f) := Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker f)

theorem UpperTheory.V.Br.holFin0 :
    UpperTheory.V.Sd.HolFin := by
  intro F _ _ _ k c hc ω hω
  obtain ⟨⟨M, hM, hlev⟩, hfin⟩ := UpperTheory.V.Br.holCuspFin F k c hc ω hω
  obtain ⟨S, hS, hgen⟩ := UpperTheory.V.Br.cuspSet F M hM
  obtain ⟨_, _, μ, _, D, hD, hone⟩ := UpperTheory.V.Br.ctOne F
  obtain ⟨h0, -, hadd, -⟩ := UpperTheory.V.Sd.holLin F k c ω
  have hint : ∀ φ : TR.Sm F 2, IsHol k c ω φ → ∀ g, IntegrableOn (fun x : NA F => φ.1 (unip x * g)) D μ := fun φ hφ =>
    (UpperTheory.eisenstein_constantTerm_of_periodMean_of_upperBlock UpperTheory.periodic_integral_fundamentalDomain_invariant UpperTheory.eisenstein_constantTerm_upperBlock F μ D hD φ.1 (UpperTheory.eisenstein_smooth_continuous F 2 φ hφ.aut.level) hφ.aut.left).1
  haveI : Finite S := hS
  refine fin_of_ker _ _ h0 hadd hfin (fun φ (s : S) => cterm μ D φ.1 s.1) ?_ (fun φ ψ z hφ hψ => ?_) fun φ hφ h => ?_
  · funext s
    simp [cterm]
  · funext s
    simp only [cterm, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (hint φ hφ s.1) ((hint ψ hψ s.1).const_mul z), integral_const_mul]
  · have hu := hgen {g | cterm μ D φ.1 g = 0} (fun s hs => congrFun h ⟨s, hs⟩)
      (UpperTheory.V.Br.ctMoves F μ D hD k c ω hω φ hφ M (hlev φ hφ))
    exact ⟨hφ, hφ.aut, hone φ.1 hφ.aut.left fun g => (hu.ge (Set.mem_univ g) :)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec
section
noncomputable section

open NumberField UpperTheory.V UpperTheory.V.Af Complex

namespace UpperTheory.V.Br

private theorem low_of {V : Type} [AddCommGroup V] [Module ℂ V] (A B C J : Module.End ℂ V) (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ)
    (hk : 3 ≤ k) (hAB : ∀ x, A (B x) = B (A x) + B x) (hAC : ∀ x, A (C x) = C (A x) - C x)
    (hBC : ∀ x, B (C x) = C (B x) + (2 : ℂ) • A x)
    (hCas : ∀ x, C (B x) = ((k : ℂ) * (k - 2) / 4) • x - A (A x) - A x)
    (hH : ∀ x, H x x = 0 → x = 0) (hA : ∀ x y, H (A x) y = -H x (A y)) (hB : ∀ x y, H (B x) y = -H x (B y))
    (hC : ∀ x y, H (C x) y = -H x (C y))
    (hJ : ∀ x, J x = 0 → x = 0) (hJA : ∀ x, A (J x) = J (A x)) (hJB : ∀ x, B (J x) = -J (B x)) (hJC : ∀ x, C (J x) = -J (C x))
    (hw : ∃ x, x ≠ 0 ∧ ∃ n : ℤ, B x - C x = (I * n) • x) :
    ∃ x, x ≠ 0 ∧ B x - C x = (I * k) • x ∧ (2 : ℂ) • A x = I • (B x + C x) := by
  have hI : I * I = -1 := I_mul_I
  have key := sl2Low V ((-I) • (B - C)) (A + (I / 2) • (B + C)) (A - (I / 2) • (B + C)) H k hk ?_ ?_ ?_ ?_ hH ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := key
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨x, hx, ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [this, h1, smul_smul]
      · linear_combination (norm := module) (2 : ℂ) • h2
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨J x, fun h => hx (hJ x h), ?_, ?_⟩
      · have : B x - C x = I • ((-I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [h1] at this
        have h3 := congrArg J this
        simp only [map_sub, map_smul] at h3
        rw [hJB, hJC]
        linear_combination (norm := module) -h3
      · have h3 := congrArg J h2
        simp only [map_add (f := _), map_smul, map_zero] at h3
        rw [hJA, hJB, hJC]
        linear_combination (norm := module) (2 : ℂ) • h3
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, map_add (f := _), map_sub, map_smul,
      Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · intro x y
    simp [hB, hC]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · intro x y
    simp [hA, hB, hC, map_ofNat]
    ring
  · obtain ⟨x, hx, n, h⟩ := hw
    refine ⟨x, hx, n, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h, smul_smul]
    congr 1
    grind

private def eps : TR.Kinf ℚ 2 :=
  ⟨Matrix.diagonal ![-1, 1], by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

private theorem eps_Eop (v : InfinitePlace ℚ) (i j : Fin 2) (φ : TR.Sm ℚ 2) :
    TR.cptRep ℚ 2 eps (TR.Eop v i j φ) = (if i = j then 1 else -1 : ℂ) • TR.Eop v i j (TR.cptRep ℚ 2 eps φ) := by
  have h := LinearMap.congr_fun (TR.Cen.rt_Eop (Unitary.toUnits eps) v i j) φ
  have e1 : (Unitary.toUnits eps).val = Matrix.diagonal ![-1, 1] := rfl
  have e2 : ((Unitary.toUnits eps)⁻¹).val = Matrix.diagonal ![-1, 1] := by
    change star (Matrix.diagonal ![-1, 1] : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) = _
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
  rw [e1, e2] at h
  refine h.trans ?_
  change _ = _ • TR.Eop v i j (TR.rt ℚ 2 (TR.infGL ℚ 2 (Unitary.toUnits eps)) φ)
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two]

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.holVec :
    UpperTheory.V.Br.HolVec := by
  classical
  intro k hk π hπ H hH
  let v : InfinitePlace ℚ := default
  have hv : ∀ w : InfinitePlace ℚ, w = v := fun w => Subsingleton.elim _ _
  let E : Fin 2 → Fin 2 → Module.End ℂ π.V := fun i j => (TR.Eop v i j).restrict fun φ h => π.stable (.lie _) φ h
  have hE : ∀ i j x, (E i j x).1 = TR.Eop v i j x.1 := fun _ _ _ => rfl
  have hcap := capTwo ℚ π v _ _ (hπ v)
  have hD : ∀ φ ∈ π.V, TR.Eop v 1 1 φ = -TR.Eop v 0 0 φ := fun φ hφ => by
    have := (hcap φ hφ).1
    rw [add_neg_cancel, zero_smul] at this
    exact eq_neg_of_add_eq_zero_right this
  have hrel : ∀ i j k l φ, _ := fun i j k l (φ : TR.Sm ℚ 2) => LinearMap.congr_fun (TR.glRel_Eop (a := 2) v i j k l) φ
  have hadj : ∀ i j x y, H (E i j x) y = -H x (E i j y) := fun i j x y => eq_neg_of_add_eq_zero_left (hH.lie _ x y)
  have hJ : ∀ i j x, π.op (.cpt eps) (E i j x) = (if i = j then 1 else -1 : ℂ) • E i j (π.op (.cpt eps) x) := fun i j x =>
    Subtype.ext (eps_Eop v i j x.1)
  have hBC : ∀ x, E 0 1 (E 1 0 x) = E 1 0 (E 0 1 x) + (2 : ℂ) • E 0 0 x := fun x => by
    refine Subtype.ext ?_
    have h := hrel 0 1 1 0 x.1
    simp only [if_true, LinearMap.sub_apply, Module.End.mul_apply, hD _ x.2] at h
    simp only [Submodule.coe_add, Submodule.coe_smul, hE]
    linear_combination (norm := module) h
  have key := low_of (E 0 0) (E 0 1) (E 1 0) (π.op (.cpt eps)) H k hk ?_ ?_ hBC ?_ hH.definite (hadj 0 0) (hadj 0 1)
    (hadj 1 0) ?_ ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, h1, h2⟩ := key
    refine ⟨x.1, x.2, fun h => hx (Subtype.ext h), fun w => ?_, fun w => ?_, fun w => ?_⟩
    · rw [hv w]
      exact congrArg Subtype.val h1
    · rw [hv w, hD _ x.2, sub_neg_eq_add, ← two_smul ℂ]
      exact congrArg Subtype.val h2
    · rw [hv w, hD _ x.2, add_neg_cancel]
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 0 1 x.1
    simp at h
    simp only [Submodule.coe_add, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := hrel 0 0 1 0 x.1
    simp at h
    simp only [Submodule.coe_sub, hE]
    linear_combination (norm := module) h
  · intro x
    refine Subtype.ext ?_
    have h := (hcap x.1 x.2).2
    have h' := congrArg Subtype.val (hBC x)
    rw [hD _ x.2, map_neg, hD (TR.Eop v 0 0 x.1) (E 0 0 x).2, neg_neg] at h
    simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, hE] at h h' ⊢
    linear_combination (norm := module) (1 / 2 : ℂ) • h - (1 / 2 : ℂ) • h'
  · intro x h
    refine hH.definite x ?_
    rw [← hH.cpt eps x x, h]
    simp
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · intro x
    simp [hJ]
  · obtain ⟨φ, hφ, h0, n, h⟩ := wtVec π
    exact ⟨⟨φ, hφ⟩, fun e => h0 (congrArg Subtype.val e), n, Subtype.ext (h v)⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.MinNew
section
open CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd in
theorem UpperTheory.V.Br.minNew :
    UpperTheory.V.Br.MinNew := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k hN hk χ g
    by_cases hnew : ∀ (M' : ℕ), M' ∣ N → M' ≠ N →
        ∀ (g' : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1 M')) ↑k)
          (χ' : DirichletCharacter ℂ M'), HasChar k χ' ⇑g' →
          (∀ᶠ (p : ℕ) in Filter.cofinite, Nat.Prime p → IsEigAt k χ' (⇑g') p (coef (⇑g.f) p)) → g' = 0
    · refine ⟨⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g.f, χ, g.char, g.one,
        fun p hp _ => g.eig p hp, hnew⟩, hN, g, rfl, Filter.Eventually.of_forall fun _ _ => rfl⟩
    · push_neg at hnew
      obtain ⟨M', hdvd, hne, g', χ', hc, hev, hg0⟩ := hnew
      have hM0 : M' ≠ 0 := by
        rintro rfl
        exact NeZero.ne N (Nat.eq_zero_of_zero_dvd hdvd)
      haveI : NeZero M' := ⟨hM0⟩
      have hlt : M' < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd) hne
      obtain ⟨g'', hg''⟩ := UpperTheory.V.Br.eigEx M' k hk χ' g' hc hg0 (coef (⇑g.f))
      obtain ⟨f, hf, h, hhf, hha⟩ := ih M' hlt k hk χ' g''
      refine ⟨f, hf, h, hhf, ?_⟩
      filter_upwards [hha, hev] with p h1 h2 hp
      rw [h1 hp, hg'' p hp (h2 hp)]
      rfl
end

