module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RootsOfUnityShapes.PowIne
public import Mathlib.NumberTheory.Multiplicity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InducedRepresentationConstituentVanishing
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Pointwise

private theorem cyc_ine (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : ¬ A.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) :
    cycZ ℚ Ω l σ = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  show cyclotomicCharacter Ω l σ.toRingEquiv = 1
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ.toRingEquiv ζ hζ.pow_eq_one
  have hv : ¬ A.valuation ((l ^ n : ℕ) : Ω) < 1 := by
    rw [Nat.cast_pow, map_pow, not_lt]
    exact one_le_pow₀ (not_lt.1 hA)
  have h1 : Chr.cls ℚ Ω (l ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (l ^ n)).2.2.2.2 A hv hσ
  have h2 := Chr.cls_spec (l ^ n) σ ζ hζ.pow_eq_one
  rw [h1] at h2
  have h3 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (hspec.symm.trans h2)
  rw [ZMod.val_injective _ h3]
  simp

private theorem ine_iff {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F]
    (A : ValuationSubring Ω) (g : G F Ω) : g ∈ Ine (F := F) A ↔ resQ F g ∈ Ine (F := ℚ) A := Iff.rfl

private theorem mix_one {k : Type} [Field k] (h : (2 : k) ≠ 0) (γ : kˣ) : mix γ 1 1 = (1 : M4 k) := by
  have e : (2 : k)⁻¹ * (1 + 1) = 1 := by rw [one_add_one_eq_two, inv_mul_cancel₀ h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mix, e]

private theorem diag_one {Γ k : Type} [Group Γ] [Field k] {r : Γ →* GL (Fin 2) k} {H : Subgroup Γ} {x : Γ →* kˣ}
    (h : IsDiagOn r H ![1, x]) {s : Γ} (hs : s ∈ H) (hx : x s = 1) : r s = 1 := by
  obtain ⟨g, hg⟩ := h
  have h1 : g * r s * g⁻¹ = 1 := by
    apply Units.ext
    rw [hg s hs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx]
  simpa [mul_inv_eq_one] using h1

private theorem sqrt_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : (Qbar l)ˣ} (h : d ^ 2 = 1) (hc : Cong d 1) : d = 1 := by
  have h1 : (d : Qbar l) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  rcases sq_eq_one_iff.1 h1 with h2 | h2
  · exact Units.ext h2
  · exfalso
    have h3 : ‖(2 : Qbar l)‖ < 1 := by
      have h4 : ‖(d : Qbar l) - 1‖ < 1 := hc
      rw [h2, show (-1 - 1 : Qbar l) = -2 by ring, norm_neg] at h4
      exact h4
    have h5 : ‖((2 : ℕ) : ℚ_[l])‖ = 1 := by
      rw [Padic.norm_natCast_eq_one_iff]
      exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hl
    have h6 : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by rw [map_natCast, Nat.cast_ofNat]
    rw [h6, norm_algebraMap', h5] at h3
    exact lt_irrefl _ h3

theorem UpperTheory.induced_representation_constituent_vanishing :
    UpperTheory.V.Sd.S2.IndKill := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r α β R δ H g hg
  obtain ⟨A, hA, hgI, hrb⟩ := hg
  have hAl : ¬ A.valuation (l : Ω) < 1 := hA l (Finset.mem_insert_self _ _)
  have hsI : resQ T.F g ∈ Ine (F := ℚ) A := (ine_iff _ _ _).1 hgI
  have hψ : D.ψ (resQ T.F g) = 1 :=
    H.hyp.ok.kb A (fun p hp => by rw [Finset.mem_singleton.1 hp]; exact hAl) g hgI hrb
  have hk : resQ T.F g ∈ k₀.fixingSubgroup := (H.hyp.ps g).1 (H.hyp.two.unr A g hgI)
  have hδ2 := H.δ_sq g
  have hδ1 := H.δ_one g
  show (tw (R.comp (resQ T.F)) δ g).val = 1
  rw [tw_val, MonoidHom.comp_apply]
  generalize resQ T.F g = s at *
  have hz : cycZ ℚ Ω l s = 1 := cyc_ine Ω l A hAl hsI
  have hbar : cycBar ℚ Ω l s = 1 := by simp [cycBar, hz]
  have hchi : chiO ℚ Ω l c.O s = 1 := by simp [chiO, hz]
  have hom : D.om s = 1 := (H.chars.om s).2 (by rw [hbar]; simp [Cong])
  have hal : D.al s = D.ξ s := by simp [Raw.al, hchi, hom]
  have hξ : D.ξ s = 1 := by
    refine H.chars.xi s ?_
    have h1 : residue c.O (D.ξ s : c.O) = 1 := by
      have h2 := congrFun (congrFun hrb 2) 2
      rw [← hal]
      simpa [Raw.rbar, Raw.r0, mapRep, GradeZeroInterpolatingElement.diagRep, Raw.ps] using h2
    have h3 : (D.ξ s : c.O) - 1 ∈ maximalIdeal c.O := by
      rw [← residue_eq_zero_iff, map_sub, h1, map_one, sub_self]
    have h4 := (UpperTheory.V.Fr.sc_norm l c _).2.1 h3
    rw [Subalgebra.coe_sub, Subalgebra.coe_one] at h4
    unfold Cong
    rw [Units.val_one]
    exact h4
  have hth : D.th s = 1 := by simp [Raw.th, Raw.Psi, Chr.Psi, hal, hξ, hchi, hψ]
  have hup : up D.ξ s = 1 := by simp [up, hξ]
  have hδ : δ g = 1 := by
    refine sqrt_one H.hyp.good.l_odd ?_ hδ1
    simpa [hbar, hup, H.hyp.φ_in s hk, up, hth, hξ] using hδ2
  obtain ⟨h, rfl⟩ : s ∈ (resQ k₀).range := ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) fun x => hk ⟨x.1, x.2⟩, rfl⟩
  have hN : (resQ k₀).range.Normal := Subgroup.normal_of_index_eq_two H.mix.index
  set t₀ := resQ T.F T.g0 with ht₀
  obtain ⟨h', hh'⟩ : t₀⁻¹ * resQ k₀ h * t₀ ∈ (resQ k₀).range := hN.conj_mem' _ ⟨h, rfl⟩ t₀
  have r1 : r h = 1 := diag_one (H.dat.away A hAl) ((ine_iff _ _ _).2 hsI) hup
  obtain ⟨c1, c2, -⟩ := UpperTheory.V.Two.ineConj ℚ Ω t₀
  have hAA : t₀ • (t₀⁻¹ • A) = A := smul_inv_smul _ _
  have r2 : r h' = 1 := by
    refine diag_one (H.dat.away (t₀⁻¹ • A) fun h0 => hAl ?_) ((ine_iff _ _ _).2 ?_) ?_
    · rw [← hAA]; exact (c2 _ l).2 h0
    · rw [hh']; exact c1 _ _ (hAA.symm ▸ hsI)
    · rw [MonoidHom.comp_apply, hh', map_mul, map_mul, hup, mul_one, ← map_mul, inv_mul_cancel, map_one]
  rw [H.mix.on h h' hh', r1, r2, hδ, Units.val_one, Units.val_one, one_smul]
  exact mix_one H.mix.two _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaActsTriviallyOnRootsOfUnity
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem no_tors (l : ℕ) [hl : Fact l.Prime] (h2 : l ≠ 2) (u : ℤ_[l]) (hu : u ^ l = 1) : u = 1 := by
  by_contra h1
  have hm : PadicInt.toZMod (u - 1) = 0 := by
    have := congrArg PadicInt.toZMod hu
    rw [map_pow, ZMod.pow_card, map_one] at this
    rw [map_sub, this, map_one, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hm
  obtain ⟨b, hb⟩ := hm
  have hu' : u = 1 + l * b := by rw [← hb]; ring
  have hs : ∑ i ∈ Finset.range l, u ^ i = 0 := by
    have := mul_geom_sum u l
    rw [hu, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hd := odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hl.out.odd_of_ne_two h2)
  simp only [one_pow, mul_one, ← hu', hs, zero_sub, dvd_neg] at hd
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hd' : (l : ℤ_[l]) * l ∣ l * 1 := by rwa [mul_one, ← sq]
  exact PadicInt.irreducible_p.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hl0).1 hd'))

theorem UpperTheory.inertia_acts_trivially_on_roots_of_unity :
    UpperTheory.V.Sd.S3.MuIne := by
  intro F Ω _ _ _ _ _ l hl h2 A hA s ⟨h1, a, h3⟩
  refine ⟨Rq.powIne F Ω l A hA s h1 _ (pow_pos hl.out.pos a)
    (Subgroup.topologicalClosure_minimal _ (UpperTheory.V.B1.decComm F Ω l A hA) (isClosed_Ine A) h3), ?_⟩
  have h4 : s ^ l ^ a ∈ (cycZ F Ω l).ker := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_singleton.preimage (continuous_cycZ F Ω l)) h3
    rw [Subgroup.commutator_le]
    intro g _ h _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  rw [MonoidHom.mem_ker, map_pow] at h4
  have : ∀ (b : ℕ) (u : ℤ_[l]), u ^ l ^ b = 1 → u = 1 := by
    intro b
    induction b with
    | zero => simp
    | succ b ih => intro u hu; exact ih u (no_tors l h2 _ (by rw [← pow_mul, ← pow_succ, hu]))
  exact Units.ext (this a _ (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralityOfNormCoefficients
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem int_of_norm {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem coef_of_field {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O :=
  _root_.UpperTheory.Reformulated.B.CoefficientsOfField.coef_of_field K

private theorem mem_pow_iff {l : ℕ} [Fact l.Prime] (c : Coef l) : ∃ a : ℝ, 0 < a ∧ a < 1 ∧
    ∀ (n : ℕ) (x : c.O), x ∈ maximalIdeal c.O ^ n ↔ ‖(x : PadicAlgCl l)‖ ≤ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h1 : ‖(ϖ : PadicAlgCl l)‖ < 1 := (UpperTheory.V.Fr.sc_norm l c ϖ).2.1 hϖ.not_isUnit
  have h0 : 0 < ‖(ϖ : PadicAlgCl l)‖ := norm_pos_iff.2 fun h => hϖ.ne_zero (Subtype.ext h)
  refine ⟨_, h0, h1, fun n x => ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (UpperTheory.V.Fr.sc_norm l c y).1
  · intro hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact dvd_zero _
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
    have hu : ‖((u : c.O) : PadicAlgCl l)‖ = 1 :=
      le_antisymm (UpperTheory.V.Fr.sc_norm l c u).1 (not_lt.1 fun h => (UpperTheory.V.Fr.sc_norm l c u).2.2 h u.isUnit)
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, hu, one_mul] at hx
    exact (pow_dvd_pow ϖ ((pow_le_pow_iff_right_of_lt_one₀ h0 h1).1 hx)).mul_left _

theorem UpperTheory.integrality_of_norm_coefficients :
    UpperTheory.V.Sd.S3.CoefEx := by
  intro l _
  refine ⟨fun c E hE => ?_, fun c Γ _ f => ?_⟩
  · obtain ⟨c', hc'⟩ := coef_of_field E
    obtain ⟨c₁, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
    exact ⟨c₁, h1, fun y hy h => h2 (hc' y hy h)⟩
  obtain ⟨a, h0, h1, ha⟩ := mem_pow_iff c
  constructor
  · intro hf
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε h1
    filter_upwards [(hf n).eventually_eq g₀] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub]
    exact lt_of_le_of_lt ((ha n _).1 (Ideal.Quotient.eq.1 hg)) hn
  · intro hf n
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    filter_upwards [Metric.tendsto_nhds.1 (hf.tendsto g₀) (a ^ n) (pow_pos h0 n)] with g hg
    rw [dist_eq_norm, ← Subalgebra.coe_sub] at hg
    exact Ideal.Quotient.eq.2 ((ha n _).2 hg.le)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixFlagExists
section
open UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2
open scoped Matrix

section
variable {k : Type} [Field k]

private def nn (p q r s t : k) : M4 k := !![1, 0, 0, 0; p, 1, 0, 0; q, s, 1, 0; r, t, -p, 1]

private theorem adj_nn (p q r s t : k) :
    adj (nn p q r s t) = !![1, 0, 0, 0; -p, 1, 0, 0; -t, -s, 1, 0; -r, -q, p, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, nn, sgn, Fin.rev]

private theorem low_nn (p q r s t : k) (h : t + p * s - q = 0) : IsLow (nn p q r s t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold IsGSp
    rw [adj_nn]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nn, Matrix.mul_apply, Fin.sum_univ_four] <;>
      first | ring1 | linear_combination h | linear_combination -h
  · intro i
    fin_cases i <;> simp [nn]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [nn]

private theorem par1 (u a a' : k) (A : Matrix (Fin 2) (Fin 2) k) (ha : a ≠ 0)
    (h : A *ᵥ ![u, 1] = a • ![u, 1]) (hd : A.det = a * a') :
    ∃ p, A = !![a' + u * p, (a - a' - u * p) * u; p, a - p * u] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : A 0 0 = a' + u * A 1 0 := by
    apply mul_left_cancel₀ ha
    linear_combination hd - A 0 0 * h1 + A 1 0 * h0
  refine ⟨A 1 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · exact h2
  · linear_combination h0 - u * h2
  · linear_combination h1

private theorem par2 (w b b' : k) (B : Matrix (Fin 2) (Fin 2) k) (hb : b ≠ 0)
    (h : B *ᵥ ![1, w] = b • ![1, w]) (hd : B.det = b * b') :
    ∃ q, B = !![b - q * w, q; (b - b' - q * w) * w, b' + q * w] := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hd
  have h2 : B 1 1 = b' + B 0 1 * w := by
    apply mul_left_cancel₀ hb
    linear_combination hd - B 1 1 * h0 + B 0 1 * h1
  refine ⟨B 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination h0
  · linear_combination h1 - w * h2
  · exact h2

private theorem case1 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : 1 + γ * u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![u, 1] = a • ![u, 1]) (hB : B *ᵥ ![1, w] = b • ![1, w]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (γ * u) (-1) (γ * u) (-(2 * w) / (1 + γ * u * w)) (-(1 - γ * u * w) / (1 + γ * u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![a, b, b', a'] i := by
  obtain ⟨p, rfl⟩ := par1 u a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par2 w b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

private theorem case2 (h2 : (2 : k) ≠ 0) (γ : kˣ) (u w : k) (hz : (γ : k) + u * w ≠ 0)
    (A B : Matrix (Fin 2) (Fin 2) k) (a a' b b' : k) (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : A *ᵥ ![1, w] = a • ![1, w]) (hB : B *ᵥ ![u, 1] = b • ![u, 1]) (dA : A.det = a * a') (dB : B.det = b * b')
    (n : M4 k) (hn : n = nn (-u) 1 u (-(2 * w) / (γ + u * w)) ((γ - u * w) / (γ + u * w))) :
    IsUp (adj n * mix γ A B * n) ∧ ∀ i, (adj n * mix γ A B * n) i i = ![b, a, a', b'] i := by
  obtain ⟨p, rfl⟩ := par2 w a a' A ha hA dA
  obtain ⟨q, rfl⟩ := par1 u b b' B hb hB dB
  have hγ : (γ : k) ≠ 0 := γ.ne_zero
  subst hn
  rw [adj_nn]
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)
  · intro i
    fin_cases i <;> (simp [nn, mix, Matrix.mul_apply, Fin.sum_univ_four]; field_simp; ring)

end

private theorem norm_add_one {k : Type} [NormedField k] [IsUltrametricDist k] (x y : k) (hx : ‖x‖ = 1) (hy : ‖y‖ < 1) :
    ‖x + y‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hx]; exact hy.ne'), hx]
  exact max_eq_left hy.le

private theorem norm_two_mul {k : Type} [NormedField k] [IsUltrametricDist k] (w : k) (hw : ‖w‖ < 1) :
    ‖2 * w‖ < 1 := by
  rw [two_mul]
  exact (IsUltrametricDist.norm_add_le_max w w).trans_lt (by simpa using hw)

private theorem lowQ_nn {l : ℕ} [Fact l.Prime] (p q r s t : Formalism.ConjugateSelfDual.Qbar l) (h : t + p * s - q = 0)
    (hp : ‖p‖ ≤ 1) (hq : ‖q‖ = 1) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ < 1) (ht : ‖t‖ ≤ 1) : LowQ (nn p q r s t) := by
  refine ⟨low_nn p q r s t h, ?_, by simpa [nn] using hs, by simpa [nn] using hq⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp [nn, hp, hq.le, hr, hs.le, ht]

theorem UpperTheory.mix_flag_exists :
    UpperTheory.V.Sd.S2.MixFlag := by
  intro l _ _ γ u w hγ hu hw
  have huw : ‖u * w‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu).trans_lt hw
  have hz : ‖γ * u * w‖ < 1 := by rw [mul_assoc, norm_mul, hγ, one_mul]; exact huw
  have h1 := norm_add_one 1 _ norm_one hz
  have h1' : ‖1 - γ * u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one 1 _ norm_one (by rwa [norm_neg])
  have h3 := norm_add_one _ _ hγ huw
  have h3' : ‖γ - u * w‖ = 1 := by
    rw [sub_eq_add_neg]; exact norm_add_one _ _ hγ (by rwa [norm_neg])
  have n1 : 1 + γ * u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  have n3 : γ + u * w ≠ 0 := by
    intro h; rw [h, norm_zero] at h3; exact zero_ne_one h3
  have h2 := norm_two_mul w hw
  have hgu : ‖γ * u‖ ≤ 1 := by rw [norm_mul, hγ, one_mul]; exact hu
  refine ⟨⟨_, lowQ_nn (γ.val * u) (-1) (γ.val * u) (-(2 * w) / (1 + γ.val * u * w)) (-(1 - γ.val * u * w) / (1 + γ.val * u * w)) ?_ hgu
      (by simp) hgu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case1 two_ne_zero γ u w n1 A B a a' b b' ha hb hA hB dA dB _ rfl⟩,
    ⟨_, lowQ_nn (-u) 1 u (-(2 * w) / (γ.val + u * w)) ((γ.val - u * w) / (γ.val + u * w)) ?_ (by rwa [norm_neg])
      (by simp) hu ?_ ?_, fun A B a a' b b' ha hb hA hB dA dB => case2 two_ne_zero γ u w n3 A B a a' b b' ha hb hA hB dA dB _ rfl⟩⟩
  · field_simp; ring
  · rw [norm_div, norm_neg, h1, div_one]; exact h2
  · rw [norm_div, norm_neg, h1, h1', div_one]
  · field_simp; ring
  · rw [norm_div, norm_neg, h3, div_one]; exact h2
  · rw [norm_div, h3, h3', div_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MixMatrixResidueProperties
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd.S2 GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem um_add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

private theorem um_add_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

private theorem um_sub_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a - b‖ < 1 := by
  rw [sub_eq_add_neg]; exact um_add_lt ha (by rwa [norm_neg])

private theorem um_sub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]; exact um_add_le ha (by rwa [norm_neg])

private theorem le_of_cong {a x : K} (h : ‖a - x‖ < 1) (hx : ‖x‖ = 1) : ‖a‖ ≤ 1 := by
  have := um_add_le h.le hx.le
  rwa [sub_add_cancel] at this

private theorem diff_lt {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) : ‖a - b‖ < 1 := by
  have := um_sub_lt ha hb
  rwa [sub_sub_sub_cancel_right] at this

private theorem half_lt (h2 : ‖(2 : K)‖ = 1) {a b x : K} (ha : ‖a - x‖ < 1) (hb : ‖b - x‖ < 1) :
    ‖(2 : K)⁻¹ * (a + b) - x‖ < 1 := by
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have e : (2 : K)⁻¹ * (a + b) - x = (2 : K)⁻¹ * ((a - x) + (b - x)) := by
    field_simp; ring
  rw [e, norm_mul, norm_inv, h2, inv_one, one_mul]
  exact um_add_lt ha hb

private theorem key (h2 : ‖(2 : K)‖ = 1) (γ : Kˣ) (x : K) (A B : Matrix (Fin 2) (Fin 2) K) (hγ : ‖(γ : K)‖ = 1) (hx : ‖x‖ = 1)
    (a00 : ‖A 0 0 - 1‖ < 1) (a11 : ‖A 1 1 - x‖ < 1) (a10 : ‖A 1 0‖ < 1) (a01 : ‖A 0 1‖ ≤ 1)
    (b00 : ‖B 0 0 - 1‖ < 1) (b11 : ‖B 1 1 - x‖ < 1) (b10 : ‖B 1 0‖ < 1) (b01 : ‖B 0 1‖ ≤ 1) :
    (∀ i j, ‖mix γ A B i j‖ ≤ 1) ∧ (∀ i, ‖mix γ A B i i - ![x, 1, x, 1] i‖ < 1) ∧
    (∀ i j, i ≠ j → wt i j ∉ vV → ‖mix γ A B i j‖ < 1) ∧
    (‖A 0 1‖ = 1 → ‖mix γ A B 1 0‖ = 1 ∨ (‖mix γ A B 1 2‖ = 1 ∧ ‖mix γ A B 3 0‖ = 1)) := by
  have hh : ∀ y : K, ‖(2 : K)⁻¹ * y‖ = ‖y‖ := fun y => by rw [norm_mul, norm_inv, h2, inv_one, one_mul]
  have h0 : (2 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; exact zero_ne_one h2
  have p : ‖A 1 0 / γ‖ < 1 := by rwa [norm_div, hγ, div_one]
  have p' : ‖-(A 1 0 / γ)‖ < 1 := by rwa [norm_neg]
  have qe : ‖γ * A 0 1‖ = ‖A 0 1‖ := by rw [norm_mul, hγ, one_mul]
  have q : ‖γ * A 0 1‖ ≤ 1 := qe ▸ a01
  have q' : ‖-(γ * A 0 1)‖ ≤ 1 := by rwa [norm_neg]
  have c00 := le_of_cong a00 norm_one
  have c11 := le_of_cong a11 hx
  have d00 := le_of_cong b00 norm_one
  have d11 := le_of_cong b11 hx
  have e01 : ‖mix γ A B 0 1‖ < 1 := (hh _).trans_lt (um_sub_lt p b10)
  have e02 : ‖mix γ A B 0 2‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e03 : ‖mix γ A B 0 3‖ < 1 := (hh _).trans_lt (um_add_lt p b10)
  have e13 : ‖mix γ A B 1 3‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e20 : ‖mix γ A B 2 0‖ < 1 := (hh _).trans_lt (diff_lt b11 a11)
  have e21 : ‖mix γ A B 2 1‖ < 1 := (hh _).trans_lt (um_sub_lt p' b10)
  have e23 : ‖mix γ A B 2 3‖ < 1 := (hh _).trans_lt (um_add_lt p' b10)
  have e31 : ‖mix γ A B 3 1‖ < 1 := (hh _).trans_lt (diff_lt a00 b00)
  have e00 : ‖mix γ A B 0 0‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e11 : ‖mix γ A B 1 1‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e22 : ‖mix γ A B 2 2‖ ≤ 1 := (hh _).trans_le (um_add_le c11 d11)
  have e33 : ‖mix γ A B 3 3‖ ≤ 1 := (hh _).trans_le (um_add_le c00 d00)
  have e10 : ‖mix γ A B 1 0‖ ≤ 1 := (hh _).trans_le (um_sub_le q b01)
  have e12 : ‖mix γ A B 1 2‖ ≤ 1 := (hh _).trans_le (um_sub_le q' b01)
  have e30 : ‖mix γ A B 3 0‖ ≤ 1 := (hh _).trans_le (um_add_le q b01)
  have e32 : ‖mix γ A B 3 2‖ ≤ 1 := (hh _).trans_le (um_add_le q' b01)
  refine ⟨fun i j => ?_, fun i => ?_, fun i j hij hw => ?_, fun h => ?_⟩
  · fin_cases i <;> fin_cases j
    exacts [e00, e01.le, e02.le, e03.le, e10, e11, e12, e13.le, e20.le, e21.le, e22, e23.le, e30, e31.le, e32, e33]
  · fin_cases i
    exacts [half_lt h2 a11 b11, half_lt h2 a00 b00, half_lt h2 a11 b11, half_lt h2 a00 b00]
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact (hw (by decide)).elim
      | assumption
  · have m10 : mix γ A B 1 0 = (2 : K)⁻¹ * (γ * A 0 1 - B 0 1) := rfl
    have m12 : mix γ A B 1 2 = (2 : K)⁻¹ * (-(γ * A 0 1) - B 0 1) := rfl
    have m30 : mix γ A B 3 0 = (2 : K)⁻¹ * (γ * A 0 1 + B 0 1) := rfl
    have s : mix γ A B 1 0 + mix γ A B 3 0 = γ * A 0 1 := by
      rw [m10, m30]; field_simp; ring
    have n : ‖mix γ A B 1 2‖ = ‖mix γ A B 3 0‖ := by
      rw [← norm_neg, m12, m30]; congr 1; ring
    rcases e10.eq_or_lt with h1 | h1
    · exact Or.inl h1
    rcases e30.eq_or_lt with h3 | h3
    · exact Or.inr ⟨n.trans h3, h3⟩
    have := um_add_lt h1 h3
    rw [s, qe, h] at this
    exact absurd this (lt_irrefl _)

end

theorem UpperTheory.mixMatrix_residue_properties :
    UpperTheory.V.Sd.S2.MixRes := by
  intro l hl l2 γ x A B hγ hx hA hB
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have e : (2 : Qbar l) = algebraMap ℚ_[l] (Qbar l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; rfl
    rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes hl.out Nat.prime_two).2 l2
  exact key h2 γ x A B hγ hx hA.1 hA.2.1 hA.2.2.1 hA.2.2.2 hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
end

