module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0058

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Boxfin
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem abs_reAt {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |reAt v x| = v x := by
  have hr := IsTotallyReal.isReal v
  rw [← InfinitePlace.norm_embedding_eq, ← InfinitePlace.embedding_of_isReal_apply hr, Complex.norm_real, reAt,
    ← InfinitePlace.embedding_of_isReal_apply hr, Complex.ofReal_re, Real.norm_eq_abs]

private theorem val_le {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥)
    {d : 𝓞 F} (hd : d ∈ I) : w.valuation F (d : F) ≤ WithZero.exp (-(ordI w I : ℤ)) := by
  have h1 : w.asIdeal ^ ordI w I ∣ I := by
    rw [← Associates.mk_dvd_mk, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) w.associates_irreducible).2 le_rfl
  have h2 : d ∈ w.asIdeal ^ ordI w I := Ideal.le_of_dvd h1 hd
  rw [show (d : F) = algebraMap (𝓞 F) F d from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_le_pow_iff_mem w d _).2 h2

private theorem val_pLoc {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (pLoc F w (algebraMap F (Af F) x)) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

theorem UpperTheory.V.Sd.Hm.boxfin :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (y : (Af F)ˣ) (ξ : F),
        {η : F | (∀ v, 0 < reAt v η) ∧ (∀ v, reAt v η < reAt v ξ) ∧ ∃ 𝔪, GenD (algebraMap F (Af F) η * (y : Af F)) 𝔪}.Finite := by
  intro F _ _ _ y ξ
  by_cases hne : ∃ η₀ : F, ∃ 𝔪, GenD (algebraMap F (Af F) η₀ * (y : Af F)) 𝔪
  swap
  · apply Set.Finite.subset Set.finite_empty
    intro η h
    exact (hne ⟨η, h.2.2⟩).elim
  obtain ⟨η₀, 𝔪₀, h₀⟩ := hne
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₀.1
  obtain ⟨w₀⟩ : Nonempty (HeightOneSpectrum (𝓞 F)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
    exact ⟨⟨M, hM.isPrime, RingOfIntegers.not_isField F |> Ring.ne_bot_of_isMaximal_of_not_isField hM⟩⟩
  have hη₀ : η₀ ≠ 0 := by
    rintro rfl
    have := h₀.2 w₀
    rw [map_zero, zero_mul, map_zero, map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hc : (d : F) / η₀ ≠ 0 := div_ne_zero (by exact_mod_cast hd0) hη₀
  refine Set.Finite.of_finite_image (f := fun η => (d : F) / η₀ * η) ?_ (mul_right_injective₀ hc).injOn
  refine (Embeddings.finite_of_norm_le F ℂ (∑ v : InfinitePlace F, v ((d : F) / η₀ * ξ))).subset ?_
  rintro _ ⟨η, ⟨hpos, hlt, 𝔪, h⟩, rfl⟩
  refine ⟨?_, fun φ => ?_⟩
  · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F ((d : F) / η₀ * η) fun w => by
      have a := h.2 w
      have a₀ := h₀.2 w
      rw [map_mul, map_mul, val_pLoc] at a a₀
      have hy : Valued.v (pLoc F w (y : Af F)) ≠ 0 := (right_ne_zero_of_mul (a ▸ WithZero.exp_ne_zero))
      rw [← eq_div_iff hy] at a a₀
      have e : w.valuation F η / w.valuation F η₀ = WithZero.exp ((ordI w 𝔪₀ : ℤ) - (ordI w 𝔪 : ℤ)) := by
        rw [a, a₀, div_div_div_cancel_right₀ hy, ← WithZero.exp_sub]
        congr 1; ring
      rw [div_mul_eq_mul_div, mul_div_assoc, map_mul, map_div₀, e]
      calc _ ≤ WithZero.exp (-(ordI w 𝔪₀ : ℤ)) * WithZero.exp ((ordI w 𝔪₀ : ℤ) - (ordI w 𝔪 : ℤ)) :=
            mul_le_mul_left (val_le w h₀.1 hd) _
        _ ≤ 1 := by
            rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
            omega
    show IsIntegral ℤ ((d : F) / η₀ * η)
    rw [← hr]
    exact r.2
  · show ‖φ ((d : F) / η₀ * η)‖ ≤ _
    rw [← InfinitePlace.apply]
    refine le_trans ?_ (Finset.single_le_sum (f := fun v : InfinitePlace F => v ((d : F) / η₀ * ξ))
      (fun v _ => apply_nonneg v _) (Finset.mem_univ (InfinitePlace.mk φ)))
    simp only [map_mul]
    refine mul_le_mul_of_nonneg_left ?_ (apply_nonneg _ _)
    rw [← abs_reAt, ← abs_reAt, abs_of_pos (hpos _)]
    exact (hlt _).le.trans (le_abs_self _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Fixunit
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem map_aff {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (aff y 0) = aff (Units.map (f : R →* S) y) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_mem {R : Type} [CommRing R] (y : Rˣ) : aff y 0 ∈ mirab R := by
  change Matrix.vecMul _ _ = _
  ext i
  fin_cases i <;> simp [aff, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

open UpperTheory.V.Af.GlobalFixedVectors Matrix in
theorem UpperTheory.V.Sd.Hm.fixunit :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (φ : TR.Sm F 2), IsOpen {k | TR.finRep F 2 k φ = φ} →
        ∀ c : Pl F → ℕ, (∀ w, φ ∈ Hi.fixd (locSm F w) (K1 w (c w))) → ∀ u : (Af F)ˣ, (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) →
        ∀ g, φ.1 (g * finGL F 2 (aff u 0)) = φ.1 g := by
  classical
  intro F _ _ _ φ hop c hc u hu g
  have key : ∀ S : Finset (Pl F),
      (∀ k ∈ KAway 2 1 S, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) →
      (∀ k ∈ KAway 2 1 ∅, (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) → TR.finRep F 2 k φ = φ) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact id
    | insert w S hw ih =>
      intro h
      refine ih fun k hk hl => ?_
      have h1 := loc_mem w (mem_KAway.1 hk).1
      have h2 : k * (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ ∈ KAway 2 1 (insert w S) := by
        refine mem_KAway.2 ⟨mul_mem (mem_KAway.1 hk).1 (inv_mem h1), fun u hu => ?_⟩
        by_cases huw : u = w
        · subst huw; simp [pLoc_locGL]
        · simp [pLoc_locGL_of_ne huw, (mem_KAway.1 hk).2 u ((Finset.mem_insert.1 hu).resolve_left huw)]
      have h3 : TR.finRep F 2 (locGL F 2 w (GeneralLinearGroup.map (pLoc F w) k)) φ = φ := hc w _ (hl w)
      have h4 := h _ h2 fun v => by
        by_cases hv : v = w
        · subst hv; simp [pLoc_locGL]
        · simpa [pLoc_locGL_of_ne hv] using hl v
      rwa [← h3, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, h3] at h4
  obtain ⟨S, hS⟩ := exists_KAway_subset (M := 1) (hop.mem_nhds (by simp))
  have hi : ∀ w, Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) = 1 := fun w => by
    have : Valued.v (pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F)) * Valued.v (pLoc F w (u : Af F)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rwa [hu, mul_one] at this
  have m1 : ∀ w, pLoc F w (u : Af F) ∈ w.adicCompletionIntegers F := fun w => (hu w).le
  have m2 : ∀ w, pLoc F w ((u⁻¹ : (Af F)ˣ) : Af F) ∈ w.adicCompletionIntegers F := fun w => (hi w).le
  let u0 : (Ohat F)ˣ := ⟨⟨u, mem_Ohat.2 m1⟩, ⟨((u⁻¹ : (Af F)ˣ) : Af F), mem_Ohat.2 m2⟩, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  have e := key S (fun k hk _ => hS hk) (aff u 0) (mem_KAway.2 ⟨⟨aff u0 0, ?_, ?_⟩, by simp⟩) fun w => ?_
  · exact congrFun (congrArg Subtype.val e) g
  · haveI : Subsingleton (Ohat F ⧸ Ideal.span {((1 : ℕ) : ↥(Ohat F))}) :=
      Ideal.Quotient.subsingleton_iff.2 (by simp)
    ext i j
    exact Subsingleton.elim _ _
  · rw [map_aff]; rfl
  · let u1 : (w.adicCompletionIntegers F)ˣ := ⟨⟨_, m1 w⟩, ⟨_, m2 w⟩,
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.mul_inv, map_one]),
      Subtype.ext (by change pLoc F w _ * pLoc F w _ = 1; rw [← map_mul, Units.inv_mul, map_one])⟩
    refine ⟨aff u1 0, ?_, ?_⟩
    · change GeneralLinearGroup.map _ (aff u1 0) ∈ mirab _
      rw [map_aff]
      exact aff_mem _
    · rw [map_aff, map_aff]
      congr 1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Mulaut
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem stab_open {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) (h : {k | ρ k v = v} ∈ nhds (1 : G)) : IsOpen {k | ρ k v = v} :=
  _root_.UpperTheory.Reformulated.B.StabilizerIsOpen.stab_open ρ v h

private theorem fin_mul {X ι : Type*} (S : Submodule ℂ (X → ℂ)) (f g h : ι → S) (e : ∀ i, (h i).1 = (f i).1 * (g i).1)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)))
    (hg : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range h)) := by
  have h1 : ((Submodule.span ℂ (Set.range f)).map S.subtype).FG := (Module.Finite.iff_fg.1 hf).map _
  have h2 : ((Submodule.span ℂ (Set.range g)).map S.subtype).FG := (Module.Finite.iff_fg.1 hg).map _
  have h3 := Module.Finite.iff_fg.2 (h1.mul h2)
  have h4 : FiniteDimensional ℂ ((Submodule.span ℂ (Set.range h)).map S.subtype) := by
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range f)).map S.subtype *
      (Submodule.span ℂ (Set.range g)).map S.subtype) (Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Submodule.subtype_apply, e]
    exact Submodule.mul_mem_mul ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩ ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  exact Module.Finite.iff_fg.2 (Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype (Module.Finite.iff_fg.1 h4))

theorem UpperTheory.V.Sd.Hm.mulaut :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 →
        TR.IsAutForm φ → TR.IsAutForm ψ →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F a) => z χ) '' TR.Zalg F a)) → TR.IsAutForm χ := by
  intro F _ _ _ a φ ψ χ e hφ hψ hz
  have hrt : ∀ g, (TR.rt F a g χ).1 = (TR.rt F a g φ).1 * (TR.rt F a g ψ).1 := fun g => by
    funext x
    simp only [TR.rt_apply, Pi.mul_apply, e]
  refine ⟨fun γ g => ?_, ?_, ?_, hz, fun g => ?_⟩
  · rw [e, Pi.mul_apply, Pi.mul_apply, hφ.left, hψ.left]
  · refine stab_open _ _ (Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨by simp, by simp⟩) fun k hk => ?_)
    have h1 : TR.rt F a (finGL F a k) φ = φ := hk.1
    have h2 : TR.rt F a (finGL F a k) ψ = ψ := hk.2
    change TR.rt F a (finGL F a k) χ = χ
    exact Subtype.ext (by rw [hrt, h1, h2, e])
  · exact fin_mul _ _ _ _ (fun k => hrt _) hφ.kfin hψ.kfin
  · obtain ⟨C, N, h1⟩ := hφ.growth g
    obtain ⟨C', N', h2⟩ := hψ.growth g
    refine ⟨C * C', N + N', fun y => ?_⟩
    rw [e, Pi.mul_apply, norm_mul]
    refine (mul_le_mul (h1 y) (h2 y) (norm_nonneg _) ((norm_nonneg _).trans (h1 y))).trans_eq ?_
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Mulsm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

theorem UpperTheory.V.Sd.Hm.mulsm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ ψ : TR.Sm F a),
        φ.1 * ψ.1 ∈ TR.Sm F a ∧ ∀ (χ : TR.Sm F a), χ.1 = φ.1 * ψ.1 → ∀ X : TR.Lie F a,
          (TR.lie F a X χ).1 = (TR.lie F a X φ).1 * ψ.1 + φ.1 * (TR.lie F a X ψ).1 := by
  intro F _ _ _ a φ ψ
  have e : ∀ g, TR.chart (φ.1 * ψ.1) g = TR.chart φ.1 g * TR.chart ψ.1 g := by
    intro g
    funext x
    by_cases h : IsUnit (Matrix.of x) <;> simp [TR.chart, h]
  have v : ∀ (f : GA F a → ℂ) g, TR.chart f g (TR.oneL F a) = f g := by
    intro f g
    have h := TR.chart_val f g 1
    rw [map_one, mul_one] at h
    exact h
  refine ⟨fun g => ?_, fun χ hχ X => ?_⟩
  · rw [e]
    exact (φ.2 g).mul (ψ.2 g)
  · funext g
    change TR.lieD X χ.1 g = TR.lieD X φ.1 g * ψ.1 g + φ.1 g * TR.lieD X ψ.1 g
    unfold TR.lieD
    rw [hχ, e, fderiv_mul (TR.differentiableAt_chart φ.2 g) (TR.differentiableAt_chart ψ.2 g), v, v]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Trzero
section
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.TR Matrix

private theorem infGL_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (u : (Rinf F)ˣ) :
    infGL F 2 (GeneralLinearGroup.scalar (Fin 2) u) = GeneralLinearGroup.scalar (Fin 2) (infId F u) := by
  have h : ∀ x, pInf F (sInf F x) = x := fun x => (infEq F).symm_apply_apply x
  have h1 : pInf F (infId F u : Ideles F) = u := by
    change pInf F (1 - sInf F 1 + sInf F _) = _
    simp [h]
  have h2 : pFin F (infId F u : Ideles F) = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h1]
  · rw [TR.pFin_infGL]
    ext i j
    by_cases e : i = j <;> simp [Matrix.diagonal_apply, e, h2]

private theorem fin_expU {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    (z : Rinf F) : ω.1 (infId F (expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : expU z = expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

private theorem lie_scalar {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {ω : HChar F} (h : IsOfFinOrder ω)
    {φ : Sm F 2} (hφ : ∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) (z : Rinf F) : lie F 2 (toL (Matrix.scalar (Fin 2) z)) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := hasDerivAt_curve φ g (fun t => GeneralLinearGroup.scalar (Fin 2) (expU (t • z)))
    (toL (Matrix.scalar (Fin 2) z)) (by simp [TR.expU_zero]) (by
      refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
      by_cases e : i = j
      · subst e
        have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
        simpa using this
      · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h2 : (fun t : ℝ => φ.1 (g * infGL F 2 (GeneralLinearGroup.scalar (Fin 2) (expU (t • z))))) = fun _ => φ.1 g := by
    funext t
    rw [infGL_scalar, ← GeneralLinearGroup.scalar_commute, hφ, fin_expU h]
    simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const _ _)

end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

theorem UpperTheory.V.Sd.Hm.trzero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F), IsOfFinOrder ω → ∀ φ : TR.Sm F 2,
        (∀ (z : Ideles F) (g : GA F 2), φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g) →
        ∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0 := by
  intro F _ _ _ ω hω φ hφ v
  classical
  rw [← lie_scalar hω hφ (Pi.single v 1), TR.Eop, TR.Eop, ← LinearMap.add_apply, ← map_add (f := _)]
  congr 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ScalarStabilizers.Zfinof
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

private theorem qdet2 {A : Type} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    Formalism.REAL.qdet E u = (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, h, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem casimir {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : Formalism.REAL.GlRel E) (k : ℂ) (φ : V) (h0 : E 0 0 φ + E 1 1 φ = 0)
    (h1 : E 0 1 φ - E 1 0 φ = (Complex.I * k) • φ) (h2 : E 0 0 φ - E 1 1 φ = Complex.I • (E 0 1 φ + E 1 0 φ)) (u : ℂ) :
    Formalism.REAL.qdet E (u + 1 / 2) φ = ((u + (k - 1) / 2) * (u - (k - 1) / 2)) • φ := by
  have hI := Complex.I_mul_I
  have hc : E 1 0 φ = E 0 1 φ - (Complex.I * k) • φ := by rw [← h1]; abel
  have ha : E 0 0 φ = Complex.I • E 0 1 φ + (k / 2) • φ := by
    rw [hc] at h2
    linear_combination (norm := skip) (1 / 2 : ℂ) • h0 + (1 / 2 : ℂ) • h2
    match_scalars <;> first | ring1 | linear_combination (k / 2) * hI | linear_combination (-k / 2) * hI
  have hd : E 1 1 φ = -E 0 0 φ := eq_neg_of_add_eq_zero_right h0
  have r1 : E 0 0 (E 0 1 φ) = E 0 1 (E 0 0 φ) + E 0 1 φ := by
    have := LinearMap.congr_fun (hE 0 0 0 1) φ
    simp at this
    exact sub_eq_iff_eq_add'.1 this
  have r2 : E 1 0 (E 0 1 φ) = E 0 1 (E 1 0 φ) + (E 1 1 φ - E 0 0 φ) := by
    have := LinearMap.congr_fun (hE 1 0 0 1) φ
    simp at this
    rw [← this]; abel
  have r3 : E 0 0 (E 0 0 φ) = Complex.I • E 0 0 (E 0 1 φ) + (k / 2) • E 0 0 φ := by
    conv_lhs => rw [ha]
    simp
  rw [qdet2]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_smul, hd, map_neg, r2, r3, r1]
  simp only [hc, ha, map_add (f := _), map_smul, map_sub]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

theorem UpperTheory.V.Sd.Hm.zfinof :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (φ : TR.Sm F 2),
        (∀ v, TR.Eop v 0 0 φ + TR.Eop v 1 1 φ = 0) → (∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ) →
        (∀ v, TR.Eop v 0 0 φ - TR.Eop v 1 1 φ = Complex.I • (TR.Eop v 0 1 φ + TR.Eop v 1 0 φ)) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (TR.Sm F 2) => z φ) '' TR.Zalg F 2)) := by
  intro F _ _ _ k φ h0 h1 h2
  have key : ∀ z ∈ TR.Zalg F 2, ∃ c : ℂ, z φ = c • φ := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨v, u, rfl⟩ := hx
      refine ⟨(u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2), ?_⟩
      rw [← casimir _ (TR.glRel_Eop v) k φ (h0 v) (h1 v) (h2 v) u, TR.cap]
      norm_num
    | algebraMap r => exact ⟨r, Module.algebraMap_end_apply ..⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [LinearMap.add_apply, ha, hb, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨b * a, by rw [Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨c, hc⟩ := key z hz
  exact Submodule.mem_span_singleton.2 ⟨c, hc.symm⟩
end

