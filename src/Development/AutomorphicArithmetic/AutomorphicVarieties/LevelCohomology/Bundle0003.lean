module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HQuad
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.ML UpperTheory.V.X

theorem UpperTheory.V.X.hQuad :
    ∀ (K : Type) [Field K] [NumberField K] (l : ℕ), l.Prime → 5 ≤ l → Module.finrank ℚ K = 2 → discr K = l → classNumber K < l := by
  intro K _ _ l hl h5 hn hd
  have h := GlobalTheory.classNumber_le_sqrt_discr_mul_pow_pred K
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have habs : |((discr K : ℤ) : ℝ)| = (l : ℝ) := by
    rw [hd]
    push_cast
    exact abs_of_pos hl0
  rw [hn, habs, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h
  have hx0 : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr hl0
  have h5r : (5 : ℝ) ≤ l := by exact_mod_cast h5
  have hx1 : Real.sqrt (l : ℝ) ≠ 1 := by
    intro h1
    have hs := Real.sq_sqrt hl0.le
    rw [h1] at hs
    linarith
  have hlog := Real.log_lt_sub_one_of_pos hx0 hx1
  have hsq : Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) = l := Real.mul_self_sqrt hl0.le
  have hlt : (classNumber K : ℝ) < l := by
    calc (classNumber K : ℝ) ≤ Real.sqrt (l : ℝ) * (1 + Real.log (Real.sqrt (l : ℝ))) := h
      _ < Real.sqrt (l : ℝ) * Real.sqrt (l : ℝ) := by
        apply mul_lt_mul_of_pos_left _ hx0
        linarith
      _ = l := hsq
  exact_mod_cast hlt
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLevFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem finite_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (ResidueField O)] (b : O) (hb : b ≠ 0) : Finite (O ⧸ Ideal.span {b}) := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hb)
  haveI : IsArtinianRing (O ⧸ Ideal.span {b}) :=
    isArtinian_of_tower O (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  exact IsLocalRing.finite_quotient_iff.mpr
    (IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _)

theorem UpperTheory.V.X.So.levFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (a : O), a ≠ 0 → ∀ (M : Type) [AddCommGroup M] [Module O M], Nonempty (M ≃ₗ[O] (O ⧸ Ideal.span {a})) → Finite M ∧ (∃ r : ℕ, 0 < r ∧ ∀ m : M, (l ^ r) • m = 0) ∧ ∀ d : O, d ≠ 0 → Nat.card {m : M // d • m = 0} ≤ Nat.card (O ⧸ Ideal.span {d}) := by
  intro l _ O _ _ _ _ _ a ha M _ _ hne
  obtain ⟨e⟩ := hne
  haveI : CharZero O := charZero_of_injective_algebraMap (UpperTheory.V.Base.dvrFacts l O).1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l O
  haveI := hfin
  haveI hQa : Finite (O ⧸ Ideal.span {a}) := finite_quot a ha
  haveI : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have hkill : ∀ c : O, c ∈ Ideal.span {a} → ∀ z : O ⧸ Ideal.span {a}, c • z = 0 := by
    intro c hc z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ hc
  have hgen : ∀ m : M, ∃ y : O, y • e.symm (Ideal.Quotient.mk _ 1) = m := by
    intro m
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (e m)
    refine ⟨y, e.injective ?_⟩
    rw [map_smul, LinearEquiv.apply_symm_apply, ← hy, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      ← map_mul, mul_one]
  refine ⟨inferInstance, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := (IsLocalRing.finite_quotient_iff (R := O)).mp hQa
    refine ⟨n + 1, Nat.succ_pos n, fun m => ?_⟩
    have hmem : (l : O) ^ (n + 1) ∈ Ideal.span {a} :=
      hn (Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.pow_mem_pow hlm (n + 1)))
    apply e.injective
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
    exact hkill _ hmem _
  · intro d hd
    haveI : Finite (O ⧸ Ideal.span {d}) := finite_quot d hd
    let φ : M →ₗ[O] M := LinearMap.lsmul O M d
    have hker : Nat.card {m : M // d • m = 0} = Nat.card (LinearMap.ker φ) :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun m => by simp [φ]))
    have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker φ).toAddSubgroup
    have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range φ).toAddSubgroup
    change Nat.card M = Nat.card (M ⧸ LinearMap.ker φ) * Nat.card (LinearMap.ker φ) at h1
    change Nat.card M = Nat.card (M ⧸ LinearMap.range φ) * Nat.card (LinearMap.range φ) at h2
    rw [Nat.card_congr φ.quotKerEquivRange.toEquiv] at h1
    have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    have heq : Nat.card (LinearMap.ker φ) = Nat.card (M ⧸ LinearMap.range φ) := by
      have h3 := h1.symm.trans h2
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h3, mul_comm])
    rw [hker, heq]
    let x0 : M := e.symm (Ideal.Quotient.mk _ 1)
    let f : O →ₗ[O] M ⧸ LinearMap.range φ :=
      (LinearMap.range φ).mkQ ∘ₗ LinearMap.toSpanSingleton O M x0
    have hle : Ideal.span {d} ≤ LinearMap.ker f := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      simp only [SetLike.mem_coe, LinearMap.mem_ker, f, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨x0, rfl⟩
    apply Nat.card_le_card_of_surjective ((Ideal.span {d}).liftQ f hle)
    intro z
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ z
    obtain ⟨y, rfl⟩ := hgen m
    exact ⟨Submodule.Quotient.mk y, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoLineZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

theorem UpperTheory.V.X.So.lineZero :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (G Γ ι : Type) [Group G] [Group Γ] [TopologicalSpace G] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G Γ ι) [Finite (ResidueField O)], F.Cl1 → ∀ s : ℕ, LineVan F 0 (lineChar F 0 s) := by
  intro O _ _ _ _ G Γ ι _ _ _ _ F _ hCl s z hz hcont hN hI _
  have hθ : ∀ u ∈ F.η.ker, lineChar F 0 s u = 1 := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    simp [lineChar, etaO, hu]
  have hz1 : z 1 = 0 := by
    have e := hz 1 1
    simp at e
    exact e
  have hadd : ∀ u w, u ∈ F.η.ker → z (u * w) = z u + z w := by
    intro u w hu
    simp [hz u w, hθ u hu]
  have hpow : ∀ u ∈ F.η.ker, ∀ n : ℕ, z (u ^ n) = n * z u := by
    intro u hu n
    induction n with
    | zero => simp [hz1]
    | succ n ih =>
      rw [pow_succ, hadd _ _ (F.η.ker.pow_mem hu n), ih]
      push_cast
      ring
  have hvan : ∀ v (t : F.D v), t ∈ F.Iv v → F.η (F.loc v t) = 1 → z (F.loc v t) = 0 := by
    intro v t ht hηt
    by_cases hv : v ∈ F.Tb
    · exact hI rfl v hv t ht
    · have hmem : t ^ Nat.card (ResidueField O)ˣ ∈ F.Nv v := by
        simp only [UnitaryThreeInertia.Frame.Nv, UnitaryThreeInertia.kerBar, Subgroup.mem_inf, MonoidHom.mem_ker, map_pow]
        refine ⟨⟨Subgroup.pow_mem _ ht _, ?_⟩, pow_card_eq_one'⟩
        simp only [UnitaryThreeInertia.Frame.ηv, MonoidHom.comp_apply]
        rw [hηt, one_pow]
      have h0 := hN v hv _ hmem
      rw [map_pow, hpow _ (MonoidHom.mem_ker.mpr hηt)] at h0
      have hn : ((Nat.card (ResidueField O)ˣ : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      exact (mul_eq_zero.mp h0).resolve_left hn
  have hall : ∀ N : ℕ, ∀ u ∈ F.η.ker, z u ∈ (maximalIdeal O) ^ N := by
    intro N
    let χ : F.η.ker →* Multiplicative (O ⧸ (maximalIdeal O) ^ N) :=
      { toFun := fun u => Multiplicative.ofAdd (Ideal.Quotient.mk _ (z u))
        map_one' := by simp [hz1]
        map_mul' := by
          intro u w
          simp [hadd u.1 w.1 u.2, ofAdd_add] }
    have hlc : IsLocallyConstant χ := by
      exact ((hcont N).comp_continuous (continuous_subtype_val (p := fun x => x ∈ F.η.ker))).comp
        Multiplicative.ofAdd
    have hχ : χ = 1 := by
      refine hCl _ χ hlc ?_
      intro v t g h ht
      have hηt : F.η (F.loc v t) = 1 := by
        have h' := MonoidHom.mem_ker.mp h
        rw [map_mul, map_mul, map_inv, mul_comm (F.η g), mul_assoc, mul_inv_cancel, mul_one] at h'
        exact h'
      have hz0 := hvan v t ht hηt
      have e1 := hz (g * F.loc v t) g⁻¹
      have e2 := hz g (F.loc v t)
      have e3 := hz g g⁻¹
      rw [mul_inv_cancel, hz1] at e3
      rw [map_mul, hθ _ (MonoidHom.mem_ker.mpr hηt), mul_one] at e1
      have hc : z (g * F.loc v t * g⁻¹) = 0 := by
        linear_combination e1 + e2 - e3 + ((lineChar F 0 s g : Oˣ) : O) * hz0
      show Multiplicative.ofAdd (Ideal.Quotient.mk _ (z (g * F.loc v t * g⁻¹))) = 1
      rw [hc]
      simp
    intro u hu
    have e := congrArg (fun f => f ⟨u, hu⟩) hχ
    simp only [MonoidHom.one_apply] at e
    exact Ideal.Quotient.eq_zero_iff_mem.mp (Multiplicative.ofAdd.injective e)
  have hker : ∀ u ∈ F.η.ker, z u = 0 := by
    intro u hu
    have hm : z u ∈ ⨅ N : ℕ, (maximalIdeal O) ^ N := Submodule.mem_iInf _ |>.mpr fun N => hall N u hu
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ Ideal.IsPrime.ne_top'] at hm
    simpa using hm
  have hU : CobOn (lineChar F 0 s) z (F.η.ker ⊓ ⊤) :=
    cobOn_of_eq_zero _ (fun g hg => hker g hg.1)
  have hrel : F.η.ker.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_ker]
    exact Nat.card_pos.ne'
  exact So.cobIndex O Γ (lineChar F 0 s) z hz F.η.ker ⊤ hrel hU
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoVanEOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

private theorem UpperTheory.V.X.So.vanE_wt_rev (a b : Fin 3) : U3.wt b.rev a.rev = U3.wt a b := by
  revert a b
  decide

private theorem UpperTheory.V.X.So.vanE_char {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : UnitaryThreeInertia.Frame O G Γ ι) (j : ℤ) (s : ℕ) (g : Γ) :
    (lineChar F j s g : O) = ((F.Ψ g ^ j : Oˣ) : O) * (if F.η g = 1 then 1 else (-1) ^ s) := by
  rcases Int.units_eq_one_or (F.η g) with h | h
  · simp [lineChar, etaO, h]
  · simp [lineChar, etaO, h]

private theorem UpperTheory.V.X.So.vanE_ad {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : UnitaryThreeInertia.Frame O G Γ ι) (s : ℕ) (g : Γ) (X : Matrix (Fin 3) (Fin 3) O) (a b : Fin 3) :
    U3.adRep (U3.r0 F.η F.Ψ) g X a b - (-1) ^ s * U3.adRep (U3.r0 F.η F.Ψ) g X b.rev a.rev =
      (lineChar F (U3.wt a b) s g : O) * (X a b - (-1) ^ s * X b.rev a.rev) := by
  rw [U3.adRep_baseLift_apply, U3.adRep_baseLift_apply, So.vanE_char, So.vanE_wt_rev, Fin.rev_rev, Fin.rev_rev]
  have h : ((-1 : O) ^ s) * (-1) ^ s = 1 := by rw [← mul_pow]; simp
  split_ifs
  · ring
  · linear_combination (((F.Ψ g ^ U3.wt a b : Oˣ) : O) * X b.rev a.rev) * h

theorem UpperTheory.V.X.So.vanEOf :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (G Γ ι : Type) [Group G] [Group Γ] [TopologicalSpace G] [TopologicalSpace Γ] (F : UnitaryThreeInertia.Frame O G Γ ι), (∀ j : ℤ, j ≤ 0 → ∀ s : ℕ, LineVan F j (lineChar F j s)) → F.VanE := by
  intro O _ _ _ _ G Γ ι _ _ _ _ F hL j hj γ hγw hcoc hcont hN hI hD
  have hz : ∀ g a b, U3.wt a b ≠ j → γ g a b = 0 := fun g a b h => hγw g a b h
  let z : Fin 3 → Fin 3 → ℕ → Γ → O := fun a b s g => γ g a b - (-1) ^ s * γ g b.rev a.rev
  have key : ∀ (a b : Fin 3) (s : ℕ), CobOn (lineChar F (U3.wt a b) s) (z a b s) ⊤ := by
    intro a b s
    by_cases hw : U3.wt a b = j
    · have hcz : Coc (lineChar F j s) (z a b s) := by
        intro g h
        have e := UpperTheory.V.X.So.vanE_ad F s g (γ h) a b
        rw [hw] at e
        simp only [z, hcoc g h, Matrix.add_apply]
        linear_combination e
      have hcc : Alg.AdicCont (IsLocalRing.maximalIdeal O) (z a b s) := by
        intro N
        have h1 := hcont a b N
        have h2 := hcont b.rev a.rev N
        have h3 := h1.comp₂ h2 (fun x y => x - Ideal.Quotient.mk _ ((-1 : O) ^ s) * y)
        convert h3 using 1
        funext g
        simp [z, map_sub, map_mul]
      have hnz : ∀ v ∉ F.Tb, ∀ t ∈ F.Nv v, z a b s ((F.loc v) t) = 0 := by
        intro v hv t ht
        simp [z, hN v hv t ht]
      have hiz : j = 0 → ∀ v ∈ F.Tb, ∀ t ∈ F.Iv v, z a b s ((F.loc v) t) = 0 := by
        intro h0 v hv t ht
        simp [z, hI h0 v hv t ht]
      have hdz : j < 0 → ∃ y, ∀ (g : ↥(F.D F.vl)), (F.ηv F.vl) g = 1 →
          z a b s ((F.loc F.vl) g) = ↑((lineChar F j s) ((F.loc F.vl) g)) * y - y := by
        intro hneg
        obtain ⟨Y, -, hY⟩ := hD hneg
        refine ⟨-(Y a b - (-1) ^ s * Y b.rev a.rev), fun g hg => ?_⟩
        have e := UpperTheory.V.X.So.vanE_ad F s ((F.loc F.vl) g) Y a b
        rw [hw] at e
        simp only [z, hY g hg, U3.cob, Matrix.sub_apply]
        linear_combination -e
      rw [hw]
      exact hL j hj s (z a b s) hcz hcc hnz hiz hdz
    · apply cobOn_of_eq_zero
      intro g _
      have h1 := hz g a b hw
      have h2 := hz g b.rev a.rev (by rw [UpperTheory.V.X.So.vanE_wt_rev]; exact hw)
      simp [z, h1, h2]
  have key0 : ∀ a b, ∃ c : O, c ≠ 0 ∧ ∃ m : O, ∀ g ∈ (⊤ : Subgroup Γ),
      c * z a b 0 g = ↑((lineChar F (U3.wt a b) 0) g) * m - m := fun a b => key a b 0
  have key1 : ∀ a b, ∃ c : O, c ≠ 0 ∧ ∃ m : O, ∀ g ∈ (⊤ : Subgroup Γ),
      c * z a b 1 g = ↑((lineChar F (U3.wt a b) 1) g) * m - m := fun a b => key a b 1
  choose c0 hc0 m0 hm0 using key0
  choose c1 hc1 m1 hm1 using key1
  set A : O := ∏ a, ∏ b, c0 a b * c1 a b with hA
  have hd0 : ∀ a b, ∃ k, A = c0 a b * k := fun a b =>
    (dvd_mul_right _ _).trans ((Finset.dvd_prod_of_mem (fun b => c0 a b * c1 a b) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a => ∏ b, c0 a b * c1 a b) (Finset.mem_univ a)))
  have hd1 : ∀ a b, ∃ k, A = c1 a b * k := fun a b =>
    (dvd_mul_left _ _).trans ((Finset.dvd_prod_of_mem (fun b => c0 a b * c1 a b) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a => ∏ b, c0 a b * c1 a b) (Finset.mem_univ a)))
  choose k0 hk0 using hd0
  choose k1 hk1 using hd1
  have hP0 : ∀ a b g, A * z a b 0 g = ↑((lineChar F (U3.wt a b) 0) g) * (k0 a b * m0 a b) - k0 a b * m0 a b := by
    intro a b g
    linear_combination k0 a b * hm0 a b g (Subgroup.mem_top g) + z a b 0 g * hk0 a b
  have hP1 : ∀ a b g, A * z a b 1 g = ↑((lineChar F (U3.wt a b) 1) g) * (k1 a b * m1 a b) - k1 a b * m1 a b := by
    intro a b g
    linear_combination k1 a b * hm1 a b g (Subgroup.mem_top g) + z a b 1 g * hk1 a b
  have hAne : A ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ =>
    Finset.prod_ne_zero_iff.mpr fun b _ => mul_ne_zero (hc0 a b) (hc1 a b)
  have h4 : (4 : O) ≠ 0 := by norm_num
  let X : Matrix (Fin 3) (Fin 3) O := Matrix.of fun a b =>
    -((k0 a b * m0 a b - k0 b.rev a.rev * m0 b.rev a.rev) + (k1 a b * m1 a b + k1 b.rev a.rev * m1 b.rev a.rev))
  refine ⟨4 * A, mul_ne_zero h4 hAne, X, fun g => ?_⟩
  ext a b
  have e0 := hP0 a b g
  have e0' := hP0 b.rev a.rev g
  have e1 := hP1 a b g
  have e1' := hP1 b.rev a.rev g
  rw [UpperTheory.V.X.So.vanE_wt_rev] at e0' e1'
  rw [UpperTheory.V.X.So.vanE_char] at e0 e0' e1 e1'
  simp only [z, Fin.rev_rev] at e0 e0' e1 e1'
  simp only [U3.cob, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, U3.adRep_baseLift_apply, X, Matrix.of_apply, Fin.rev_rev]
  by_cases hη : F.η g = 1
  · simp only [hη, if_true] at e0 e0' e1 e1' ⊢
    linear_combination e0 - e0' + e1 + e1'
  · simp only [hη, if_false] at e0 e0' e1 e1' ⊢
    linear_combination e0 - e0' + e1 + e1'
end

