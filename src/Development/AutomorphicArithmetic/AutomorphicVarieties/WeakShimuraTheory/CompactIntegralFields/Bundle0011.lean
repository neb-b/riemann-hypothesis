module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.LinClosedOfAdic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegCosetFour
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.StabilizerIndexBounds.NonComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.H4
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.h4 :
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (F : W.GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l]
      (r : W.Resid F O 4) (x : W.Point r), Nonempty F.Vl → (∀ v i, Alg.AdicCont (maximalIdeal x.A) fun g => ((x.ψ v i g : x.Aˣ) : x.A)) →
      (∀ v i j, i ≠ j → ∃ g, F.φ v g ∈ F.G' ∧ r.psib v i g = r.psib v j g ∧ x.ψ v i g ≠ x.ψ v j g) →
      U3.MatIrr ⊤ (W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)) →
      (∀ η : F.G₀ →* (ResidueField O)ˣ, η ^ 2 = 1 → (F.eps O (ResidueField O)).ker ≤ η.ker → (∀ i, ∃ j, η * r.chib i = r.chib j) → η = 1) →
      (∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (r.chib i / r.chib j) ^ n ≠ 1) → x.N1 ∧ x.TypeI ∧ x.N3 := by
  intro l _ hl F O _ _ _ _ _ r x ⟨v⟩ _ ha hb hc hd
  classical
  have hlp : l.Prime := Fact.out
  haveI : CharP x.K l := charP_of_injective_algebraMap (algebraMap (ResidueField O) x.K).injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  haveI hN : F.G'.Normal := MonoidHom.normal_ker _
  let j : x.A →+* x.Fb := (algebraMap x.Fr x.Fb).comp (algebraMap x.A x.Fr)
  have hj : Function.Injective j := (algebraMap x.Fr x.Fb).injective.comp (IsFractionRing.injective x.A x.Fr)
  let ρ : F.G₀ →* Matrix (Fin 4) (Fin 4) x.Fb := W.mat (W.pushRep (algebraMap x.Fr x.Fb) x.ρF)
  have hρ : ∀ g, ρ g = (W.mat x.ρ g).map j := fun g => rfl
  have two : ∀ (k : Type) [Field k] [CharP k l], (2 : k) ≠ 0 := fun k _ _ h =>
    hl ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 ((CharP.cast_eq_zero_iff k l 2).1 (by exact_mod_cast h)))
  haveI : CharP x.Fb l := charP_of_injective_ringHom (j.comp (PowerSeries.C : x.K →+* x.A)).injective l
  obtain ⟨cpR, cpL⟩ := h4Cp l F O 4 r x

  obtain ⟨g, hg, hfree⟩ := exists_mem_powerSeries_char_ratios_not_isOfFinOrder l (F.Gv v) x.K 4 (x.ψ v) (F.G'.comap (F.φ v)) fun a b hab => by
    obtain ⟨s, h1, h2, h3⟩ := ha v a b hab
    refine ⟨s, h1, ?_, h3⟩
    have h4 : ∀ i, PowerSeries.constantCoeff (x.ψ v i s : PowerSeries x.K) =
        algebraMap (ResidueField O) x.K (r.psib v i s) := fun i =>
      congrArg Units.val (DFunLike.congr_fun (x.ψ_red v i) s)
    rw [h4, h4, h2]
  let a : Fin 4 → x.Fbˣ := fun i => Units.map (j : x.A →* x.Fb) (x.ψ v i g)
  have hu : (ρ (F.φ v g)).charpoly = ∏ i, (X - C (a i : x.Fb)) := by
    rw [hρ, Matrix.charpoly_map, cpL, Polynomial.map_prod]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hfa : ∀ s t, s ≠ t → ¬ IsOfFinOrder (a s / a t) := fun s t hst h => hfree s t hst <| by
    rw [← _root_.map_div] at h
    exact (Function.Injective.isOfFinOrder_iff (Units.map_injective (f := (j : x.A →* x.Fb)) hj)).1 h
  have hsep := charpoly_pow_separable_of_eigenvalue_ratios_not_finOrder _ 4 _ a hu hfa
  have hcomm : commutator F.G₀ ≤ F.G' := Abelianization.commutator_subset_ker _

  have hI : x.TypeI := by
    by_contra hI
    obtain ⟨V, S, hV0, hV1, hNS, hS, hSi⟩ := exists_stabilizer_index_dvd_of_not_irreducible_restriction x.Fb F.G₀ 4 ρ hb F.G' hcomm
      ⟨_, hg, by simpa using hsep 1 one_pos⟩ hI
    obtain ⟨η, hη, hSη, hcp⟩ := exists_sign_twist_charpoly_of_not_irreducible_restriction x.Fb F.G₀ (two _) ρ hb S (hcomm.trans hNS) hSi fun h =>
      (h V fun s hs => (hS s).1 hs).elim hV0 hV1
    haveI : S.FiniteIndex := ⟨fun h => by simp [h] at hSi⟩
    have hSo : IsOpen (S : Set F.G₀) := by
      refine S.isOpen_of_isClosed_of_finiteIndex ?_
      have h1 := isClosed_setOf_matrix_stabilizes_submodule F.G₀ x.Fb 4 _ (Pr.linClosedOfAdic F.G₀ x.A x.Fb j hj 4 (W.mat x.ρ) x.cont) V
      convert h1 using 1
      ext s
      exact hS s
    have hk := sign_char_eq_one_of_cyclotomic_sub_one_not_isUnit l hl F.G₀ (F.ε.comp F.η.ker.subtype) (F.ε_cont.comp continuous_subtype_val) η
      (Subgroup.isOpen_mono hSη hSo) (hNS.trans hSη)
    have h1 := hc (W.pushCh (Int.castRingHom (ResidueField O)) η) ?_ ?_
      (exists_sign_twist_char_eq_of_charpoly_twist_invariant x.Fb (ResidueField O) x.K x.A F.G₀ 4 (W.mat x.ρ) j _ _ r.chib η hj cpR hcp)
    · refine hη (MonoidHom.ext fun s => ?_)
      rcases Int.units_eq_one_or (η s) with h | h
      · exact h
      · have h2 := congrArg Units.val (DFunLike.congr_fun h1 s)
        simp only [MonoidHom.comp_apply, h] at h2
        exact absurd (by simp at h2; linear_combination -h2) (two (ResidueField O))
    · ext s
      rcases Int.units_eq_one_or (η s) with h | h <;> simp [h]
    · intro s hs
      have h2 : η s = 1 := hk s fun h => by
        have h3 := h.map ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O))
        have h4 : ((algebraMap O (ResidueField O)).comp (algebraMap ℤ_[l] O)) ((F.ε.comp F.η.ker.subtype) s : ℤ_[l]) = 1 :=
          congrArg Units.val (MonoidHom.mem_ker.1 hs)
        rw [map_sub, h4, map_one, sub_self] at h3
        exact not_isUnit_zero h3
      simp [MonoidHom.mem_ker, h2]
  refine ⟨fun w => ⟨fun s t hst h => ?_, fun s t hst h => ?_⟩, hI, ?_⟩
  · obtain ⟨y, -, -, h3⟩ := ha w s t hst
    exact h3 (by rw [h])
  · obtain ⟨y, h1, -, h3⟩ := ha w s t hst.ne
    have h4 : (F.ε.comp F.η.ker.subtype) (F.φ w y) = 1 := h1
    refine h3 ?_
    rw [h, MonoidHom.mul_apply, MonoidHom.comp_apply, W.GFrame.eps, MonoidHom.comp_apply, h4, map_one, mul_one]
  · have hsp : Submodule.span x.Fb (Set.range (ρ.comp F.G'.subtype)) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hI N fun s hs => hN ⟨s, hs⟩
    have hsp' : Submodule.span x.Fb (Set.range ρ) = ⊤ :=
      KStar.Schema.span_eq_top_of_irreducible _ fun N hN => hb N fun s _ => hN s
    have hnc := exists_noncommuting_images_in_finiteIndex_normal_subgroup x.Fb x.K x.A F.G₀ ρ j PowerSeries.constantCoeff
      (fun i => W.pushCh (algebraMap (ResidueField O) x.K) (r.chib i)) hj
      (fun s => ⟨(W.mat x.ρ s).charpoly, by rw [hρ, Matrix.charpoly_map], cpR s⟩) hsp' (by
        obtain ⟨s, t, h⟩ := hd
        refine ⟨s, t, fun n h0 h4 he => h n h0 h4 (MonoidHom.ext fun y => ?_)⟩
        apply Units.map_injective (f := (algebraMap (ResidueField O) x.K : ResidueField O →* x.K)) (RingHom.injective _)
        simpa using DFunLike.congr_fun he y) F.G' _ hg hsep
    refine exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex F.G₀ F.G' (fun s => (W.mat x.ρF s).charpoly.Separable) fun V hV σ => ?_
    obtain ⟨y, hy, hs⟩ := AlgebraTools.regCosetFour x.Fb F.G' (two _) (ρ.comp F.G'.subtype)
      (fun f => (isClosed_zeroLocus_mvPolynomial_eval_adicContinuous F.G₀ x.A x.Fb (Fin 4 × Fin 4) j hj (fun p s => W.mat x.ρ s p.1 p.2) (fun p => x.cont p.1 p.2) f).preimage
        continuous_subtype_val) hsp ⟨⟨_, hg⟩, a, hu, hfa⟩ (fun N _ h2 h3 => hnc N h2 h3) V hV σ
    refine ⟨y, hy, (Polynomial.separable_map (algebraMap x.Fr x.Fb)).1 ?_⟩
    rw [← Matrix.charpoly_map]
    exact hs
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PfConst
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

section Abstract

variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private theorem pf_const [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) {y : R} (hy : IsIntegral O y) :
    ∃ a, y = algebraMap O R a := by
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) y
  refine ⟨a, ?_⟩
  by_contra hne
  letI : Algebra (ResidueField O) R := (Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R) h0).toAlgebra
  haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h1 : IsIntegral (ResidueField O) (y - algebraMap O R a) := (hy.sub isIntegral_algebraMap).tower_top
  exact ha (h1.isUnit (sub_ne_zero.2 hne))

private theorem pf_sect (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ s : B →ₐ[O] R, (∀ b ∈ maximalIdeal B, s b = 0) ∧ ∀ (f : B →ₐ[O] R) (b : B), (∃ a, f b = algebraMap O R a) → f b = s b := by
  let j : ResidueField O →ₐ[O] R := Ideal.Quotient.liftₐ (maximalIdeal O) (Algebra.ofId O R) h0
  refine ⟨j.comp (res O B), fun b hb => ?_, ?_⟩
  · rw [AlgHom.comp_apply, (res_eq_zero_iff O B b).2 hb, map_zero]
  · rintro f b ⟨a, ha⟩
    rw [AlgHom.comp_apply, ← res_map f, ha, AlgHom.commutes, AlgHom.commutes]

private theorem pf_cont {Γ B : Type} [TopologicalSpace Γ] [CommRing B] [Algebra O B] [IsCO O B] (f : B →ₐ[O] R) {u : Γ → B}
    (hu : AdicCont (maximalIdeal B) u) : AdicCont (maximalIdeal R) fun g => f (u g) := fun N => by
  have hle : maximalIdeal B ^ N ≤ (maximalIdeal R ^ N).comap (f : B →+* R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hu N).comp (Ideal.quotientMap _ (f : B →+* R) hle)

private theorem pf_lam {l : ℕ} [Fact l.Prime] {F : W.GFrame l} [Algebra ℤ_[l] O] {n : ℕ} {r : W.Resid F O n} (Λ : W.LamObj r)
    (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : Λ.Λ →ₐ[O] R)
    (hf : ∀ v i g, ∃ a, f (Λ.κ v i g) = algebraMap O R a) (x : Λ.Λ) : ∃ a, f x = algebraMap O R a := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 Λ.Λ
  have hi : W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* R) (Λ.κ v i) := fun v i => by
    obtain ⟨ψ, hψ, he⟩ := Λ.inert v i
    refine ⟨W.pushCh (f : Λ.Λ →+* R) ψ, ⟨pf_cont f hψ.cont, fun g => (res_map f _).trans (hψ.red g), fun g => ?_⟩, ?_⟩
    · show f (ψ g) = _
      rw [hψ.mu g, f.commutes]
    · exact congrArg (W.pushCh (f : Λ.Λ →+* R)) he
  have he : f = s := (Λ.univ R _ hi).unique (fun _ _ => rfl) fun v i =>
    MonoidHom.ext fun g => Units.ext (hsf f _ (hf v i g)).symm
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
  have h1 := hs _ ha
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h1
  exact ⟨a, he ▸ h1⟩

private theorem pf_int {Λ B : Type} [CommRing Λ] [CommRing B] [Algebra O Λ] [Algebra O B] (t : Λ →ₐ[O] B) (J : Ideal B)
    (hfin : ((Ideal.Quotient.mk J).comp (t : Λ →+* B)).Finite) (f : B →ₐ[O] R) (hJ : ∀ b ∈ J, f b = 0)
    (hc : ∀ x, ∃ a, f (t x) = algebraMap O R a) (b : B) : IsIntegral O (f b) := by
  obtain ⟨p, hp, hb⟩ := hfin.to_isIntegral (Ideal.Quotient.mk J b)
  have h1 := congrArg (Ideal.Quotient.lift J (f : B →+* R) hJ) hb
  rw [hom_eval₂, map_zero] at h1
  have hl : p.map ((f.comp t : Λ →ₐ[O] R) : Λ →+* R) ∈ lifts (algebraMap O R) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    obtain ⟨a, ha⟩ := hc (p.coeff n)
    exact ⟨a, by rw [coeff_map]; exact ha.symm⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hm, ?_⟩
  rw [← eval_map, hq, eval_map]
  exact h1

variable {O₀ Γ : Type} [CommRing O₀] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O₀ Γ} {a : O₀ →+* O} (X : Space Φ a)

private theorem pf_sq (f : X.B →ₐ[O] R) (g : Γ) (hg : ∀ n, IsIntegral O (f ((X.cp (g ^ 2)).coeff n))) (n : ℕ) :
    IsIntegral O (f ((X.cp g).coeff n)) := by
  let S₀ : Subring X.B := (integralClosure O R).toSubring.comap (f : X.B →+* R)
  let S : Subring X.A := S₀.map (algebraMap X.B X.A)
  have h1 := AlgebraTools.charpolyPowInt X.A (Fin 4) S (X.P.r g) 2 two_pos (fun i => by
    rw [← map_pow, ← X.cp_map, coeff_map]
    exact ⟨_, hg i, rfl⟩) n
  rw [← X.cp_map, coeff_map] at h1
  obtain ⟨p, hp, hb⟩ := h1
  have hl : p.map S.subtype ∈ lifts ((algebraMap X.B X.A).comp S₀.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro m
    obtain ⟨y, hy, he⟩ := (p.coeff m).2
    exact ⟨⟨y, hy⟩, by rw [coeff_map]; exact he⟩
  obtain ⟨q, hq, -, hm⟩ := lifts_and_natDegree_eq_and_monic hl (hp.map _)
  have h2 : q.eval₂ S₀.subtype ((X.cp g).coeff n) = 0 := by
    apply X.inj
    rw [hom_eval₂, map_zero, ← eval_map, hq, eval_map]
    exact hb
  let j : S₀ →+* integralClosure O R := ((f : X.B →+* R).comp S₀.subtype).codRestrict _ fun y => y.2
  have h3 : IsIntegral (integralClosure O R) (f ((X.cp g).coeff n)) := by
    refine ⟨q.map j, hm.map j, ?_⟩
    have h4 := congrArg (f : X.B →+* R) h2
    rw [hom_eval₂, map_zero] at h4
    rw [eval₂_map]
    exact h4
  exact isIntegral_trans _ h3

private theorem pf_gen [IsDomain R] (h0 : ∀ a ∈ maximalIdeal O, algebraMap O R a = 0) (f : X.B →ₐ[O] R)
    (h1 : ∀ g n, IsIntegral O (f ((X.cp g).coeff n))) (h2 : ∀ v i, ∀ s ∈ Φ.Gv v, IsIntegral O (f (X.ψ v i s))) :
    ∀ b ∈ maximalIdeal X.B, f b = 0 := by
  obtain ⟨s, hs, hsf⟩ := pf_sect h0 X.B
  rw [X.genB R f s (fun g n => hsf f _ (pf_const h0 (h1 g n))) fun v i g hg => hsf f _ (pf_const h0 (h2 v i g hg))]
  exact hs

private theorem pf_unit {u : Oˣ} {y : R} (h : IsIntegral O (algebraMap O R u * y)) : IsIntegral O y := by
  have h1 := (isIntegral_algebraMap (R := O) (A := R) (x := (u⁻¹ : Oˣ))).mul h
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h1

end Abstract

section Galois

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} (T : Tower D)

private theorem pf_lift {g : G T.F Ω} (hg : resQ T.F g ∈ T.K.fixingSubgroup) : ∃ g' : G T.L Ω, resLe T.F_le g' = g := by
  have h1 : resQ T.F g ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => g.commutes ⟨x, hx⟩
  have h2 : resQ T.F g ∈ T.L.fixingSubgroup := by
    rw [T.hL, IntermediateField.fixingSubgroup_sup]
    exact ⟨h1, hg⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at h2
  exact ⟨{ g.toRingEquiv with commutes' := fun x => h2 x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

private theorem pf_sqK (g : G ℚ Ω) : g ^ 2 ∈ T.K.fixingSubgroup := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : IsGalois ℚ Ω := inferInstance
  have hi : T.K.fixingSubgroup.index = 2 := by
    rw [← T.degK]
    exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω T.K).symm
  exact Subgroup.sq_mem_of_index_two hi g

end Galois
end

