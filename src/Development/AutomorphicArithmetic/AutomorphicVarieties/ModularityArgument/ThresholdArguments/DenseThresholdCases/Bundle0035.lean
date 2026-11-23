module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.PrimEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.MinPol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.DerZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ArithmeticPointPurity
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPmFin
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

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
theorem UpperTheory.V.Ws.exists_pow_maximalIdeal_le_of_modular_phi :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (Λ : W.LamObj K.r) (ι : PadicAlgCl l ≃+* ℂ) (J₀ : Ideal B.B), B.ModularAlt ι J₀ Λ → ∀ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X 0 B φ → ∀ J : Ideal X.B, J = J₀.map φ → ∃ n : ℕ, maximalIdeal X.B ^ n ≤ J ⊔ (maximalIdeal c'.O).map (algebraMap c'.O X.B) ⊔
        Ideal.span {b | ∃ v i, ∃ s ∈ Ine (F := T.F) (T.pl v), b = X.ψ v i s - 1} := by
  intro _ Ω _ _ _ l _ c D T hT _ c' h K X B Λ ι J₀ hM φ hφ J hJ
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro q ⟨hq, hp⟩
  have hl : l ∈ D.S := hT.2.elim (fun x => x.1.1.l_mem) fun x => x.1.1.l_mem
  let π : X.B →ₐ[c'.O] X.B ⧸ q := Ideal.Quotient.mkₐ c'.O q
  haveI : IsCO c'.O (X.B ⧸ q) := co_quot c'.O X.B _ π Ideal.Quotient.mk_surjective
  have hπ : ∀ b, π b = 0 ↔ b ∈ q := fun b => Ideal.Quotient.eq_zero_iff_mem
  have h0 : ∀ a ∈ maximalIdeal c'.O, algebraMap c'.O (X.B ⧸ q) a = 0 := fun a ha => by
    rw [← π.commutes, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
  have hone : ∀ v i, ∀ s ∈ Ine (F := T.F) (T.pl v), π (X.ψ v i s) = 1 := fun v i s hs => by
    rw [← sub_eq_zero, ← map_one π, ← map_sub, hπ]
    exact hq (Ideal.mem_sup_right (Ideal.subset_span ⟨v, i, s, hs, rfl⟩))
  have hΛ := pf_lam Λ h0 ((π.comp φ).comp (Λ.toPair B.u)) fun v i g => by
    have h1 : Λ.toPair B.u (Λ.κ v i g) = B.u.ψ v i g :=
      congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec K.r Λ B.u v i) g)
    refine ⟨K.κ g.1.1 * K.β g.1.1 ^ 0, ?_⟩
    have h2 : resLe T.F_le g.1.1 ∈ Ine (F := T.F) (T.pl (K.e v)) :=
      (congrArg (fun A => resLe T.F_le g.1.1 ∈ Ine (F := T.F) A) (K.hA v)).mp g.2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, h1, hφ.2 v i g.1, map_mul, π.commutes, hone _ _ _ h2, mul_one]
  have hB := pf_int (Λ.toPair B.u) J₀ hM.ring.fin (π.comp φ) (fun b hb => by
    rw [AlgHom.comp_apply, hπ]
    exact hq (Ideal.mem_sup_left (Ideal.mem_sup_left (hJ ▸ Ideal.mem_map_of_mem _ hb)))) hΛ
  intro b hb
  rw [← hπ]
  refine pf_gen X h0 π (fun g => pf_sq X π g fun n => ?_) (fun v i s hs => ?_) b hb
  · obtain ⟨g', hg'⟩ := pf_lift T (g := g ^ 2) (by rw [map_pow]; exact pf_sqK T _)
    have h1 := hB ((B.u.D.chi (MonoidAlgebra.single (K.V.pr g') 1)).coeff n)
    have h2 := congrArg (fun p => p.coeff n) (hφ.1 g')
    simp only [coeff_map, coeff_scaleRoots, hg'] at h2
    rw [AlgHom.comp_apply] at h1
    erw [h2] at h1
    rw [map_mul, map_pow, π.commutes, mul_comm, ← map_pow, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
      ← Units.val_pow_eq_pow_val] at h1
    exact pf_unit h1
  · obtain ⟨v, rfl⟩ := K.e.surjective v
    obtain ⟨g', rfl⟩ := pf_lift T (g := s) (hT.1.split l hl _ (T.ovl (K.e v)) hs)
    have hg : g' ∈ Dec (F := T.L) (K.s.A v) := by
      rw [K.hA]
      exact hs
    have h1 := hB (B.u.ψ v i ⟨g', hg⟩)
    rw [AlgHom.comp_apply, hφ.2 v i ⟨g', hg⟩, map_mul, π.commutes, ← Units.val_pow_eq_pow_val, ← Units.val_mul] at h1
    exact pf_unit h1
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnrE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series :
    UnrAlgE → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → NumE B Λ J → UpperTheory.V.J.UnrAt B J := by
  intro hU l _ L Ω _ _ _ _ _ _ s V c n r B Λ ι J m hn hiso hD hE hN
  obtain ⟨M, _, _, _, h, e₀, hId, hmu⟩ := hN
  intro x w hJ hA hI δ hδ hJδ hψ
  obtain ⟨b₀, hb₀, hopen⟩ := _root_.UpperTheory.V.J.irrOpenW_alt l L Ω s V c n r B ι J hn hE x hI
  have hlam := UpperTheory.V.J.lamDer l L Ω s V c n r B Λ x m hiso δ hδ hψ
  have hdense : ∀ a : B.B, (∀ y ∈ {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w}, y a = 0) → a ∈ J :=
    fun a ha => hD w hA.1 a fun y hy hg => ha y ⟨hy, hg⟩
  have hex : ∃ y : B.Pt, (J ≤ RingHom.ker y ∧ y.Good w) ∧ y b₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb₀ (hJ (hdense b₀ hcon))
  obtain ⟨y₀, hy₀, hyb₀⟩ := hex
  have hone := (hmu x y₀ w hJ hy₀.1 hA hy₀.2 hI (hopen y₀ w hy₀.1 hy₀.2 hyb₀)).1
  obtain ⟨e⟩ := hiso
  haveI : IsDomain (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isDomain_mvPowerSeries c.O m
  haveI : IsDomain Λ.Λ := e.toRingEquiv.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries c.O m
  haveI : IsIntegrallyClosed Λ.Λ := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherianRing Λ.Λ := UpperTheory.V.Alg.IsCO.toIsNoetherian (O := c.O)
  haveI : CharZero Λ.Λ := by
    haveI : CharZero c.O :=
      (RingHom.charZero_iff (ϕ := (c.O.val : c.O →ₐ[ℤ_[l]] PadicAlgCl l).toRingHom) Subtype.val_injective).2 inferInstance
    have hC : Function.Injective (MvPowerSeries.C : c.O →+* MvPowerSeries (Fin m) c.O) := fun a b hab => by
      simpa using congrArg MvPowerSeries.constantCoeff hab
    exact (RingHom.charZero_iff (ϕ := (e.symm.toRingEquiv : MvPowerSeries (Fin m) c.O →+* Λ.Λ).comp MvPowerSeries.C)
      (e.symm.injective.comp hC)).1 inferInstance
  exact hU c.O Λ.Λ B.B _ (Λ.toPair B.u) J M h e₀ hId x {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w} b₀ hb₀ hdense hone
    (fun y hy hyb => (hmu x y w hJ hy.1 hA hy.2 hI (hopen y w hy.1 hy.2 hyb)).2)
    δ hδ hJδ hlam
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VConjP
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published
private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩
private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [e]
  exact (Ideal.map_symm _).symm
private theorem eventually_unr {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (χ : HChar F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩
private theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ) {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ}
    (hz : (z' : ℂ) = σ z) (h : B₁.map (·⁻¹) = B.map (· * z⁻¹)) (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) : B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn,
      Real.rpow_natCast]
    push_cast
    rfl
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  have ae : ∀ B : Multiset ℂˣ, algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) :=
    fun B => by simp [algSat]
  simp only [ae] at e e₁
  clear ae
  generalize (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *
  have hs : σ c * σ c = c * c := by rw [← map_mul, hc, map_pow, map_natCast]
  have h1 : σ c ≠ 0 := (map_ne_zero σ).2 h0
  apply Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ))
    (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))
  have k1 := congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁
  have k2 := congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e
  have k3 := congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h
  simp only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k3.trans
    ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans (Multiset.map_congr rfl fun x _ => ?_))))))
  · simp [mul_comm]
  · simp [mul_comm]
  · rw [← hs]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz]
    field_simp
theorem UpperTheory.GalN.V.conjP_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Br.ConjP := by
  intro P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩
  have hreg := regAlg_of_infOf hm hinf
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π hreg σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hsat : ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ :=
    fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB
  refine ⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair K n (by omega) π χ hreg hpol
  have hF : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h1 := (letI : Module.Free (maximalRealSubfield K) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
    omega
  obtain ⟨χ', hsg, hv⟩ := UpperTheory.V.Br.charConj _ hF χ a ha σ
  refine ⟨χ', fun v => (hsg v).trans (hpol.sign v),
    UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩
  have hM1 := eventually_notMem (K := K) hM
  filter_upwards [eventually_unr (K := K) χ, hM1,
    (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2
  obtain ⟨B, hB⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π hfix w a1
  obtain ⟨B₁, hB₁⟩ := _root_.UpperTheory.V.Af.satake_k_of_printed_results P K n M π hfix (cPl w) a2
  obtain ⟨B', hB', e⟩ := hsat w B hB
  obtain ⟨B₁', hB₁', e₁⟩ := hsat _ B₁ hB₁
  rw [normV_cPl] at e₁
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw
  obtain ⟨e5, e6⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1
  refine ⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_
    (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩
  rw [e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]
end
end

