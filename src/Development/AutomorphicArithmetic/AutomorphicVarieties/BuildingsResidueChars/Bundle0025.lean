module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneUnipotentMonodromy

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusResidueDegreeFixes
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

private theorem UpperTheory.frobenius_crystalline_eq_unramified {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : ↥(K0 K)) :
    (((P.PD K).σ x : ↥(K0 K)) : Om l) = ((frobUr l ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  have h1 := (P.PD K).φ_K₀ x
  rw [P.PD_φ] at h1
  have h2 := phiB_algebraMap P ⟨x.1, x.2.2⟩
  have h3 : algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ⟨((P.PD K).σ x).1, ((P.PD K).σ x).2.2⟩ =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (frobUr l ⟨x.1, x.2.2⟩) := h1.symm.trans h2
  have : Nontrivial P.R.B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply (P.PD K).not_mem_filtration_two
    rw [Subsingleton.elim (P.PD K).t 0, map_zero]
    exact zero_mem _
  exact congrArg Subtype.val ((algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective h3)

private theorem UpperTheory.frobenius_crystalline_iterate_eq {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (n : ℕ) (x : ↥(K0 K)) :
    ((((P.PD K).σ)^[n] x : ↥(K0 K)) : Om l) = (((frobUr l ^ n) ⟨x.1, x.2.2⟩ : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', UpperTheory.frobenius_crystalline_eq_unramified, pow_succ', AlgHom.mul_apply]
    exact congrArg (fun c => ((frobUr l c : ↥(MaximalUnramifiedExtension l)) : Om l)) (Subtype.ext ih)

theorem UpperTheory.frobenius_residue_degree_fixes :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw), 0 < resDeg l w ∧ ∀ x : ↥(K0 Bw.Kw), ((P.PD Bw.Kw).σ)^[resDeg l w] x = x := by
  intro l _ P E Ω _ _ _ _ _ A w O _ _ _ Bw h hj
  refine ⟨Nat.pos_of_ne_zero fun h0 => ?_, fun x => Subtype.ext ?_⟩
  · have h1 := one_lt_normV w
    rw [normV_eq_pow (hj.mem_placesOver h), h0, pow_zero] at h1
    exact lt_irrefl _ h1
  · have h1 := weilToGK_frobUr hj (frob h) (a := 1) (b := 0)
      (actsAs_of_deg (by simp)) ⟨x.1, x.2.2⟩
    rw [mul_one, mul_zero, pow_zero] at h1
    rw [UpperTheory.frobenius_crystalline_iterate_eq, ← h1]
    exact mem_GK.mp (weilToGK Bw h (frob h)).2 _ x.2.1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetExistsLeviCongruenceFixedOfCharSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem UpperTheory.smooth_gl_one_cuspidal {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) : IsCuspidal π := by
  refine ⟨hs, fun s d e he => absurd ?_ he⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
  ext i j
  obtain rfl : i = j := Subsingleton.elim _ _
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  simpa using (mem_unipRad.1 hu).2 a i i

private theorem UpperTheory.fixed_vectors_nonzero_character {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (y : IrrRep (GL (Fin 1) k)) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1)
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h : IrrGL.of y.ρ y.smooth y.irr = IrrGL.ofChar χ hχ)
    (h1 : ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) :
    fixed y.ρ (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
  have h' : IrrGL.of y.ρ y.smooth y.irr = IrrGL.of (detRep (Fin 1) χ) (isCuspidal_detRep_one hχ).1
      (isIrreducible_ofChar _) := h
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h'
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible y.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : y.V)
  refine (Submodule.ne_bot_iff _).2 ⟨v, fun g => ?_, hv⟩
  have hg : valuation k ((g.1.val - 1) 0 0) < γ := g.2 0 0
  have h2 : χ (Matrix.GeneralLinearGroup.det g.1) = 1 := by
    refine h1 _ ?_
    simpa [Matrix.det_unique] using hg
  refine φ.toLinearEquiv.injective ?_
  have h3 := φ.toIntertwiningMap.isIntertwining _ _ g.1 v
  refine h3.trans ?_
  simp only [detRep, ofChar_apply, detChar_apply, h2, MonoidHom.one_apply, Units.val_one, one_mul, one_smul]
  rfl

theorem UpperTheory.jacquet_exists_levi_congruence_fixed_of_char_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1), HasSupport π s → (∀ y ∈ s, ∃ χ hχ, y = IrrGL.ofChar χ hχ ∧ ∀ u : kˣ, valuation k ((u : k) - 1) < γ → χ u = 1) →
    ∀ e : (Σ _ : Fin N, Fin 1) ≃ Fin N, Nontrivial (Jacquet π (unipRad k e)) →
    ∃ y : Jacquet π (unipRad k e), y ≠ 0 ∧ ∀ g : Levi k fun _ : Fin N => Fin 1,
      (∀ a, g a ∈ GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) → jac e π g y = y := by
  intro hG hZ k _ _ _ _ N V _ _ π s γ hγ hs hχ e hJ
  have hjs : IsSmooth (jac e π) := isSmooth_jac e hs.isSmooth
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hjs
  have hsm : ∀ j : Fin N, IsSmooth (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) := fun j =>
    isSmooth_comp hτsm _ (continuous_mulSingle (A := fun _ : Fin N => GL (Fin 1) k) j)
  have hy : ∀ j : Fin N, ∃ y : IrrRep (GL (Fin 1) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) : Representation ℂ (GL (Fin 1) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (hsm j), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac (d := fun _ : Fin N => 1) hG hZ hs e hτ hτs y hy
  have hfix : ∀ j : Fin N, fixed (τ.comp (MonoidHom.mulSingle (fun _ : Fin N => GL (Fin 1) k) j) :
      Representation ℂ (GL (Fin 1) k) Y) (GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) ≠ ⊥ := by
    intro j
    have hc : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp :=
      ⟨Nat.one_pos, UpperTheory.smooth_gl_one_cuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hc ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    obtain ⟨χ, hχs, h2, h3⟩ := hχ (IrrGL.of (y j).ρ (y j).smooth (y j).irr)
      (Multiset.mem_sum.2 ⟨j, Finset.mem_univ j, by rw [h1]; exact Multiset.mem_singleton_self _⟩)
    exact UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ _ _ _ (hsm j) (hy j) (GlobalTheory.CentralExponent.isCompact_cong γ hγ)
      (UpperTheory.fixed_vectors_nonzero_character (y j) γ hγ χ hχs h2 h3)
  have hcomm : ∀ (_ : Fin N) (x z : GL (Fin 1) k), x * z = z * x := by
    intro _ x z
    ext i j
    simp [Matrix.mul_apply, Subsingleton.elim i 0, Subsingleton.elim j 0, mul_comm]
  have htriv := UpperTheory.eq_one_of_irreducible_pi_abelian_fixed_ne_bot (Fin N) (fun _ => GL (Fin 1) k) hcomm Y τ
    (fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ) hτ hfix
  let H : Subgroup (Levi k fun _ : Fin N => Fin 1) :=
    Subgroup.pi Set.univ fun _ => GlobalTheory.CentralExponent.cong (Fin 1) γ hγ
  have hH : IsCompact (H : Set (Levi k fun _ : Fin N => Fin 1)) :=
    isCompact_univ_pi fun _ => GlobalTheory.CentralExponent.isCompact_cong γ hγ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ
  obtain ⟨v, hv⟩ := exists_ne (0 : Y)
  have hτf : fixed τ H ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, fun g => by
    rw [htriv g.1 fun a => g.2 a trivial]
    simp, hv⟩
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 (UpperTheory.fixed_ne_bot_of_isSubquotient_of_isCompact _ _ _ τ (jac e π) H hjs hτs hH hτf)
  refine ⟨w, hw0, fun g hg => ?_⟩
  simpa using hw ⟨g, fun a _ => hg a⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetFinerParabolicOfCharacterSupport
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem UpperTheory.jacquet_finer_parabolic_of_character_support :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : Multiset (IrrGL (k := k))), HasSupport π s → (∀ y ∈ s, y.1 = 1) →
    ∀ (r : ℕ) (d : Fin r → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin N) (j : Fin r), 2 ≤ d j → Nontrivial (Jacquet π (unipRad k e)) →
    ∃ (t : ℕ) (c : Fin t → ℕ) (f : (Σ a, Fin (c a)) ≃ Fin N), Nontrivial (Jacquet π (unipRad k f)) ∧
      (∀ p q, blk e p < blk e q → blk f p < blk f q) ∧ ∃ p q, blk f p < blk f q ∧ ¬ blk e p < blk e q := by
  intro hG hZ k _ _ _ _ N V _ _ π s hs hs1 r d e j hj hJ
  have hπ : IsSmooth π := by
    obtain ⟨h, x, -, hi, hc, e, hsub⟩ := hs
    exact hsub.isSmooth (isSmooth_parInd _ _)
  have hJs : IsSmooth (jac e π) := isSmooth_jac e hπ
  obtain ⟨Y, _, _, τ, hτ, hτs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _ (jac e π) hJ
  have hτsm : IsSmooth τ := hτs.isSmooth hJs
  have hy : ∀ j, ∃ y : IrrRep (GL (Fin (d j)) k), IsSubquotient y.ρ
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j) : Representation ℂ (GL (Fin (d j)) k) Y) := by
    intro j
    obtain ⟨X, _, _, υ, hυ, hυs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
      (τ.comp (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
      (GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hτ)
    exact ⟨⟨X, υ, hυs.isSmooth (isSmooth_comp hτsm _
      (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)), hυ⟩, hυs⟩
  choose y hy using hy
  obtain ⟨u, hu, rfl⟩ := SupportUnique.exists_sum_of_jac hG hZ hs e hτ hτs y hy
  have hnc : ¬ IsCuspidal (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep := by
    intro hc
    have hx : (IrrGL.of (y j).ρ (y j).smooth (y j).irr).IsCusp := ⟨show 0 < d j by omega, hc⟩
    have h1 := SupportUnique.eq_singleton_of_isCusp hx ((hu j).of_equiv (IrrGL.equivOf _ _ _))
    have h2 : IrrGL.of (y j).ρ (y j).smooth (y j).irr ∈ ∑ i, u i :=
      Multiset.mem_sum.2 ⟨j, Finset.mem_univ _, h1 ▸ Multiset.mem_singleton_self _⟩
    have h3 : d j = 1 := hs1 _ h2
    omega
  obtain ⟨r', d', e', hU, hJ'⟩ : ∃ (r' : ℕ) (d' : Fin r' → ℕ) (e' : (Σ a, Fin (d' a)) ≃ Fin (d j)),
      unipRad k e' ≠ ⊥ ∧
      ¬ Subsingleton (Jacquet (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep (unipRad k e')) := by
    by_contra! hn
    exact hnc ⟨(IrrGL.of (y j).ρ (y j).smooth (y j).irr).2.rep.smooth, hn⟩
  obtain ⟨t, c, f, hf⟩ := UpperTheory.exists_refinement_block_order N r r' d e j d' e'
  refine ⟨t, c, f, ?_, fun p q h => (hf p q).2 (Or.inl h), ?_⟩
  · by_contra hn
    have h0 := UpperTheory.weilDeligne_unipotent_monodromy k N V π r r' d e j d' e' t c f (fun p q => (hf p q).1)
      (not_nontrivial_iff_subsingleton.1 hn)
    let φ := (IrrGL.equivOf (y j).ρ (y j).smooth (y j).irr).symm
    have h1 : IsSubquotient (IrrGL.of (y j).ρ (y j).smooth (y j).irr).rep (y j).ρ :=
      .of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
    have h2 := (h1.trans (hy j)).trans (SupportUnique.isSubquotient_comp hτs
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) k) j))
    obtain ⟨S, g, hg⟩ := GlobalTheory.JacquetExact.isSubquotient_jac e' (isSmooth_comp hJs _
      (continuous_mulSingle (A := fun j => GL (Fin (d j)) k) j)) h2
    haveI : Subsingleton S.toSubmodule := ⟨fun a b => Subtype.ext (h0.elim _ _)⟩
    exact hJ' (Function.Surjective.subsingleton hg)
  · obtain ⟨p, q, hpq⟩ := GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.1 hU
    refine ⟨e ⟨j, p⟩, e ⟨j, q⟩, (hf _ _).2 (Or.inr ⟨p, q, rfl, rfl, hpq⟩), ?_⟩
    rw [blk_apply, blk_apply]
    exact lt_irrefl _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneSpanCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct Module GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial

theorem UpperTheory.weil_deligne_span_crystalline :
    ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {K LL : FinExt l} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsPst P ρ → IsCrys (P.PD K) ρ → Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} = ⊤ := by
  intro l _ P ι K LL V _ _ _ _ _ ρ hV hc
  have hk := mem_Dst_and_monV_eq_zero_iff l P K LL V ρ
  set S := Submodule.span ℂ {z : WDSpace P ι ρ | ∃ (x : V ⊗[ℚ_[l]] P.R.B) (y : ↥(Dpst P ρ)), x ∈ Dcris (P.PD K) ρ ∧ (y : V ⊗[ℚ_[l]] Bst P) = crisIncl P ↥LL.1 V x ∧ z = wdMk P ι ρ y} with hS
  have key : ∀ (x : V ⊗[ℚ_[l]] Bst P), x ∈ Dpst P ρ → ∃ h : x ∈ Dpst P ρ, wdMk P ι ρ ⟨x, h⟩ ∈ S := by
    intro x hx
    refine AddSubgroup.closure_induction
      (p := fun y _ => ∃ h : y ∈ Dpst P ρ, wdMk P ι ρ ⟨y, h⟩ ∈ S) ?_ ?_ ?_ ?_
      (GlobalTheory.PstLaws.mem_closure_of_isCrys P ρ hV hc x hx)
    · rintro _ ⟨c, s, hs, rfl⟩
      have hsD : s ∈ Dpst P ρ := Dst_resTo_le P ρ le_rfl ((hk s).mpr hs).1
      obtain ⟨x₀, hx₀, e⟩ := hs
      refine ⟨mulV_mem_Dpst P ρ c s hsD, ?_⟩
      have h1 : wdMk P ι ρ ⟨s, hsD⟩ ∈ S := Submodule.subset_span ⟨x₀, ⟨s, hsD⟩, hx₀, e.symm, rfl⟩
      have h2 := S.smul_mem (ι (c : Om l)) h1
      rw [← wdMk_mul] at h2
      exact h2
    · refine ⟨zero_mem _, ?_⟩
      have h1 : wdMk P ι ρ 0 ∈ S := by rw [wdMk_zero]; exact zero_mem _
      exact h1
    · rintro y z _ _ ⟨hy, h1⟩ ⟨hz, h2⟩
      refine ⟨add_mem hy hz, ?_⟩
      have h3 := S.add_mem h1 h2
      rw [← wdMk_add] at h3
      exact h3
    · rintro y _ ⟨hy, h1⟩
      refine ⟨neg_mem hy, ?_⟩
      have heq : wdMk P ι ρ ⟨-y, neg_mem hy⟩ = -wdMk P ι ρ ⟨y, hy⟩ := by
        apply eq_neg_of_add_eq_zero_left
        rw [← wdMk_add]
        have hz : (⟨-y, neg_mem hy⟩ : ↥(Dpst P ρ)) + ⟨y, hy⟩ = 0 := by
          ext
          simp
        rw [hz, wdMk_zero]
      rw [heq]
      exact S.neg_mem h1
  rw [eq_top_iff, ← span_wdMk P ι ρ, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact (key x.1 x.2).2
end

