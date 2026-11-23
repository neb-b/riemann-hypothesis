module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivs
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange

theorem h1_baseChange (R R' C : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (m : BC F F')
    (E₀ : R' ⊗[R] C0 F ≃ₗ[R'] C0 F') (E₁ : R' ⊗[R] C1 F ≃ₗ[R'] C1 F')
    (E₂ : R' ⊗[R] C2 F ≃ₗ[R'] C2 F')
    (hE₁ : ∀ c, E₁ (1 ⊗ₜ c) = fun T T' φ ↦ m.α T' (c T T' φ))
    (h01 : ∀ x, E₁ ((d0 F).baseChange R' x) = d0 F' (E₀ x))
    (h12 : ∀ x, E₂ ((d1 F).baseChange R' x) = d1 F' (E₁ x))
    (hex : ∀ x : R' ⊗[R] C1 F, (d1 F).lTensor R' x = 0 →
      ∃ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
        (Z1 F).subtype.lTensor R' t + (d0 F).lTensor R' y = x)
    (hinj : ∀ (t : R' ⊗[R] Z1 F) (y : R' ⊗[R] C0 F),
      (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' y →
        ∃ y' : R' ⊗[R] C0 F, ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)).lTensor R' y' = t) :
    ∃ e : R' ⊗[R] H1 F ≃ₗ[R'] H1 F', ∀ c, e (1 ⊗ₜ c) = m.coef.pull1 c := by
  letI : Module R (H1 F') := Module.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (H1 F') := ⟨fun r s x ↦ by
    change (r • s) • x = algebraMap R R' r • s • x
    rw [Algebra.smul_def, mul_smul]⟩
  let p : H1 F →ₗ[R] H1 F' :=
    { toFun := m.coef.pull1
      map_add' := map_add _
      map_smul' := fun r c ↦ m.coef.pull1.map_smulₛₗ r c }
  let Φ : R' ⊗[R] H1 F →ₗ[R'] H1 F' := p.liftBaseChange R'
  have hΦ : ∀ (r : R') (c : H1 F), Φ (r ⊗ₜ c) = r • m.coef.pull1 c := fun r c ↦
    LinearMap.liftBaseChange_tmul _ _ _ _

  have key : ∀ t : R' ⊗[R] Z1 F, ∃ z' : Z1 F', z'.1 = E₁ ((Z1 F).subtype.lTensor R' t) ∧
      Φ ((H1.mk F).lTensor R' t) = H1.mk F' z' := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul r z =>
      refine ⟨r • m.coef.pullbackOneCocycle z, ?_, ?_⟩
      · have : (r ⊗ₜ[R] z.1 : R' ⊗[R] C1 F) = r • (1 ⊗ₜ[R] z.1) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
        simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
        rw [this, map_smul, hE₁]
        rfl
      · simp only [LinearMap.lTensor_tmul, hΦ, map_smul]
        rfl
    | add a b ha hb =>
      obtain ⟨za, ha1, ha2⟩ := ha
      obtain ⟨zb, hb1, hb2⟩ := hb
      refine ⟨za + zb, ?_, ?_⟩
      · simp only [map_add (f := _), Submodule.coe_add, ha1, hb1]
      · simp only [map_add (f := _), ha2, hb2]
  have bc : ∀ x, (d0 F).lTensor R' x = (d0 F).baseChange R' x := fun x ↦ by
    rw [LinearMap.baseChange_eq_ltensor]
  have hsurj : Function.Surjective Φ := by
    intro c'
    obtain ⟨z', rfl⟩ := H1.mk_surjective F' c'
    have hx : (d1 F).lTensor R' (E₁.symm z'.1) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      apply E₂.injective
      rw [h12, LinearEquiv.apply_symm_apply, map_zero]
      have hz : z'.1 ∈ LinearMap.ker (d1 F') := by
        rw [← commAlgFunctorCocyclesOne_eq_ker]
        exact z'.2
      exact hz
    obtain ⟨t, y, hty⟩ := hex _ hx
    obtain ⟨z'', h1, h2⟩ := key t
    refine ⟨(H1.mk F).lTensor R' t, ?_⟩
    rw [h2, H1.mk_eq_mk]
    refine ⟨-E₀ y, ?_⟩
    have e := congrArg E₁ hty
    rw [LinearEquiv.apply_symm_apply, map_add (f := _), bc, h01, ← h1] at e
    rw [← e, map_neg]
    abel
  have hinjΦ : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective R' (H1.mk_surjective F) w
    obtain ⟨z'', h1, h2⟩ := key t
    rw [h2, H1.mk_eq_zero] at hw
    obtain ⟨g, hg⟩ := hw
    have e : (Z1 F).subtype.lTensor R' t = (d0 F).lTensor R' (E₀.symm g) := by
      apply E₁.injective
      rw [bc, h01, LinearEquiv.apply_symm_apply, hg, h1]
    obtain ⟨y', rfl⟩ := hinj t _ e
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (H1.mk F).comp ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F)) = 0 := by
      ext1 g
      exact H1.mk_eq_zero.2 ⟨g, rfl⟩
    rw [this]
    simp
  refine ⟨LinearEquiv.ofBijective Φ ⟨hinjΦ, hsurj⟩, fun c ↦ ?_⟩
  exact (hΦ 1 c).trans (one_smul R' _)

end GlobalTheory.CompanionTheory.PerfectFirstCohomologyBaseChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesFormula
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GaloisCoh

theorem finite_of_finite_ker {R A B : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [Finite B] (f : A →ₗ[R] B)
    (hk : Finite (LinearMap.ker f)) : Finite A := by
  classical
  let s : B → A := fun b => if h : ∃ a, f a = b then h.choose else 0
  have hs : ∀ a, f (s (f a)) = f a := fun a => by
    have h : ∃ a', f a' = f a := ⟨a, rfl⟩
    simp only [s, dif_pos h]
    exact h.choose_spec
  let φ : A → B × LinearMap.ker f := fun a =>
    (f a, ⟨a - s (f a), by simp [LinearMap.mem_ker, hs]⟩)
  refine Finite.of_injective φ fun a b hab => ?_
  have h1 : f a = f b := congrArg Prod.fst hab
  have h2 : a - s (f a) = b - s (f b) := congrArg (fun x => (x.2 : A)) hab
  rw [h1] at h2
  exact sub_left_injective h2

theorem global_finite_of_poitouTate : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), μ.comp (toGS Ω _) = cycMod F Ω l r → Finite (TDual (ZMod (l ^ r)) M) → LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → ShaDual S Av μ ρ → Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Finite (H0 (twDual μ ρ)) ∧ Finite (H1 (twDual μ ρ)) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ j hμ hT hF hr hA _ hSha
  have hρ' : ContAction (twDual μ ρ) := GlobalTheory.CompanionTheory.GalDual.contAction_twDual F Ω l r M S Av μ ρ hρ hμ
  obtain ⟨-, hS1, hS2⟩ := selmer_sha_eq_comap_ker F Ω l r M S Av μ ρ hρ
  obtain ⟨-, hT1, -⟩ := selmer_sha_eq_comap_ker F Ω l r (TDual (ZMod (l ^ r)) M) S Av μ
    (twDual μ ρ) hρ'
  have hloc := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r M S Av μ ρ hρ hF hr hA
  have hlocT := GlobalTheory.CompanionTheory.Galois.PlacesOfS.localFinite_at_places F Ω l r (TDual (ZMod (l ^ r)) M)
    S Av μ (twDual μ ρ) hρ' hF hr hA
  have p1 : Finite (∀ v : S, H1 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.1
    inferInstance
  have p2 : Finite (∀ v : S, H2 (ρ.comp (locFam S Av v))) :=
    haveI := fun v => (hloc v).2.2
    inferInstance
  have pT : Finite (∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v))) :=
    haveI := fun v => (hlocT v).2.1
    inferInstance
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av ρ) ?_
    rw [← hS1]
    exact hSha.2.1
  · refine finite_of_finite_ker (loc2 S Av ρ) ?_
    rw [← hS2]
    exact hSha.1.2.1
  · exact inferInstance
  · refine finite_of_finite_ker (loc1 S Av (twDual μ ρ)) ?_
    rw [← hT1]
    exact hSha.1.1

end GlobalTheory.CompanionTheory.GaloisCoh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTop
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GeoNetop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem irrelevant_le_spanX (K : Type) [Field K] (N : ℕ) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)) := by
  intro x hx
  have h0 := (HomogeneousIdeal.mem_irrelevant_iff _ _).1 hx
  rw [GradedRing.proj_apply] at h0
  have h1 : MvPolynomial.homogeneousComponent 0 x = 0 := by
    rw [← MvPolynomial.decomposition.decompose'_apply]
    exact h0
  rw [MvPolynomial.homogeneousComponent_zero, MvPolynomial.C_eq_zero] at h1
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (MvPolynomial.mem_support_iff.1 hm) h1
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hm0
  exact ⟨a, Set.mem_univ _, ha⟩

theorem exists_chart {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (x : X) :
    ∃ j : Fin (N + 1), x ∈ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j) := by
  have h := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) MvPolynomial.X
    (irrelevant_le_spanX K N)
  have hx : i x ∈ ⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X j) := by
    rw [h]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  exact ⟨j, hj⟩

theorem mk_C_mul_inv {K : Type} [Field K] {N : ℕ} (j : Fin (N + 1)) (c : K) (hc : c ≠ 0)
    (ha : MvPolynomial.C c ∈ grK K N (0 • 1)) (hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1)) :
    HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c) ha *
      HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) 0 (MvPolynomial.C c⁻¹) hb = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, ← map_mul, mul_inv_cancel₀ hc]

theorem constantCoeff_gen {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N) (hX : Nonempty X)
    {f : MvPolynomial (Fin (N + 1)) K} (d : ℕ) (hf : f ∈ grK K N (d • 1))
    (h0 : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) d f hf) = 0) :
    MvPolynomial.constantCoeff f = 0 := by
  have hc := MvPolynomial.homogeneousComponent_of_mem (m := 0) hf
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  rw [MvPolynomial.constantCoeff_eq]
  by_cases hd : 0 = d • 1
  · rw [if_pos hd] at hc
    have hd0 : d = 0 := by simpa using hd.symm
    subst hd0
    obtain ⟨c, rfl⟩ : ∃ c, f = MvPolynomial.C c := ⟨_, hc.symm⟩
    rw [MvPolynomial.coeff_zero_C]
    by_contra hne
    obtain ⟨x⟩ := hX
    obtain ⟨j, hj⟩ := exists_chart i x
    haveI : Nonempty (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) := ⟨⟨x, hj⟩⟩
    haveI := Scheme.component_nontrivial X (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j))
    have hb : MvPolynomial.C c⁻¹ ∈ grK K N (0 • 1) := by
      simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c⁻¹
    have e := congrArg (evV i (MvPolynomial.X j) _ le_rfl) (mk_C_mul_inv j c hne hf hb)
    rw [map_mul, map_one, h0 j, zero_mul] at e
    exact zero_ne_one e
  · rw [if_neg hd, MvPolynomial.C_eq_zero] at hc
    exact hc

theorem homIdeal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N),
    Nonempty X → homIdeal i ≠ ⊤ := by
  intro K _ X N i hX htop
  have hle : homIdeal i ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) := by
    refine Ideal.span_le.2 ?_
    rintro f ⟨d, hf, h0⟩
    exact (RingHom.mem_ker).2 (constantCoeff_gen i hX d hf h0)
  have h1 : (1 : MvPolynomial (Fin (N + 1)) K) ∈ RingHom.ker (MvPolynomial.constantCoeff (σ := Fin (N + 1)) (R := K)) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1
end GlobalTheory.CompanionTheory.GeoNetop
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpression
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Geo


open MvPolynomial in
theorem exists_monic_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (y : Fin m → MvPolynomial σ K)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (a : MvPolynomial σ K) :
    ∃ (s : ℕ) (C : ℕ → MvPolynomial (Fin m) K), 0 < s ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (C l) * a ^ l ∈ I := by
  by_cases htop : I = ⊤
  · exact ⟨1, 0, one_pos, by simp [htop]⟩
  haveI : Nontrivial (MvPolynomial σ K ⧸ I) := Ideal.Quotient.nontrivial_iff.2 htop
  set B := Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)) with hB
  haveI : Algebra.IsIntegral B (MvPolynomial σ K ⧸ I) := Algebra.IsIntegral.of_finite _ _
  obtain ⟨p, hp, hroot⟩ := Algebra.IsIntegral.isIntegral (R := B) (Ideal.Quotient.mk I a)
  have hq : (p * Polynomial.X).Monic := hp.mul Polynomial.monic_X
  have hroot' : Polynomial.eval₂ (algebraMap B (MvPolynomial σ K ⧸ I)) (Ideal.Quotient.mk I a)
      (p * Polynomial.X) = 0 := by
    rw [Polynomial.eval₂_mul, hroot, zero_mul]
  have hdeg : 0 < (p * Polynomial.X).natDegree := by
    rw [hp.natDegree_mul Polynomial.monic_X, Polynomial.natDegree_X]
    omega
  generalize p * Polynomial.X = q at hq hroot' hdeg
  have hlift : ∀ l, ∃ c : MvPolynomial (Fin m) K,
      Ideal.Quotient.mk I (aeval y c) = ((q.coeff l : B) : MvPolynomial σ K ⧸ I) := by
    intro l
    have hmem : ((q.coeff l : B) : MvPolynomial σ K ⧸ I) ∈
        (aeval (fun k => Ideal.Quotient.mk I (y k)) :
          MvPolynomial (Fin m) K →ₐ[K] MvPolynomial σ K ⧸ I).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff l).2
    obtain ⟨c, hc⟩ := hmem
    refine ⟨c, ?_⟩
    rw [← hc]
    have := MvPolynomial.comp_aeval_apply (R := K) (B := MvPolynomial σ K ⧸ I) y
      (Ideal.Quotient.mkₐ K I) c
    simpa using this
  choose C hC using hlift
  refine ⟨q.natDegree, C, hdeg, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hroot', Polynomial.eval₂_eq_sum_range,
    Finset.sum_range_succ, map_add, map_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, hC, map_pow]
    rfl
  · simp [hq.coeff_natDegree]


open MvPolynomial in
theorem homogeneousComponent_aeval_mul {K σ : Type} [Field K] {m e : ℕ} (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (C : MvPolynomial (Fin m) K) (r t : ℕ) (b : MvPolynomial σ K) (hb : b.IsHomogeneous t) :
    homogeneousComponent (e * r + t) (aeval y C * b) = aeval y (homogeneousComponent r C) * b := by
  have key : ∀ r', homogeneousComponent (e * r + t) (aeval y (homogeneousComponent r' C) * b) =
      if r' = r then aeval y (homogeneousComponent r C) * b else 0 := by
    intro r'
    have h : (aeval y (homogeneousComponent r' C) * b).IsHomogeneous (e * r' + t) :=
      ((homogeneousComponent_isHomogeneous r' C).aeval y hy).mul hb
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    by_cases hr : r' = r
    · subst hr
      simp
    · have hne : e * r' + t ≠ e * r + t := fun h' =>
        hr (Nat.eq_of_mul_eq_mul_left he (Nat.add_right_cancel h'))
      rw [if_neg hne.symm, if_neg hr]
  conv_lhs => rw [← sum_homogeneousComponent C]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, map_sum]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hmem)]
    simp


open MvPolynomial in
theorem exists_hom_relation {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ n : ℕ, homogeneousComponent n f ∈ I) (e : ℕ) (he : 0 < e)
    (y : Fin m → MvPolynomial σ K) (hy : ∀ k, (y k).IsHomogeneous e)
    (hfin : Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k)))
      (MvPolynomial σ K ⧸ I))
    (w : ℕ) (a : MvPolynomial σ K) (ha : a.IsHomogeneous (e * w)) :
    ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧
      a ^ s + ∑ l ∈ Finset.range s, aeval y (c l) * a ^ l ∈ I := by
  obtain ⟨s, C, hs, hmem⟩ := exists_monic_relation I y hfin a
  refine ⟨s, fun l => homogeneousComponent ((s - l) * w) (C l), hs,
    fun l => homogeneousComponent_isHomogeneous _ _, ?_⟩
  have hcomp := hI _ hmem (e * w * s)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum] at hcomp
  convert hcomp using 2
  · have h := ha.pow s
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h)]
    simp
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l ≤ s := (Finset.mem_range.1 hl).le
    have hdeg : e * w * s = e * ((s - l) * w) + e * w * l := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl'
      simp only [Nat.add_sub_cancel_left]
      ring
    rw [hdeg, homogeneousComponent_aeval_mul he y hy (C l) _ _ _ (ha.pow l)]

end GlobalTheory.CompanionTheory.Geo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSquareLeKernelOfSquareZeroMap
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.CotKer

theorem mul_eq_zero_top {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (a b : Γ(Sp Q, ⊤))
    (ha : (spMap q).appTop.hom a = 0) (hb : (spMap q).appTop.hom b = 0) : a * b = 0 := by
  have key : ∀ x : Γ(Sp Q, ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap q).appTop.hom x) =
      q ((Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom x) := fun x =>
    congrArg (fun f => CommRingCat.Hom.hom f x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom q))
  have hφ : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of Q)).hom.hom := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom hxy
    simpa using h
  apply hφ
  rw [map_mul, map_zero]
  apply hq
  · rw [← key, ha, map_zero]
  · rw [← key, hb, map_zero]

theorem ker_sq_eq_bot {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) : (spMap q).ker ^ 2 = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
    Scheme.Hom.ker_apply, pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  exact (Submodule.mem_bot _).mpr (mul_eq_zero_top q hq a b ha hb)

theorem mul_eq_zero_affine {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (W : (Sp Q).affineOpens) (a b : Γ(Sp Q, W.1))
    (ha : ((spMap q).app W.1).hom a = 0) (hb : ((spMap q).app W.1).hom b = 0) : a * b = 0 := by
  have h := congrArg (fun I => Scheme.IdealSheafData.ideal I W) (ker_sq_eq_bot q hq)
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply, Scheme.Hom.ker_apply] at h
  have hab : a * b ∈ (RingHom.ker ((spMap q).app W.1).hom) ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  rw [h] at hab
  exact (Submodule.mem_bot _).mp hab

theorem mul_eq_zero_open {Q B : Type} [CommRing Q] [CommRing B] (q : Q →+* B)
    (hq : ∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) (O : (Sp Q).Opens) (a b : Γ(Sp Q, O))
    (ha : ((spMap q).app O).hom a = 0) (hb : ((spMap q).app O).hom b = 0) : a * b = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (Sp Q).sheaf
    (fun W : {W : (Sp Q).affineOpens // W.1 ≤ O} => W.1.1) O (fun W => homOfLE W.2) ?_ (a * b) 0 ?_
  · intro x hx
    obtain ⟨U', hU', hxU', hle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens (Sp Q))) hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U', hU'⟩, hle⟩, hxU'⟩
  · intro W
    have hres : ∀ s : Γ(Sp Q, O), ((spMap q).app O).hom s = 0 →
        ((spMap q).app W.1.1).hom (((Sp Q).presheaf.map (homOfLE W.2).op).hom s) = 0 := by
      intro s hs
      have h := congrArg (fun f => CommRingCat.Hom.hom f s) ((spMap q).naturality (homOfLE W.2).op)
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, hs, map_zero] at h
      exact h
    show ((Sp Q).presheaf.map (homOfLE W.2).op).hom (a * b) =
      ((Sp Q).presheaf.map (homOfLE W.2).op).hom 0
    rw [map_zero, map_mul]
    exact mul_eq_zero_affine q hq W.1 _ _ (hres a ha) (hres b hb)

theorem comp_comp_apply_eq_zero {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D) (a : A)
    (ha : f.hom a = 0) : ((f ≫ g) ≫ h).hom a = 0 := by
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_zero]

theorem ker_sq_le_ker : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  intro R Q B _ _ _ U e _ q ρ y _ hq hcomm
  show _ ≤ Scheme.IdealSheafData.ofIdeals (fun V => RingHom.ker (y.app V).hom)
  rw [Scheme.IdealSheafData.le_ofIdeals_iff]
  intro V
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply e V, pow_two, Ideal.mul_le]
  intro a ha b hb
  rw [RingHom.mem_ker] at ha hb ⊢
  have key : ∀ s, (e.app V).hom s = 0 → ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = 0 := by
    intro s hs
    have h1 : ((spMap q).app (y ⁻¹ᵁ V)).hom ((y.app V).hom s) = ((spMap q ≫ y).app V).hom s := by
      rw [Scheme.Hom.comp_app]
      rfl
    rw [h1, Scheme.Hom.congr_app hcomm V, Scheme.Hom.comp_app]
    exact comp_comp_apply_eq_zero _ _ _ s hs
  rw [map_mul]
  exact mul_eq_zero_open q hq (y ⁻¹ᵁ V) _ _ (key a ha) (key b hb)

end GlobalTheory.CompanionTheory.CotKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmorFrFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ChartFrames

theorem smor_Fr_frame : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) {V V' : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d) (c' : Chart γ' p q κ' V' d) (hc : c.Good) (hc' : c'.Good)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T)) (hQ : ∀ T, Q T → InU V T) (hD : Q c.D)
    (hQ' : ∀ T, Q' T → InU V' T) (hD' : Q' c'.D) (e : c.D ⟶ (m.mor p).functor.obj c'.D),
    (∀ i, e.φ (c.t i) = c'.t i) →
      SMor.Fr (m.smor Q Q' h) (c.frame hc Q hQ hD) (c'.frame hc' Q' hQ' hD') (ObjectProperty.homMk e) := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m V V' d c c' hc hc' Q Q' h hQ hD hQ' hD' e he i T s s'
  change (s'.hom.φ (e.φ (c.t i)) - s.hom.φ (e.φ (c.t i)) : T.obj.B) = s'.hom.φ (c'.t i) - s.hom.φ (c'.t i)
  rw [he]

end GlobalTheory.CompanionTheory.ChartFrames
end

