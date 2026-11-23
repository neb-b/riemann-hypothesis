module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Mathlib.RingTheory.AdicCompletion.Completeness

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.TupMap
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mem_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {y : R} (hy : y ∈ maximalIdeal R) :
    f y ∈ maximalIdeal R' := by
  rw [← res_eq_zero_iff O R'] at *
  rw [res_map]
  exact (res_eq_zero_iff O R y).mpr hy

private theorem adic_map {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : AdicCont (maximalIdeal R) a) : AdicCont (maximalIdeal R') fun g => f (a g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap f.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact mem_map f hx
  have key := (ha N).comp (Ideal.quotientMap (maximalIdeal R' ^ N) f.toRingHom hle)
  convert key using 1
  funext g
  simp [Ideal.quotientMap_mk]

theorem UpperTheory.V.Pa.Core.tupMap :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (R R' : Type) [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (t : Tup Λ A R) (f : R →ₐ[O] R'), ∃ t' : Tup Λ A R', t.Maps f.toRingHom t'.D t'.ψ t'.s t'.U t'.y := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A R R' _ _ _ _ _ _ t f
  refine ⟨⟨t.D.map f.toRingHom, ?_, ?_, fun v i => pushCh f.toRingHom (t.ψ v i), ?_, f t.s, mem_map f t.s_mem,
    fun j i => f (t.U j i), ?_, fun j i => f (t.y j i), fun j i => mem_map f (t.y_mem j i)⟩,
    rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro i
    have h := adic_map f (t.cont i)
    convert h using 2 with g
    have := ((UpperTheory.V.CA.d_gmap t.D).2.2.1 f.toRingHom (MonoidAlgebra.single g 1)).2 i
    simpa using this
  · rw [(UpperTheory.V.CA.d_gmap t.D).2.1]
    have : (res O R' : R' →+* ResidueField O).comp f.toRingHom = (res O R : R →+* ResidueField O) := by
      ext x
      exact res_map f x
    rw [this]
    exact t.red
  · intro v i
    have hp := t.psi v i
    refine ⟨?_, ?_, ?_⟩
    · exact adic_map f hp.cont
    · intro g
      simpa [res_map] using hp.red g
    · intro g
      simpa using congrArg f (hp.mu g)
  · intro j i
    have h := mem_map f (t.U_mem j i)
    simpa using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.TupNOfRep
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tupN_lam {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G)
    (i : ℕ) (g : H) : (D.comap φ).lam i (MonoidAlgebra.single g 1) = D.lam i (MonoidAlgebra.single (φ g) 1) := by
  show (-1) ^ i * _root_.AddMonoidAlgebra.coeff (M := ℕ) (D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
      (MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1)))) (n - i) = _
  rw [map_sub]
  simp [GDet.lam, GDet.chi, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

private theorem tupN_ofRep {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg ρ B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (ρ.comp φ) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem tupN_X {R σ : Type} [CommRing R] [IsLocalRing R] (a : σ) :
    (MvPowerSeries.X a : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact not_isUnit_zero

theorem UpperTheory.V.Pa.Core.tupN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → ∀ N, ∃ t : Tup Λ A (A.A N).R, t.D = (A.A N).p.D.comap (πN0 Λ N) ∧ t.ψ = (A.A N).p.ψ ∧ t.s = (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))) ∧ t.U = (A.A N).U ∧ t.y = fun j i => (A.A N).s (MvPowerSeries.X (j, i)) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hAd N
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI hO : IsCO O O :=
    { complete := inferInstance
      isLocalHom := ⟨fun x hx => by simpa using hx⟩
      res_surj := fun x => ⟨x, by simp⟩ }
  haveI hL : IsCO O (abelian₂ O Unit D) := co_mvps O O (Unit ⊕ Fin D)
  haveI hS : IsCO O (Sinf O Unit D T.q n) := co_mvps O (abelian₂ O Unit D) (Fin T.q × Fin n)
  have hC : ∀ x : abelian₂ O Unit D, x ∈ maximalIdeal (abelian₂ O Unit D) →
      (MvPowerSeries.C x : Sinf O Unit D T.q n) ∈ maximalIdeal (Sinf O Unit D T.q n) := by
    intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal x).mp hx
  have hmap : ∀ z : Sinf O Unit D T.q n, z ∈ maximalIdeal (Sinf O Unit D T.q n) →
      (A.A N).s z ∈ maximalIdeal (A.A N).R := by
    intro z hz
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz
  have hcomp := (A.A N).compat
  have key : ∀ (g : Ph0 Λ) (i : Fin n),
      (r.chib i) ((T.h N).p₀ (πN0 Λ N g)) = (r.chib i) (Λ.h.p₀ (πo0 Λ g)) := by
    intro g i
    have hH := hAd.1 ((T.h N).p₀ (πN0 Λ N g) * (Λ.h.p₀ (πo0 Λ g))⁻¹) (Λ.modH N g) i
    rw [map_mul, map_inv, mul_inv_eq_one] at hH
    exact hH
  refine ⟨⟨(A.A N).p.D.comap (πN0 Λ N), ?_, ?_, (A.A N).p.ψ, ?_,
    (A.A N).s (MvPowerSeries.C (MvPowerSeries.X (.inl ()))), ?_, (A.A N).U, (A.A N).U_res,
    fun j i => (A.A N).s (MvPowerSeries.X (j, i)), ?_⟩, rfl, rfl, rfl, rfl, rfl⟩
  · intro i M
    have h2 := ((A.A N).p.cont i M).comp_continuous (Λ.π0_cont N)
    convert h2 using 1
    funext g
    simp only [Function.comp_apply, tupN_lam]
    rfl
  · show ((A.A N).p.D.map (res O (A.A N).R : (A.A N).R →+* ResidueField O)).comap (πN0 Λ N) = _
    rw [(A.A N).p.red]
    simp only [Resid.Dbar, tupN_ofRep]
    congr 1
    ext g i j
    simp only [MonoidHom.comp_apply, diagRep, MonoidHom.coe_mk, OneHom.coe_mk]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      rw [hcomp.1 i, MonoidHom.comp_apply, key]
    · simp [Matrix.diagonal_apply_ne _ hij]
  · intro v i
    have hp := (A.A N).p.psi v i
    exact ⟨hp.cont, fun g => by rw [hp.red g, hcomp.2.1], fun g => by rw [hp.mu g, hcomp.2.2] <;> rfl⟩
  · exact hmap _ (hC _ (tupN_X _))
  · intro j i
    exact hmap _ (tupN_X _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.UlimQuot
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.ulimQuot :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)] (ν : ℕ → ℕ) (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N)))), Antitone I → Tendsto ν F atTop → ∃ Φ : ULim F I M →ₗ[R] ULim F I M', ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) = φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p' := by
  intro R _ F I M M' _ _ _ _ ν φ hI hν
  have hev : ∀ j, ∀ᶠ N in F, I (ν N) ≤ I j := fun j =>
    (tendsto_atTop.1 hν j).mono fun N hN => hI hN
  have he : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R),
      (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) =
        (J • ⊤ : Submodule R X).map (K • ⊤ : Submodule R X).mkQ := by
    intro X _ _ K J
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hlift : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R), K ≤ J → ∀ x : X,
      (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
        (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) → x ∈ (J • ⊤ : Submodule R X) := by
    intro X _ _ K J hKJ x hx
    rw [he] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hd : x - y ∈ (K • ⊤ : Submodule R X) := by
      rw [← Submodule.Quotient.eq]
      exact hyx.symm
    have := Submodule.add_mem _ (Submodule.smul_mono_left hKJ hd) hy
    rwa [sub_add_cancel] at this
  have hmk : ∀ {X : Type} [AddCommGroup X] [Module R X] (K J : Ideal R) (x : X),
      x ∈ (J • ⊤ : Submodule R X) →
        (Submodule.Quotient.mk x : X ⧸ (K • ⊤ : Submodule R X)) ∈
          (J • ⊤ : Submodule R (X ⧸ (K • ⊤ : Submodule R X))) := by
    intro X _ _ K J x hx
    rw [he]
    exact ⟨x, hx, rfl⟩
  have hφ : ∀ N j (z : M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))),
      z ∈ (I j • ⊤ : Submodule R _) → φ N z ∈ (I j • ⊤ : Submodule R _) := by
    intro N j z hz
    have hle : (I j • ⊤ : Submodule R _).map (φ N) ≤ I j • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hle ⟨z, hz, rfl⟩
  let π : (∀ N, M' N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (Submodule.mkQ _).comp (LinearMap.proj N)
  have hπ : Function.Surjective π := fun q =>
    ⟨fun N => (Submodule.mkQ_surjective _ (q N)).choose,
      funext fun N => (Submodule.mkQ_surjective _ (q N)).choose_spec⟩
  have hker : LinearMap.ker π ≤ LinearMap.ker (ULim.mk F I M') := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    rw [ULim.mk_eq_zero]
    intro j
    refine (hev j).mono fun N hN => ?_
    have hpN : p N ∈ (I (ν N) • ⊤ : Submodule R (M' N)) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      exact congrFun hp N
    exact Submodule.smul_mono_left hN hpN
  let φ' : (∀ N, M N) →ₗ[R] ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) :=
    LinearMap.pi fun N => (φ N).comp ((Submodule.mkQ _).comp (LinearMap.proj N))
  let Φ0 : (∀ N, M N) →ₗ[R] ULim F I M' :=
    ((LinearMap.ker π).liftQ (ULim.mk F I M') hker).comp
      ((π.quotKerEquivOfSurjective hπ).symm.toLinearMap.comp φ')
  have hΦ0 : ∀ p p', π p' = φ' p → Φ0 p = ULim.mk F I M' p' := by
    intro p p' h
    simp only [Φ0, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h]
    have hs : (π.quotKerEquivOfSurjective hπ).symm (π p') = Submodule.Quotient.mk p' := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    rw [hs, Submodule.liftQ_apply]
  have hnull : uNull F I M ≤ LinearMap.ker Φ0 := by
    intro p hp
    have hp : ∀ j, ∀ᶠ N in F, p N ∈ (I j • ⊤ : Submodule R (M N)) := hp
    rw [LinearMap.mem_ker]
    obtain ⟨p', hp'⟩ := hπ (φ' p)
    rw [hΦ0 p p' hp', ULim.mk_eq_zero]
    intro j
    refine ((hp j).and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
    apply hlift (I (ν N)) (I j) h2
    have hN : π p' N = φ N (Submodule.Quotient.mk (p N)) := congrFun hp' N
    change π p' N ∈ _
    rw [hN]
    exact hφ N j _ (hmk _ _ _ h1)
  refine ⟨(uNull F I M).liftQ Φ0 hnull, fun p p' h => ?_⟩
  change (uNull F I M).liftQ Φ0 hnull (Submodule.Quotient.mk p) = _
  rw [Submodule.liftQ_apply]
  obtain ⟨q, hq⟩ := hπ (φ' p)
  rw [hΦ0 p q hq, ← sub_eq_zero, ← map_sub, ULim.mk_eq_zero]
  intro j
  refine (h.and (hev j)).mono fun N ⟨h1, h2⟩ => ?_
  apply Submodule.smul_mono_left h2
  rw [← Submodule.Quotient.mk_eq_zero, Pi.sub_apply, Submodule.Quotient.mk_sub, h1]
  have hN : π q N = φ N (Submodule.Quotient.mk (p N)) := congrFun hq N
  exact sub_eq_zero.2 hN
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.YCplMemOf
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem yCpl_mem {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion (I.map (algebraMap R S)) S) :
    x ∈ (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      AdicCompletion.eval (I.map (algebraMap R S)) S n x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), Ideal.smul_top_eq_map,
    ← Ideal.map_pow, Ideal.map_map, Submodule.restrictScalars_mem, ← IsScalarTower.algebraMap_eq]

private theorem yCpl_mem_of {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (s : S) :
    algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) s ∈
      (I ^ n).map (algebraMap R (AdicCompletion (I.map (algebraMap R S)) S)) ↔
      s ∈ (I ^ n).map (algebraMap R S) := by
  rw [yCpl_mem I hI, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, Submodule.mkQ_apply,
    Algebra.algebraMap_self, RingHom.id_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.map_pow]

theorem UpperTheory.V.Pa.Core.yCpl :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R), IsYCpl y f (AdicCompletion ((Ideal.span (Set.range y)).map (algebraMap R (Localization.Away f))) (Localization.Away f)) := by
  intro R σ _ _ _ y f
  set S := Localization.Away f
  set I : Ideal R := Ideal.span (Set.range y)
  set A := AdicCompletion (I.map (algebraMap R S)) S
  have hI : I.FG := Submodule.fg_span (Set.finite_range y)
  have hS : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  have hRA : ∀ r : R, algebraMap R A r = algebraMap S A (algebraMap R S r) := fun r =>
    IsScalarTower.algebraMap_apply R S A r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, ?_, ?_, ?_⟩
  · rw [hRA]
    exact (IsLocalization.Away.algebraMap_isUnit f).map _
  · intro n x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (I.map (algebraMap R S)) S n x)
    obtain ⟨⟨r, _, ⟨k, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers f) s
    simp only at hr
    refine ⟨k, r, ?_⟩
    have hmem : x - algebraMap S A s ∈ (I ^ n).map (algebraMap R A) := by
      rw [yCpl_mem I hI, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of, ← hs,
        Algebra.algebraMap_self, RingHom.id_apply, Submodule.mkQ_apply, sub_self]
    have heq : algebraMap R A f ^ k * x - algebraMap R A r
        = algebraMap R A (f ^ k) * (x - algebraMap S A s) := by
      rw [mul_sub, hRA r, ← hr, map_mul, ← hRA (f ^ k), map_pow]
      ring
    rw [heq]
    exact Ideal.mul_mem_left _ _ hmem
  · intro n r hr
    rw [hRA, yCpl_mem_of I hI] at hr
    obtain ⟨m, ⟨k, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S (I ^ n) r).1 hr
    exact ⟨k, hm⟩
end

