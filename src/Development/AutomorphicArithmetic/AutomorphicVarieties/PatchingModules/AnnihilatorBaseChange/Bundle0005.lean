module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.CharpolyElementEqAevalGroupElement
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem ch_ker {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (x : E) :
    Polynomial.aeval x (D.chi x) ∈ D.ker := by
  apply UpperTheory.V.CA.d_ch_ker D
  have h1 := (UpperTheory.V.CA.d_chS D A).1 ((1 : A) ⊗ₜ[A] x)
  have hchi : D.chiS A ((1 : A) ⊗ₜ[A] x) = D.chi x := by
    unfold Det.chiS Det.chi
    simp [Algebra.TensorProduct.map_tmul]
  rw [hchi] at h1
  have he : Polynomial.aeval x (D.chi x) =
      Algebra.TensorProduct.lid A E (Polynomial.aeval ((1 : A) ⊗ₜ[A] x) (D.chi x)) := by
    rw [← Polynomial.aeval_algHom_apply]
    simp
  rw [he]
  have key : ∀ w ∈ Submodule.span A ((fun z : E => (1 : A) ⊗ₜ[A] z) '' (D.CH : Set E)),
      Algebra.TensorProduct.lid A E w ∈ D.CH := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      simpa using hc
    | zero => simpa using TwoSidedIdeal.zero_mem _
    | add a b _ _ ha hb =>
      rw [map_add (f := _)]
      exact TwoSidedIdeal.add_mem _ ha hb
    | smul a z _ hz =>
      rw [map_smul, Algebra.smul_def]
      exact TwoSidedIdeal.mul_mem_left _ _ _ hz
  exact key _ h1

private theorem tr_ker {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n)
    {y : MonoidAlgebra A G} (hy : y ∈ D.toDet.ker) (h : MonoidAlgebra A G) : D.tr (h * y) = 0 := by
  have hk := (UpperTheory.V.CA.d_ker D.toDet y).2.2 hy h 1 le_rfl hn
  have htr : D.toDet.tr (h * y) = D.toDet.lam 1 (h * y) := by
    unfold Det.tr Det.lam
    rfl
  rw [← (UpperTheory.V.CA.d_toDet D (h * y)).2.2.1, htr, hk]

private theorem charpoly_element_eq_aeval_group_element {n : ℕ} {A G : Type} [CommRing A] [Group G] (g : G) (U : Fin n → A) :
    q1El g U = Polynomial.aeval (MonoidAlgebra.single g (1 : A)) (∏ i, (Polynomial.X - Polynomial.C (U i))) := by
  unfold q1El
  rw [← Fin.prod_ofFn, map_list_prod, List.map_ofFn]
  congr 1
  congr 1
  funext i
  simp [MonoidAlgebra.coe_algebraMap]

private noncomputable def push {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) : MonoidAlgebra R H →+* MonoidAlgebra S G :=
  (MonoidAlgebra.mapDomainRingHom S φ).comp (MonoidAlgebra.mapRingHom H f)

private theorem push_single {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G] (f : R →+* S)
    (φ : H →* G) (g : H) (a : R) : push f φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (φ g) (f a) := by
  simp [push, MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom]

private theorem gDet_lam_map_comap_eq_lam_mapDomainRingHom {n : ℕ} {B S H G : Type} [CommRing B] [CommRing S] [Group H] [Group G]
    (D : GDet n B G) (a : B →+* S) (φ : H →* G) (i : ℕ) (z : MonoidAlgebra S H) :
    ((D.comap φ).map a).lam i z = (D.map a).lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  have key : MonoidAlgebra.mapDomainRingHom (Polynomial S) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C z) =
      MonoidAlgebra.single 1 Polynomial.X -
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    rw [map_sub]
    congr 1
    · simp [MonoidAlgebra.mapDomainRingHom]
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | single h s =>
        simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapRingHom, MonoidAlgebra.mapDomain_single]
  unfold GDet.lam GDet.map GDet.comap GDet.chi
  dsimp only
  rw [MonoidHom.comp_apply]
  erw [key]

private theorem lam_push {n : ℕ} {R B S H G : Type} [CommRing R] [CommRing B] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n B G} {f : R →+* S} {a : B →+* S} {φ : H →* G}
    (h : E.map f = (D.comap φ).map a) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = (D.map a).lam i (push f φ y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h, gDet_lam_map_comap_eq_lam_mapDomainRingHom]
  rfl

theorem UpperTheory.V.Pa.Core.piKer :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ii W ≤ RingHom.ker m.π := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn hAd
  obtain ⟨hD, hψ, hs, hU, hy⟩ := m.π_maps
  have hL : ∀ i y, m.π.toRingHom (W.t.D.lam i y) =
      (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun i y => lam_push hD i y
  have hT : ∀ y, m.π (W.t.D.tr y) =
      (u.D.map (algebraMap B (Spo A))).tr (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) :=
    fun y => hL 1 y
  have hz : ∀ h y, y ∈ (u.D.map (algebraMap B (Spo A))).toDet.ker →
      (u.D.map (algebraMap B (Spo A))).tr (h * y) = 0 :=
    fun h y hy => tr_ker _ hn hy h
  have hz0 : (u.D.map (algebraMap B (Spo A))).tr 0 = 0 := by
    simpa using hz 1 0 (TwoSidedIdeal.zero_mem _)
  have hmapTr : ∀ x, (u.D.map (algebraMap B (Spo A))).tr
      (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) x) = algebraMap B (Spo A) (u.D.tr x) :=
    fun x => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) x).2 1
  have hc : (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))).comp
      (algebraMap W.R (MonoidAlgebra W.R (Ph0 Λ))) =
      (algebraMap (Spo A) (MonoidAlgebra (Spo A) G0.frame.G₀)).comp m.π.toRingHom := by
    ext c
    simp [push_single, MonoidAlgebra.coe_algebraMap]
  rw [ii, Ideal.span_le]
  intro x hx
  rw [SetLike.mem_coe, RingHom.mem_ker]
  induction hx
  next h k hk =>
    rw [hT, map_mul, map_sub, map_one, push_single, push_single]
    simp [hk, ← MonoidAlgebra.one_def, hz0]
  next i g g' hg =>
    have hL' : ∀ i y, m.π (W.t.D.lam i y) =
        (u.D.map (algebraMap B (Spo A))).lam i (push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) y) := hL
    have hlam : ∀ z, (u.D.map (algebraMap B (Spo A))).lam i
        (MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A)) z) = algebraMap B (Spo A) (u.D.lam i z) :=
      fun z => ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A)) z).2 i
    have heps : ∀ (x : Λ.G.G₀) (k : ℤ), m.π (((Λ.G.frame.eps O W.R x ^ k : W.Rˣ)) : W.R) =
        (((G0.frame.eps O (Spo A) (Λ.h.p₀ x) ^ k : (Spo A)ˣ)) : Spo A) := by
      intro x k
      rw [Λ.h.eps_p₀]
      have hu : Units.map (m.π : W.R →* Spo A) (Λ.G.frame.eps O W.R x) = Λ.G.frame.eps O (Spo A) x := by
        ext
        simp [GFrame.eps, pushCh]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (m.π : W.R →* Spo A)) (Λ.G.frame.eps O W.R x) k)
    have hepsB : ∀ (y : G0.G₀) (k : ℤ), algebraMap B (Spo A) (((G0.frame.eps O B y ^ k : Bˣ)) : B) =
        (((G0.frame.eps O (Spo A) y ^ k : (Spo A)ˣ)) : Spo A) := by
      intro y k
      have hu : Units.map (algebraMap B (Spo A) : B →* Spo A) (G0.frame.eps O B y) = G0.frame.eps O (Spo A) y := by
        ext
        simp [GFrame.eps, pushCh, ← IsScalarTower.algebraMap_apply]
      rw [← hu]
      exact congrArg Units.val (map_zpow (Units.map (algebraMap B (Spo A) : B →* Spo A)) (G0.frame.eps O B y) k)
    have hconj : πo0 Λ g' = Λ.G.frame.conj (πo0 Λ g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc hψ hL' hlam heps hepsB
      apply Subtype.ext
      show Λ.πo (g' : Λ.Ph) = Λ.G.c * Λ.πo (g : Λ.Ph) * Λ.G.c⁻¹
      rw [hg, map_mul, map_mul, map_inv, Λ.ct_o]
    have h1 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single g'⁻¹ (((Λ.G.frame.eps O W.R (πo0 Λ g) ^ (1 - (n : ℤ)) : W.Rˣ)) : W.R)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (G0.frame.star O B n (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1)) := by
      unfold GFrame.star GFrame.starOp
      rw [MonoidAlgebra.lift_single, one_smul]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op]
      rw [MonoidAlgebra.mapRingHom_single, push_single]
      congr 1
      · rw [map_inv, MonoidHom.comp_apply, hconj, Λ.h.p₀_conj]
      · rw [hepsB]
        exact heps _ _
    have h2 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ g)) 1) := by
      rw [push_single, MonoidAlgebra.mapRingHom_single, map_one, map_one, MonoidHom.comp_apply]
    rw [map_sub, hL', hL', h1, h2, hlam, hlam, u.P, sub_self]
  next v g ga h hga =>
    have hpt : ∀ i, m.π.toRingHom ((W.t.ψ v i (g i) : W.R)) =
        algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := by
      intro i
      have := congrArg (fun χ : L.Gv v →* (Spo A)ˣ => ((χ (g i) : (Spo A)ˣ) : Spo A)) (hψ v i)
      simpa [pushCh] using this
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) 1 -
          MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.R))).prod) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * G0.frame.oEl v (u.ψ v) g) := by
      clear hL hT hz hz0 hmapTr hs hD hAd hy hU hc
      unfold GFrame.oEl
      rw [map_mul, map_mul, push_single, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      congr 1
      · rw [MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, map_one, map_one]
      · congr 2
        funext i
        have hpt' : m.π ((W.t.ψ v i (g i) : W.R)) = algebraMap B (Spo A) ((u.ψ v i (g i) : B)) := hpt i
        rw [Function.comp_apply, Function.comp_apply, map_sub, map_sub, push_single, push_single, MonoidAlgebra.mapRingHom_single,
          MonoidAlgebra.mapRingHom_single, MonoidHom.comp_apply, hga, Λ.h.p₀_φ, map_one, map_one]
        exact congrArg (fun c => MonoidAlgebra.single _ 1 - MonoidAlgebra.single 1 c) hpt'
    rw [hT, hp, hmapTr, u.Ord, map_zero]
  next w g ga h hg hga =>
    have hp : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) =
        MonoidAlgebra.mapRingHom _ (algebraMap B (Spo A))
          (MonoidAlgebra.single (Λ.h.p₀ (πo0 Λ h)) 1 * (MonoidAlgebra.single (G0.φu w g) 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, push_single, MonoidAlgebra.mapRingHom_single,
        MonoidHom.comp_apply, hga, Λ.h.p₀_φu]
    have hmem : G0.φu w g ∈ r.Ip w := by
      rw [hAd.2 w]
      exact Subgroup.mem_map_of_mem _ hg
    rw [hT, hp, hmapTr, u.I w _ hmem, map_zero]
  next j ph h hph =>
    have hchi : (u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1) =
        Polynomial.map (algebraMap B (Spo A)) (u.D.chi (MonoidAlgebra.single (T.sg j) 1)) := by
      have := ((UpperTheory.V.CA.d_gmap u.D).2.2.1 (algebraMap B (Spo A))
        (MonoidAlgebra.single (T.sg j) 1)).1
      simpa [MonoidAlgebra.mapRingHom] using this
    have hq : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ)) (q1El ph (W.t.U j)) =
        Polynomial.aeval (MonoidAlgebra.single (T.sg j) (1 : Spo A))
          ((u.D.map (algebraMap B (Spo A))).chi (MonoidAlgebra.single (T.sg j) 1)) := by
      clear hL hT hz hz0 hmapTr hψ hs hD hAd hy
      rw [charpoly_element_eq_aeval_group_element, Polynomial.aeval_def, Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map,
        ← Polynomial.aeval_def, push_single, MonoidHom.comp_apply, hph, Λ.p_ph, map_one, hchi,
        Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [← (spRoots B T.q n _ _ j).1]
      congr 2
      funext i
      exact congrArg (fun c => Polynomial.X - Polynomial.C c) (hU j i)
    rw [hT, map_mul, push_single, hq]
    apply hz
    have := ch_ker (u.D.map (algebraMap B (Spo A))).toDet (MonoidAlgebra.single (T.sg j) 1)
    rwa [(UpperTheory.V.CA.d_toDet _ _).1] at this
  next j i ph ta h hph hta =>
    have h0 : push m.π.toRingHom (Λ.h.p₀.comp (πo0 Λ))
        (MonoidAlgebra.single ta 1 - 1 - MonoidAlgebra.single 1 (W.t.y j i)) = 0 := by
      rw [map_sub, map_sub, map_one, push_single, push_single, MonoidHom.comp_apply, hta, Λ.p_ta,
        map_one, hy, MonoidAlgebra.single_zero, sub_zero, ← MonoidAlgebra.one_def, sub_self]
    rw [hT]
    unfold q2El
    rw [map_mul, map_mul, h0, mul_zero, mul_zero, hz0]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsPowMaximalIdealSmulFiniteEqZero
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem exists_pow_maximalIdeal_smul_finite_eq_zero (R Q : Type) [CommRing R] [IsLocalRing R] [AddCommGroup Q] [Module R Q] [Finite Q] :
    ∃ c : ℕ, ∀ a ∈ maximalIdeal R ^ c, ∀ z : Q, a • z = 0 :=
  _root_.UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero R Q

private theorem finite_quotient_of_power_maximal_ideal_le (Λ R X : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing Λ]
    [Finite (ResidueField Λ)] [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X] (t : Λ →+* R)
    (ht : ∀ (a : Λ) (x : X), a • x = t a • x) (j : ℕ) (K : Ideal R) (hK : (maximalIdeal Λ).map t ^ j ≤ K) :
    Finite (X ⧸ (K • ⊤ : Submodule R X)) := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X), x ∈ (K • ⊤ : Submodule R X) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      rw [ht]
      refine Submodule.smul_mem_smul (hK ?_) Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  let g : (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) → (X ⧸ (K • ⊤ : Submodule R X)) := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  refine Finite.of_surjective g fun z => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem UpperTheory.V.Pa.Core.finite_quotient_of_ultrafilter_limit_module :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [Finite (ResidueField Λ)] [IsLocalRing R] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∀ k j : ℕ, ∃ c : ℕ, ∀ᶠ N in (U : Filter ℕ), ∀ a ∈ maximalIdeal R ^ c, ∀ x : M N, (f ^ k * a) • x ∈ ((Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) • ⊤ : Submodule R (M N)) := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hC _ h k j
  have hK := kjMap Λ R σ s 1 j
  haveI : Finite (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) :=
    finite_quotient_of_power_maximal_ideal_le Λ R X (s.comp MvPowerSeries.C) hC j _ (hK ▸ le_sup_right)
  obtain ⟨c, hc⟩ := exists_pow_maximalIdeal_smul_finite_eq_zero R (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))
  refine ⟨c * k, (h j).mono ?_⟩
  rintro N ⟨φ, ψ, hφψ, -⟩ a ha x
  have h1 : ((Ideal.span {f} * maximalIdeal R ^ c) • ⊤ : Submodule R (M N)) ≤ (kjIdeal Λ σ 1 j).map s • ⊤ := by
    refine Submodule.smul_le.2 ?_
    intro r hr y _
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, mul_comm, mul_smul, ← hφψ, ← map_smul,
      hc b hb, map_zero]
  rw [hK, pow_one, sup_comm] at h1
  have h2 := (smul_pow_le_of_step R (maximalIdeal R ^ c) _ _ f).2 (M N) h1 k
  rw [sup_comm]
  refine h2 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_) Submodule.mem_top)
  rwa [← pow_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsUltraLimitPairOfEventualQuotientMaps
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem const_bij {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (U : Ultrafilter ℕ)
    (m : Ideal R) (I : ℕ → Ideal R) (hc : IsAdicComplete m X)
    (hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)))
    (hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤) :
    Function.Bijective
      (ULim.mk (U : Filter ℕ) I (fun _ => X) ∘ₗ LinearMap.pi fun _ : ℕ => (LinearMap.id : X →ₗ[R] X)) := by
  have hb := ULim.const_bijective R ℕ U m X hc hf
  have key : ∀ p q : ℕ → X, ULim.mk (U : Filter ℕ) I (fun _ => X) p = ULim.mk (U : Filter ℕ) I (fun _ => X) q ↔
      ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) p =
        ULim.mk (U : Filter ℕ) (fun j => m ^ j) (fun _ => X) q := by
    intro p q
    rw [← sub_eq_zero, ← map_sub, ULim.mk_eq_zero, ← sub_eq_zero (a := ULim.mk _ _ _ p), ← map_sub,
      ULim.mk_eq_zero]
    simp only [hI]
  refine ⟨fun a b hab => hb.1 ((key (fun _ => a) (fun _ => b)).1 hab), fun x => ?_⟩
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ x
  obtain ⟨z, hz⟩ := hb.2 (ULim.mk _ _ _ p)
  exact ⟨z, (key (fun _ => z) p).2 hz⟩

private theorem comp_smul {R : Type} [CommRing R] (F : Filter ℕ) (I : ℕ → Ideal R) (M M' : ℕ → Type)
    [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] [∀ N, AddCommGroup (M' N)] [∀ N, Module R (M' N)]
    (ν : ℕ → ℕ) (hν : Tendsto ν F atTop) (hI : Antitone I) (f : R)
    (φ : ∀ N, (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))))
    (ψ : ∀ N, (M' N ⧸ (I (ν N) • ⊤ : Submodule R (M' N))) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))))
    (h : ∀ᶠ N in F, ∀ z, ψ N (φ N z) = f • z)
    (Φ : ULim F I M →ₗ[R] ULim F I M') (Ψ : ULim F I M' →ₗ[R] ULim F I M)
    (hΦ : ∀ (p : ∀ N, M N) (p' : ∀ N, M' N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      φ N (Submodule.Quotient.mk (p N))) → Φ (ULim.mk F I M p) = ULim.mk F I M' p')
    (hΨ : ∀ (p : ∀ N, M' N) (p' : ∀ N, M N), (∀ᶠ N in F, Submodule.Quotient.mk (p' N) =
      ψ N (Submodule.Quotient.mk (p N))) → Ψ (ULim.mk F I M' p) = ULim.mk F I M p') (z : ULim F I M) :
    Ψ (Φ z) = f • z := by
  obtain ⟨p, rfl⟩ := ULim.mk_surjective _ _ _ z
  choose q hq using fun N => Submodule.Quotient.mk_surjective _ (φ N (Submodule.Quotient.mk (p N)))
  rw [hΦ p q (Eventually.of_forall hq), ← map_smul]
  refine hΨ q (f • p) (h.mono fun N hN => ?_)
  rw [hq, hN]
  rfl

theorem UpperTheory.V.Pa.Core.exists_ultraLimit_pair_of_eventual_quotient_maps :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (U : Filter ℕ) ≤ atTop → (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∃ (Φ : X →ₗ[R] ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M) (Ψ : ULim (U : Filter ℕ) (fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) M →ₗ[R] X), (∀ z, Φ (Ψ z) = f • z) ∧ ∀ z, Ψ (Φ z) = f • z := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hU hs hy h
  classical
  letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
  haveI : IsScalarTower Λ R X := IsScalarTower.of_algebraMap_smul fun a x => (hs a x).symm
  set m : Ideal R := (maximalIdeal Λ).map (s.comp MvPowerSeries.C) with hm
  set I : ℕ → Ideal R := fun j => Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ⊔ m ^ j with hIdef
  have hkj : ∀ j, (kjIdeal Λ σ 1 j).map s = I j := fun j => by rw [kjMap, pow_one]
  have h' : ∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ (I j • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I j • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I j • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I j • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro j
    rw [← hkj j]
    exact h j
  obtain ⟨ν, hν, hP⟩ := exists_diag _ hU _ h'
  have hanti : Antitone I := fun a b hab => sup_le_sup_left (Ideal.pow_le_pow_right hab) _
  have hex : ∀ N, ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z := by
    intro N
    by_cases hN : ∃ (φ : (X ⧸ (I (ν N) • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ (I (ν N) • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ (I (ν N) • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z
    · obtain ⟨φ, ψ, hh⟩ := hN
      exact ⟨φ, ψ, fun _ => hh⟩
    · exact ⟨0, 0, fun hh => absurd hh hN⟩
  choose φ ψ hφψ using hex
  have hgood := hP.mono fun N hN => hφψ N (hN _ le_rfl)
  obtain ⟨Φ, hΦ⟩ := ulimQuot R U I (fun _ => X) M ν φ hanti hν
  obtain ⟨Ψ, hΨ⟩ := ulimQuot R U I M (fun _ => X) ν ψ hanti hν
  have h1 := comp_smul U I (fun _ => X) M ν hν hanti f φ ψ (hgood.mono fun _ hN => hN.2) Φ Ψ hΦ hΨ
  have h2 := comp_smul U I M (fun _ => X) ν hν hanti f ψ φ (hgood.mono fun _ hN => hN.1) Ψ Φ hΨ hΦ
  have hc : IsAdicComplete m X :=
    (IsAdicComplete.map_algebraMap_iff (S := R) (maximalIdeal Λ) X).2 (AnnihilatorQuotientFinite.finCompl Λ X _)
  have hf : ∀ j : ℕ, Finite (X ⧸ (m ^ j • ⊤ : Submodule R X)) := by
    intro j
    haveI : Finite (Λ ⧸ maximalIdeal Λ) := inferInstanceAs (Finite (ResidueField Λ))
    haveI : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
    haveI : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
      Submodule.finite_quotient_smul _ Module.Finite.fg_top
    have hle : (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X) ≤ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ := by
      refine Submodule.smul_le.2 fun a ha x _ => ?_
      rw [Submodule.restrictScalars_mem, hs]
      refine Submodule.smul_mem_smul ?_ Submodule.mem_top
      rw [hm, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem (s.comp MvPowerSeries.C) ha
    haveI : Finite (X ⧸ (m ^ j • ⊤ : Submodule R X).restrictScalars Λ) :=
      Finite.of_surjective _ (Submodule.factor_surjective hle)
    exact Finite.of_equiv _ (Submodule.Quotient.restrictScalarsEquiv Λ _).toEquiv
  have hI : ∀ j, (I j • ⊤ : Submodule R X) = m ^ j • ⊤ := by
    intro j
    have h0 : (Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) • ⊤ : Submodule R X) = ⊥ := by
      rw [← Submodule.le_annihilator_iff, Ideal.span_le]
      rintro _ ⟨a, rfl⟩
      exact Submodule.mem_annihilator.2 fun x _ => hy a x
    show ((_ ⊔ _ : Ideal R) • ⊤ : Submodule R X) = _
    rw [Submodule.sup_smul, h0, bot_sup_eq]
  let e := LinearEquiv.ofBijective _ (const_bij U m I hc hf hI)
  refine ⟨Φ ∘ₗ e.toLinearMap, e.symm.toLinearMap ∘ₗ Ψ, fun z => ?_, fun z => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact h2 z
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, map_smul, LinearEquiv.symm_apply_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem comap_inj {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (φ : H →* G)
    (hφ : Function.Surjective φ) {D D' : GDet n A G} (h : D.comap φ = D'.comap φ) : D = D' := by
  refine GDet.ext fun B _ _ x => ?_
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective hφ x.coeff
  have hx : MonoidAlgebra.mapDomainRingHom B φ (MonoidAlgebra.ofCoeff y) = x := by
    apply MonoidAlgebra.coeff_injective
    simp [MonoidAlgebra.mapDomainRingHom, MonoidAlgebra.mapDomain, hy]
  rw [← hx]
  exact congrArg (fun E : GDet n A H => E.D B (MonoidAlgebra.ofCoeff y)) h

private theorem comap_comp' {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [Group K] (φ : H →* G)
    (ψ : K →* H) (D : GDet n A G) : (D.comap φ).comap ψ = D.comap (φ.comp ψ) := by
  refine GDet.ext fun B _ _ x => ?_
  simp [GDet.comap, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_comp]

private theorem map_comap' {n : ℕ} {A A' G H : Type} [CommRing A] [CommRing A'] [Group G] [Group H] (φ : H →* G)
    (f : A →+* A') (D : GDet n A G) : (D.map f).comap φ = (D.comap φ).map f := by
  rfl

theorem UpperTheory.V.Pa.Core.ooMaps :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → o.p.Maps πb.toRingHom ((u.D.comap Λ.h.p₀).map (algebraMap B (Spo A))) fun v i => pushCh (algebraMap B (Spo A)) (u.ψ v i) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπ
  have hc : πb.toRingHom.comp (Ideal.Quotient.mk (ii W)) = m.π.toRingHom := RingHom.ext hπ
  refine ⟨?_, fun v i => ?_⟩
  · refine comap_inj (πo0 Λ) Λ.πo0_surj ?_
    rw [map_comap', map_comap', o.D_eq, (UpperTheory.V.CA.d_gmap W.t.D).2.1, hc, comap_comp']
    exact m.π_maps.1
  · have h2 := m.π_maps.2.1 v i
    refine Eq.trans ?_ h2
    rw [o.ψ_eq, ← hc]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrExt
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrExt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : W.R →ₐ[O] R'), (∀ i g, f (W.t.D.lam i (MonoidAlgebra.single g 1)) = f' (W.t.D.lam i (MonoidAlgebra.single g 1))) → (∀ v i g, f (W.t.ψ v i g) = f' (W.t.ψ v i g)) → f W.t.s = f' W.t.s → (∀ j i, f (W.t.U j i) = f' (W.t.U j i)) → (∀ j i, f (W.t.y j i) = f' (W.t.y j i)) → f = f' := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W R' _ _ _ f f' hD hψ hs hU hy
  obtain ⟨t', ht'⟩ := UpperTheory.V.Pa.Core.tupMap l L G0 T Λ n O r B u J D A W.R R' W.t f
  obtain ⟨-, -, hlam, -⟩ := UpperTheory.V.CA.d_gmap W.t.D
  have hl : ∀ (φ : W.R →+* R') i (g : Ph0 Λ), (W.t.D.map φ).lam i (MonoidAlgebra.single g 1) =
      φ (W.t.D.lam i (MonoidAlgebra.single g 1)) := fun φ i g => by
    have := (hlam φ (MonoidAlgebra.single g 1)).2 i
    rwa [MonoidAlgebra.mapRingHom_single, map_one] at this
  refine (W.univ R' t').unique ht' ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := ht'
  refine ⟨?_, fun v i => ?_, ?_, fun j i => ?_, fun j i => ?_⟩
  · rw [← h1]
    refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
    rw [hl, hl]
    exact (hD i g).symm
  · rw [← h2]
    ext g
    exact (hψ v i g).symm
  · exact hs.symm.trans h3
  · exact (hU j i).symm.trans (h4 j i)
  · exact (hy j i).symm.trans (h5 j i)
end

