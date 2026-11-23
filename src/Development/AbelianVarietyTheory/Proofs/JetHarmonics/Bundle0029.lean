module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Formalism.HermitianCurvature.StatementM
public import Formalism.HermitianCurvature.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwoBracketsLePowMulProdEntries

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory.AdicColimit

theorem smodEq_smul_top_map {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (f : M →ₗ[A] N) {x y : M} (h : x ≡ y [SMOD (J • ⊤ : Submodule A M)]) :
    f x ≡ f y [SMOD (J • ⊤ : Submodule A N)] := by
  rw [SModEq.sub_mem] at h ⊢
  rw [← map_sub]
  have : (J • ⊤ : Submodule A M).map f ≤ J • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨_, h, rfl⟩

theorem isAdicComplete_of_retract {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] (J : Ideal A) (s : N →ₗ[A] M) (p : M →ₗ[A] N) (hps : ∀ x, p (s x) = x)
    (h : IsAdicComplete J M) : IsAdicComplete J N := by
  refine { toIsHausdorff := ⟨?_⟩, toIsPrecomplete := ⟨?_⟩ }
  · intro x hx
    have : s x = 0 := IsHausdorff.haus h.toIsHausdorff (s x) fun n => by
      simpa using smodEq_smul_top_map _ s (hx n)
    rw [← hps x, this, map_zero]
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := fun n => s (f n)) fun {m n} hmn =>
      smodEq_smul_top_map _ s (hf hmn)
    exact ⟨p L, fun n => by simpa [hps] using smodEq_smul_top_map _ p (hL n)⟩

theorem isAdicComplete_map_eval {A ι : Type} [CommRing A] (T : ι → Type) [∀ i, CommRing (T i)]
    (e : A ≃+* Π i, T i) (J : Ideal A) (h : IsAdicComplete J A) (i : ι) :
    IsAdicComplete (J.map ((Pi.evalRingHom T i).comp e.toRingHom)) (T i) := by
  classical
  letI : Algebra A (T i) := ((Pi.evalRingHom T i).comp e.toRingHom).toAlgebra
  let s : T i →ₗ[A] A :=
    { toFun t := e.symm (Pi.single i t)
      map_add' x y := by rw [Pi.single_add, map_add (f := _)]
      map_smul' a t := by
        apply e.injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply,
          ← Pi.single_mul_right]
        rfl }
  refine (IsAdicComplete.map_algebraMap_iff J (T i)).2
    (isAdicComplete_of_retract J s (Algebra.linearMap A (T i)) (fun t => ?_) h)
  change e (e.symm (Pi.single i t)) i = t
  rw [e.apply_symm_apply, Pi.single_eq_same]

theorem isAdicColimit_finite_henselian_of_local :
    (∀ (R : Type) [CommRing R] (I : Ideal R) (A : Type) [CommRing A] [IsLocalRing A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ)))) → (∀ (R : Type) [CommRing R] (I : Ideal R) (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0}), (∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j))) → (∀ i, IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) → IsAdicColimit I T) → ∀ (R : Type) [CommRing R] (I : Ideal R) (O : Type) [CommRing O] [HenselianLocalRing O] (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] (φ : R →+* A), IsAdicComplete (I.map φ) A → IsAdicColimit I (Over.mk (Spec.map (CommRingCat.ofHom φ))) := by
  intro hloc hcov R _ I O _ _ A _ _ _ φ hc
  classical
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O A
  let π (i : ι) : A →+* T i := (Pi.evalRingHom T i).comp e.toRingEquiv.toRingHom
  have hopen (i : ι) : IsOpenImmersion (Spec.map (CommRingCat.ofHom (π i))) := by
    have : IsIso (CommRingCat.ofHom e.toRingEquiv.toRingHom) :=
      inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    infer_instance
  let 𝒰 : (Spec (CommRingCat.of A)).OpenCover := Scheme.Cover.mkOfCovers ι
    (fun i => Spec (CommRingCat.of (T i))) (fun i => Spec.map (CommRingCat.ofHom (π i))) (fun x => by
      obtain ⟨i, q, hq⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq
        (PrimeSpectrum.comap e.toRingEquiv.symm.toRingHom x)
      refine ⟨i, q, ?_⟩
      change PrimeSpectrum.comap e.toRingEquiv.toRingHom (PrimeSpectrum.comap (Pi.evalRingHom T i) q) = x
      rw [hq]
      ext a
      change e.symm (e a) ∈ x.asIdeal ↔ _
      rw [e.symm_apply_apply]) hopen
  refine hcov R I (Over.mk (Spec.map (CommRingCat.ofHom φ))) 𝒰 (fun i j hij => ?_) fun i => ?_
  · rw [Set.disjoint_left]
    rintro x ⟨p, rfl⟩ ⟨q, hq⟩
    change ι at i j
    change PrimeSpectrum (T i) at p
    change PrimeSpectrum (T j) at q
    change PrimeSpectrum.comap (π j) q = PrimeSpectrum.comap (π i) p at hq
    have h1 : e.symm (Pi.single i 1) ∈ (PrimeSpectrum.comap (π j) q).asIdeal := by
      change e (e.symm (Pi.single i 1)) j ∈ q.asIdeal
      rw [e.apply_symm_apply, Pi.single_eq_of_ne (i := i) (i' := j) (fun h => hij h.symm)]
      exact zero_mem _
    rw [hq] at h1
    change e (e.symm (Pi.single i 1)) i ∈ p.asIdeal at h1
    rw [e.apply_symm_apply, Pi.single_eq_same] at h1
    exact p.isPrime.one_notMem h1
  · change ι at i
    have := (hT i).1
    have key := hloc R I (T i) ((π i).comp φ) (by
      rw [← Ideal.map_map]
      exact isAdicComplete_map_eval T e.toRingEquiv _ hc i)
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at key
    exact key

end GlobalTheory.AdicColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfDisjointCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AdicColimit


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.AdicColimit.isAdicColimit_of_disjoint_cover (R : Type) [CommRing R] (I : Ideal R)
    (T : Over (Spec (CommRingCat.of R))) (𝒰 : T.left.OpenCover.{0})
    (hd : ∀ i j, i ≠ j → Disjoint (Set.range (𝒰.f i)) (Set.range (𝒰.f j)))
    (h : ∀ i, _root_.GlobalTheory.AdicColimit.IsAdicColimit I (Over.mk (𝒰.f i ≫ T.hom))) :
    _root_.GlobalTheory.AdicColimit.IsAdicColimit I T := by
  obtain ⟨r, hr⟩ : ∃ r : ∀ i, Over.mk (𝒰.f i ≫ T.hom) ⟶ T, ∀ i, (r i).left = 𝒰.f i :=
    ⟨fun i => Over.homMk (𝒰.f i) rfl, fun i => rfl⟩
  intro X f hf

  have hfi : ∀ i, ∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Out.thickMap R I e (Over.mk (𝒰.f i ≫ T.hom)) ≫
      (_root_.GlobalTheory.AdicColimit.thickHom I (e + 1) (r i) ≫ f (e + 1)) = _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e := by
    intro i e
    rw [_root_.GlobalTheory.AdicColimit.thickMap_thickHom_assoc, hf]
  choose g hg hgu using fun i => h i X (fun e => _root_.GlobalTheory.AdicColimit.thickHom I e (r i) ≫ f e) (hfi i)
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have : pullback.fst (𝒰.f i) (𝒰.f i) = pullback.snd (𝒰.f i) (𝒰.f i) :=
        (cancel_mono (𝒰.f i)).1 pullback.condition
      rw [this]
    · haveI : IsEmpty ↥(pullback (𝒰.f i) (𝒰.f j)) := ⟨fun x =>
        Set.disjoint_left.1 (hd i j hij) ⟨pullback.fst (𝒰.f i) (𝒰.f j) x, rfl⟩
          ⟨pullback.snd (𝒰.f i) (𝒰.f j) x, by
            rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨𝒰.glueMorphisms g hglue, fun e => ?_, fun y hy => ?_⟩
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ (_root_.GlobalTheory.AdicColimit.thickι I e T)) _ _ fun i => ?_
    change pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _ =
      pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc, Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    let φ : pullback (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ⟶
        (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj R I e (Over.mk (𝒰.f i ≫ T.hom))).left :=
      pullback.lift (pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i))
        (pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e))
        (by
          show pullback.snd _ _ ≫ 𝒰.f i ≫ T.hom = _
          rw [← Category.assoc, ← pullback.condition]
          simp only [Category.assoc]
          exact congrArg (fun k => pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ k)
            (pullback.condition (f := T.hom) (g := _root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)))
    have hφ₁ : φ ≫ _root_.GlobalTheory.AdicColimit.thickι I e (Over.mk (𝒰.f i ≫ T.hom)) =
        pullback.snd (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := pullback.lift_fst _ _ _
    have hφ₂ : φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i) = pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) := by
      apply pullback.hom_ext
      · change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T =
          pullback.fst (_root_.GlobalTheory.AdicColimit.thickι I e T) (𝒰.f i) ≫ _root_.GlobalTheory.AdicColimit.thickι I e T
        rw [Category.assoc, _root_.GlobalTheory.AdicColimit.thickHom_ι, ← Category.assoc, hφ₁]
        erw [hr i]
        exact pullback.condition.symm
      · have hw := Over.w ((Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e)).map (r i))
        change (φ ≫ _root_.GlobalTheory.AdicColimit.thickHom I e (r i)) ≫ pullback.snd T.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I e) = _
        rw [Category.assoc]
        erw [hw]
        exact pullback.lift_snd _ _ _
    rw [← hφ₁, Category.assoc]
    erw [hg i e]
    rw [← Category.assoc, hφ₂]
  · refine 𝒰.hom_ext _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms 𝒰 g hglue i]
    refine hgu i _ fun e => ?_
    have hcomp := _root_.GlobalTheory.AdicColimit.thickHom_ι_assoc I e (r i) y
    rw [hr] at hcomp
    rw [← hcomp, hy]

end GlobalTheory.AdicColimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicCompleteOfPowLeOfPowLe
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AdicColimit

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry in
theorem _root_.GlobalTheory.isAdicComplete_of_pow_le_of_pow_le (A : Type) [CommRing A] (J J' : Ideal A) (k l : ℕ)
    (h1 : J ^ k ≤ J') (h2 : J' ^ l ≤ J) (h : IsAdicComplete J A) : IsAdicComplete J' A := by
  have hk : J ^ (k + 1) ≤ J' := le_trans (Ideal.pow_le_pow_right (Nat.le_succ k)) h1
  have hl : J' ^ (l + 1) ≤ J := le_trans (Ideal.pow_le_pow_right (Nat.le_succ l)) h2
  have hJ : ∀ m, J ^ ((k + 1) * m) ≤ J' ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hk m
  have hJ' : ∀ m, J' ^ ((l + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]; exact Ideal.pow_right_mono hl m
  exact
    { haus' := fun x hx => h.toIsHausdorff.haus' x fun m =>
        (hx ((l + 1) * m)).mono (Submodule.smul_mono_left (hJ' m))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun m => f ((l + 1) * m))
          (fun {m n} hmn => (hf (Nat.mul_le_mul_left (l + 1) hmn)).mono
            (Submodule.smul_mono_left (hJ' m)))
        refine ⟨L, fun n => ?_⟩
        have hn : n ≤ (l + 1) * ((k + 1) * n) :=
          (Nat.le_mul_of_pos_left n (Nat.succ_pos k)).trans
            (Nat.le_mul_of_pos_left _ (Nat.succ_pos l))
        exact (hf hn).trans ((hL ((k + 1) * n)).mono (Submodule.smul_mono_left (hJ n))) }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesAlt
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem powerSeriesEvalTsum_unitDisc_properties : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (x : K), ‖x‖ < 1 → (∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x)) ∧ (∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧ ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x) ∧ (∀ a : K, ev1 (PowerSeries.C a) x = a) ∧ ev1 PowerSeries.X x = x ∧ (∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x) ∧ (∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) → ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x) ∧ (∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧ ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧ ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2) ∧ (∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f → ev1 (f.subst g) x = ev1 f (ev1 g x)) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h → PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 → ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x = ev F ![ev1 g x, ev1 h x]) ∧ (∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F → Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y]) ∧ (∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f) := by
  intro K _ _ _ x hx
  have A := _root_.GlobalTheory.ConvSer.Bridge.csub_bridge K
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, BetaSesquilinearity, B9, lowerOffDiagonalCoeff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨C1, C2, C3, C4, C5, C6, C7, C8⟩ := _root_.GlobalTheory.ConvSer.ev_algebra K Unit (fun _ => x) (fun _ => hx)
  have hev : ∀ (f : PowerSeries K) (t : K), ev1 f t = ev f (fun _ : Unit => t) := A.2.1
  have P1 : ∀ f : PowerSeries K, Bdd f → PowerSeriesHasSumAt f x (ev1 f x) := by
    intro f hf
    rw [A.2.2.1, hev]
    exact C1 f hf
  have P2 : ∀ f g : PowerSeries K, Bdd f → Bdd g → ev1 (f + g) x = ev1 f x + ev1 g x ∧
      ev1 (f - g) x = ev1 f x - ev1 g x ∧ ev1 (f * g) x = ev1 f x * ev1 g x := by
    intro f g hf hg
    simp only [hev]
    exact C2 f g hf hg
  have P3 : ∀ a : K, ev1 (PowerSeries.C a) x = a := by
    intro a
    rw [hev]
    exact C3 a
  have P4 : ev1 PowerSeries.X x = x := by
    rw [hev]
    exact C4 ()
  have hBddX : Bdd (PowerSeries.X : PowerSeries K) := (B3 _ 0).2.2 (B5 ()).1
  have hBddP : ∀ P : Polynomial K, Bdd (P : PowerSeries K) := by
    intro P
    rw [(lowerOffDiagonalCoeff _).2]
    refine ⟨∑ i ∈ P.support, ‖P.coeff i‖, fun m => ?_⟩
    rw [Polynomial.coeff_coe]
    by_cases hm : m ∈ P.support
    · exact Finset.single_le_sum (f := fun i => ‖P.coeff i‖) (fun i _ => norm_nonneg _) hm
    · have h0 : P.coeff m = 0 := by simpa using hm
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have P5 : ∀ P : Polynomial K, Bdd (P : PowerSeries K) ∧ ev1 (P : PowerSeries K) x = P.eval x := by
    intro P
    refine ⟨hBddP P, ?_⟩
    refine Polynomial.induction_on P ?_ ?_ ?_
    · intro a
      rw [Polynomial.coe_C, P3, Polynomial.eval_C]
    · intro p q hp hq
      rw [Polynomial.coe_add, (P2 _ _ (hBddP p) (hBddP q)).1, hp, hq, Polynomial.eval_add]
    · intro m a ih
      have e : (Polynomial.C a * Polynomial.X ^ (m + 1) : Polynomial K) =
          (Polynomial.C a * Polynomial.X ^ m) * Polynomial.X := by ring
      rw [e, Polynomial.coe_mul, Polynomial.coe_X, (P2 _ _ (hBddP _) hBddX).2.2, ih, P4]
      simp
  have P6 : ∀ (ι : Type) (t : Finset ι) (f : ι → PowerSeries K), (∀ i ∈ t, Bdd (f i)) →
      ev1 (∏ i ∈ t, f i) x = ∏ i ∈ t, ev1 (f i) x := by
    intro ι t f hf
    classical
    induction t using Finset.induction_on with
    | empty =>
      have h1 : (1 : PowerSeries K) = PowerSeries.C 1 := by simp
      rw [Finset.prod_empty, Finset.prod_empty, h1, P3]
    | @insert j s hj ih =>
      have hs : ∀ i ∈ s, Bdd (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert hj, Finset.prod_insert hj,
        (P2 _ _ (hf j (Finset.mem_insert_self j s)) ((B6 ι s f).2 hs).1).2.2, ih hs]
  have P7 : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 ∧
      ‖ev1 f x - PowerSeries.coeff 0 f‖ ≤ ‖x‖ ∧
      ‖ev1 f x - PowerSeries.coeff 0 f - PowerSeries.coeff 1 f * x‖ ≤ ‖x‖ ^ 2 := by
    have hI : ∀ f : PowerSeries K, Intg f → ‖ev1 f x‖ ≤ 1 := fun f hf => by
      rw [hev]
      exact (C5 f hf).1
    have hsh : ∀ f : PowerSeries K, Intg f →
        Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) ∧
        ev1 f x = PowerSeries.coeff 0 f +
          x * ev1 (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) x := by
      intro f hf
      have hg : Intg (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) := by
        rw [(lowerOffDiagonalCoeff _).1]
        intro m
        rw [PowerSeries.coeff_mk]
        exact (lowerOffDiagonalCoeff f).1.mp hf (m + 1)
      refine ⟨hg, ?_⟩
      have hgb := (B3 _ 0).2.2 hg
      have e : ev1 f x = ev1 ((PowerSeries.X * PowerSeries.mk fun p => PowerSeries.coeff (p + 1) f) +
          PowerSeries.C (PowerSeries.constantCoeff f)) x :=
        congrArg (fun F => ev1 F x) (PowerSeries.eq_X_mul_shift_add_const f)
      rw [e, (P2 _ _ (B2 _ _ hBddX hgb).2.2
        (show Bdd (PowerSeries.C (PowerSeries.constantCoeff f)) from (B4 _).1)).1, (P2 _ _ hBddX hgb).2.2, P4, P3,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      ring
    intro f hf
    obtain ⟨hg, e1⟩ := hsh f hf
    obtain ⟨hh, e2⟩ := hsh _ hg
    rw [PowerSeries.coeff_mk, zero_add] at e2
    refine ⟨hI f hf, ?_, ?_⟩
    · rw [e1, add_sub_cancel_left, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hI _ hg)
    · have key : ∀ a b d : K, a + x * (b + x * d) - a - b * x = x ^ 2 * d := by
        intro a b d
        ring
      rw [e1, e2, key, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hI _ hh)
  have P8 : ∀ (f g : PowerSeries K), Intg g → PowerSeries.constantCoeff g = 0 → Bdd f →
      ev1 (f.subst g) x = ev1 f (ev1 g x) := by
    intro f g hg h0 hf
    rw [hev (f.subst g), hev g]
    exact C8 g f hg h0 hf
  have P9 : ∀ (F : MvPowerSeries (Fin 2) K) (g h : PowerSeries K), Bdd F → Intg g → Intg h →
      PowerSeries.constantCoeff g = 0 → PowerSeries.constantCoeff h = 0 →
      ev1 (MvPowerSeries.subst (![g, h] : Fin 2 → MvPowerSeries Unit K) F) x =
        ev F ![ev1 g x, ev1 h x] := by
    intro F g h hF hg hh hg0 hh0
    rw [hev, C7 (Fin 2) ![g, h] F (fun j => by fin_cases j; exacts [hg, hh])
      (fun j => by fin_cases j; exacts [hg0, hh0]) hF]
    congr 1
    funext j
    fin_cases j <;> simp [hev]
  have product_first_zeroth_parts : ∀ (F : MvPowerSeries (Fin 2) K) (y : K), ‖y‖ < 1 → Intg F →
      Intg (shift1 F y) ∧ ev1 (shift1 F y) x = ev F ![x, y] := by
    intro F y hy hF
    have hs : ∀ i, Small ((![PowerSeries.X, PowerSeries.C y] : Fin 2 → MvPowerSeries Unit K) i) := by
      intro i
      fin_cases i
      · exact B5 ()
      · exact (B4 y).2.2 hy
    have hFb : Bdd F := ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 F 0).2.2 hF
    have D := _root_.GlobalTheory.ConvSer.csub_hasSum_and_bounds K (Fin 2) Unit _ F hs hFb
    rw [A.2.2.2.2.1 F y]
    refine ⟨D.2.2.1 hF, ?_⟩
    rw [hev, C6 (Fin 2) _ F hs hFb]
    congr 1
    funext j
    fin_cases j
    · exact C4 ()
    · exact C3 y
  have product_first_partition : ∀ f : PowerSeries K, ev1 f 0 = PowerSeries.coeff 0 f := by
    intro f
    unfold ev1
    rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
    simp
  exact ⟨P1, P2, P3, P4, P5, P6, P7, P8, P9, product_first_zeroth_parts, product_first_partition⟩

end GlobalTheory.ConvSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdFinEqProdIcc
section
open Formalism.FourierDecayAlt Finset

namespace GlobalTheory.NormaliserCutBound

theorem prod_fin_eq_prod_Icc (n : ℕ) (f : Fin n → ℝ) (g : ℕ → ℝ)
    (h : ∀ s : Fin n, g (s.val + 1) = f s) : ∏ s, f s = ∏ s ∈ Finset.Icc 1 n, g s := by
  have h1 : ∏ s, f s = ∏ s : Fin n, g (s.val + 1) := Finset.prod_congr rfl (fun s _ => (h s).symm)
  rw [h1, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem qC_re (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by
  have : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
    unfold M.qC I.qpoly
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

theorem main : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by
  intro C b c P l lam nn Y hP hC hl hlk hc hcb hkb hu hu' hlam hgap hint hint' hT hT' hnn hcut y hy
  have hcy := hcut y hy
  have hb3 : 3 ≤ b := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = 2 * P.r + P.k + 1 := ⟨_, rfl⟩
  revert lam
  rw [← hn]
  intro lam hlam hgap hint hint' hnn
  let lamN : ℕ → ℝ := fun s => if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
  have hlamN : ∀ s : Fin n, lamN (s.val + 1) = lam s := by
    intro s
    simp [lamN, s.isLt]
  have hlamN' : ∀ (s : ℕ) (h : s - 1 < n), lamN s = lam ⟨s - 1, h⟩ := by
    intro s h
    simp [lamN, h]
  have hn' : P.k + 2 * P.r + 1 = n := by omega
  have hinter : I.Interlaces P.k P.u P.u' P.lo := by
    intro i hi
    have hg := hP.gap i hi
    unfold M.Par.hi at hg
    have h1 := min_le_left (P.u i) (P.u' i)
    have h2 := min_le_right (P.u i) (P.u' i)
    have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> unfold M.Par.lo <;> linarith
  have hint2 : ∀ v : ℕ → ℝ, (∀ s : Fin n, s.val + 2 ≤ P.k →
      (s.val + 1 ≠ l → lam s + 1 / 2 ≤ v (s.val + 1)) ∧
        (s.val + 2 ≠ l → v (s.val + 2) + 1 / 2 ≤ lam s)) →
      ∀ s : ℕ, 1 ≤ s → s + 1 ≤ P.k → (s ≠ l → lamN s + 1 / 2 ≤ v s) ∧
        (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lamN s) := by
    intro v hv s hs hsk
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have ht : t < n := by omega
    have h := hv ⟨t, ht⟩ hsk
    rw [← hlamN ⟨t, ht⟩] at h
    exact h
  have hmain := GlobalTheory.two_brackets_le_pow_mul_prod_entries P.k P.r l b c y lamN P.u P.u' hl hlk hc hcb
    hkb hu hu'
    (by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [hlamN' s (by omega)]
      exact hlam _)
    (by
      intro s hs hsk
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have ht : t < n := by omega
      have ht' : t + 1 < n := by omega
      have h := hgap ⟨t, ht⟩ ⟨t + 1, ht'⟩ rfl (by simp only; omega)
      rw [← hlamN ⟨t, ht⟩, ← hlamN ⟨t + 1, ht'⟩] at h
      exact h)
    (hint2 _ hint) (hint2 _ hint')
    (by
      intro i hi hik
      obtain ⟨h1, h2, h3, h4⟩ := hinter i (Finset.mem_Icc.mpr ⟨hi, hik⟩)
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    hcy
  rw [hn'] at hmain
  have e0 : ∏ s, (|y + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + lamN s| + c) (fun s => by simp only [hlamN])
  have e1 : ∏ s, (|y + 1 + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + 1 + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + 1 + lamN s| + c) (fun s => by simp only [hlamN])
  rw [← e0, ← e1] at hmain
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l y P.T P.T' hl hlk hinter hcy
    hP.T_pos hP.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hP.T_pos hP.T'_pos
  have hqe : I.qpoly P.k P.T P.T' P.u P.u' y = (P.T * P.T') *
      ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| := by
    rw [← abs_of_pos hq]
    unfold I.qpoly
    rw [abs_mul, abs_neg, abs_of_pos hTT, Finset.abs_prod]
  have hsize := (GlobalTheory.LamSize.main C b P.T P.T' P.r 1 hC hb3 (by push_cast; linarith) hT hT').2
  rw [Nat.cast_one, one_mul] at hsize
  have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [qC_re, hqe, ← mul_assoc]
  calc nn y * nn (y + 1) ≤ (∏ s, (|y + lam s| + c)) * ∏ s, (|y + 1 + lam s| + c) :=
        mul_le_mul (hnn y).2 (hnn (y + 1)).2 (hnn (y + 1)).1 ((hnn y).1.trans (hnn y).2)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize hA

end GlobalTheory.NormaliserCutBound
end

