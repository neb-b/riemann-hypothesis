module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.AcycQAPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.AcycQAPf

def MVHyp (q : ℕ) (i n : ℤ) : Prop := ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) → ∀ f g : S,
  Ideal.span {f, g} = ⊤ → ∀ c : Ht q (sp (Localization.Away (f * g))) n i,
    ∃ a b, c = pull _ (spMap (rL f g)) _ n a - pull _ (spMap (rR f g)) _ n b

def Deg0 : Prop := QAClosed → EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions → LCSplit → A9 → ∀ (q : ℕ) [NeZero q] (i : ℤ), MVHyp q i 0

def Cover : Prop := QAClosed → MV → A1 → ∀ (q : ℕ) [NeZero q] (i n : ℤ), MVHyp q i n → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
  ∀ x : Ht q (sp S) (n + 1) i, (∀ p : PrimeSpectrum S, ∃ f : S, f ∉ p.asIdeal ∧
    pull _ (spMap (algebraMap S (Localization.Away f))) _ _ x = 0) → x = 0

theorem step (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hC : Cover) (h1 : A1) (b1 : B1) (b2 : B2) (q : ℕ) [NeZero q] (i : ℤ) :
    ∀ k : ℕ, MVHyp q i k → ∀ (S : Type) [CommRing S], QA S → IsUnit (q : S) →
      Subsingleton (Ht q (sp S) ((k : ℤ) + 1) i) := by
  intro k hk S _ hS hq
  refine subsingleton_of_forall_eq 0 fun x => ?_
  refine hC hQ hM h1 q i k hk S hS hq x fun p => ?_
  exact hZ b1 b2 q S (hQ S hS).1 hq _ i (by omega) x p

theorem AcycQA_of (hQ : QAClosed) (hZ : ZarLocal) (hM : MV) (hH : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hL : LCSplit) (hD : Deg0) (hC : Cover) :
    AcycQA := by
  intro h1 h9 b1 b2 q _ S _ hS hq
  have key : ∀ k : ℕ, MVHyp q 0 k ∧ ∀ (i : ℤ), MVHyp q i k := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hD hQ hH hL h9 q 0, fun i => by simpa using hD hQ hH hL h9 q i⟩
    | succ k ih =>
      have hv : ∀ (i : ℤ), MVHyp q i ((k + 1 : ℕ) : ℤ) := by
        intro i S' _ hS' hq' f g _ c
        have hfg : QA (Localization.Away (f * g)) := (hQ S' hS').2.1 (f * g)
        have hqfg : IsUnit (q : Localization.Away (f * g)) := by
          simpa using hq'.map (algebraMap S' (Localization.Away (f * g)))
        have hs := step hQ hZ hM hC h1 b1 b2 q i k (ih.2 i) _ hfg hqfg
        refine ⟨0, 0, ?_⟩
        have : c = 0 := by
          have e : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
          revert c; rw [e]; intro c; exact Subsingleton.elim _ _
        simp [this]
      exact ⟨hv 0, hv⟩
  intro n i hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  exact step hQ hZ hM hC h1 b1 b2 q i k ((key k).2 i) S hS hq

end LateralTheory.E.AcycQAPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechLevels
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf
open PrimeSpectrum

theorem qm_comp {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ := Ideal.quotientMap_comp_mk _

theorem qm_integral {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).IsIntegral := by
  apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I)
  rw [qm_comp]
  exact RingHom.IsIntegral.trans _ _ h (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)

theorem qm_surj {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Surjective (PrimeSpectrum.comap (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  intro P
  obtain ⟨Q, hQ⟩ := hs (PrimeSpectrum.comap (Ideal.Quotient.mk I) P)
  have hmem : Q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map φ))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    show I.map φ ≤ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have : x ∈ (PrimeSpectrum.comap φ Q).asIdeal := by
      rw [hQ]; show Ideal.Quotient.mk I x ∈ P.asIdeal; rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _
    exact this
  obtain ⟨Q', rfl⟩ := hmem
  refine ⟨Q', comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, qm_comp]

theorem spec_surj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) : Surjective (Spec.map (CommRingCat.ofHom f)) := by
  rw [surjective_iff]; exact hs

theorem part1 {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) :=
  ⟨IsIntegralHom.SpecMap_iff.2 h, spec_surj _ hs, IsIntegralHom.SpecMap_iff.2 (qm_integral φ I h),
    spec_surj _ (qm_surj φ I hs)⟩

end LateralTheory.E.CechLevelsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassSpecialization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleExistenceAndUniqueness

open LateralTheory.E.CupProductRingLaws

section Ext
variable {R : Type} [CommRing R]

theorem free_hom_ext {P : PSh} {F : Shv R} (f g : (free R).obj P ⟶ F)
    (h : ∀ U x, (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J := Scheme.etaleTopology) f.hom g.hom F.property
  ext U : 2
  induction U using Opposite.rec with | _ U => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact h U x

theorem cochain_ext_ev {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hev : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) :
    α = β := by
  apply Cochain.ext
  intro p s hps
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
    have : (chainsXIso R E k).inv ≫ α.v _ _ hps = (chainsXIso R E k).inv ≫ β.v _ _ hps :=
      free_hom_ext _ _ (fun U x => hev k s hps U x)
    simpa using this
  · refine (HomologicalComplex.isZero_extend_X _ _ p (fun i => ?_)).eq_of_src _ _
    show -(i : ℤ) ≠ p
    omega

theorem res_isZero (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  HomologicalComplex.isZero_extend_X _ _ s (fun i => by show (i : ℤ) ≠ s; omega)

end Ext

def EtaleKummerChernCocycleEvaluationsUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernClassCocycle q L γ → IsEtaleFirstChernClassCocycle q L γ' →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 1 (by simp) U x = ev γ'.1 1 1 (by simp) U x) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev γ.1 2 0 (by simp) U x = ev γ'.1 2 0 (by simp) U x

def EtaleKummerChernCocycleExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ γ, IsEtaleFirstChernClassCocycle q L γ

theorem etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness (hU : EtaleKummerChernCocycleEvaluationsUnique) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hq : Inv q E)
    (γ γ' : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (h : IsEtaleFirstChernClassCocycle q L γ) (h' : IsEtaleFirstChernClassCocycle q L γ') :
    γ = γ' := by
  obtain ⟨h1, h2⟩ := hU q L hq γ γ' h h'
  apply Subtype.ext
  apply cochain_ext_ev
  intro p s hs U x
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [h.1 U x, h'.1 U x]
  · obtain rfl : s = 1 := by omega
    exact h1 U x
  · obtain rfl : s = 0 := by omega
    exact h2 U x
  · unfold ev
    rw [(res_isZero (tw q 1) s (by omega)).eq_of_tgt ((chainsXIso _ E _).inv ≫ γ.1.v _ _ hs)
      ((chainsXIso _ E _).inv ≫ γ'.1.v _ _ hs)]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hU : EtaleKummerChernCocycleEvaluationsUnique) : EtaleFirstChernClassRepresentedByChernCocycle := by
  intro q _ E L hq
  obtain ⟨γ0, h0⟩ := hE q L hq
  refine ⟨⟨γ0, h0⟩, fun γ hγ => ?_⟩
  have hex : ∃ c : Ht q E 2 1, ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧ IsEtaleFirstChernClassCocycle q L γ :=
    ⟨_, γ0, rfl, h0⟩
  obtain ⟨γ1, hc, h1⟩ := pick_spec hex
  have : γ1 = γ := etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness hU q L hq γ1 γ h1 hγ
  subst this
  exact hc.symm

end LateralTheory.E.ChernCocycleExistenceAndUniqueness
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverIntegralClosure
section
noncomputable section
open GlobalTheory.EtC

namespace LateralTheory.E.CoverIntegralClosure

theorem inj_sub (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) :=
  Subtype.val_injective

theorem aic_integralClosure (P : Type) [CommRing P] [IsDomain P] :
    AIC (integralClosure P (AlgebraicClosure (FractionRing P))) := by
  intro p hp hdeg
  have hdeg' : (p.map (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P)))).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (inj_sub P)]
    intro h
    rw [Polynomial.degree_eq_natDegree hp.ne_zero] at h
    norm_cast at h
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root _ hdeg'
  have hTa : IsIntegral (integralClosure P (AlgebraicClosure (FractionRing P))) a :=
    ⟨p, hp, by simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha⟩
  have hPa : IsIntegral P a := isIntegral_trans a hTa
  have ha' : Polynomial.eval₂ (algebraMap (integralClosure P (AlgebraicClosure (FractionRing P))) (AlgebraicClosure (FractionRing P))) a p = 0 := by
    simpa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap, Polynomial.aeval_def] using ha
  refine ⟨⟨a, hPa⟩, ?_⟩
  apply inj_sub P
  rw [map_zero, ← Polynomial.eval₂_at_apply]
  exact ha'

theorem inj_P (P : Type) [CommRing P] [IsDomain P] :
    Function.Injective (algebraMap P (integralClosure P (AlgebraicClosure (FractionRing P)))) := by
  have h : Function.Injective (algebraMap P (AlgebraicClosure (FractionRing P))) := by
    rw [IsScalarTower.algebraMap_eq P (FractionRing P) (AlgebraicClosure (FractionRing P))]
    exact (algebraMap (FractionRing P) _).injective.comp (IsFractionRing.injective P _)
  rw [IsScalarTower.algebraMap_eq P (integralClosure P (AlgebraicClosure (FractionRing P)))
    (AlgebraicClosure (FractionRing P))] at h
  exact fun x y hxy => h (by simp only [RingHom.comp_apply, hxy])

theorem Cover_of : LateralTheory.E.t_E1Cut.Cover := by
  intro A _
  let π : MvPolynomial A ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) id
  have hπ : Function.Surjective π := fun a => ⟨MvPolynomial.X a, by simp [π]⟩
  let T := integralClosure (MvPolynomial A ℤ) (AlgebraicClosure (FractionRing (MvPolynomial A ℤ)))
  let I : Ideal T := (RingHom.ker π).map (algebraMap (MvPolynomial A ℤ) T)
  let ψ : MvPolynomial A ℤ ⧸ RingHom.ker π →+* T ⧸ I :=
    Ideal.quotientMap I (algebraMap (MvPolynomial A ℤ) T) Ideal.le_comap_map
  let φ : A →+* T ⧸ I := ψ.comp (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom
  have hcomp : φ.comp π = (Ideal.Quotient.mk I).comp (algebraMap (MvPolynomial A ℤ) T) := by
    apply RingHom.ext
    intro x
    simp [φ, ψ, Ideal.quotientMap_mk]
  refine ⟨T ⧸ I, inferInstance, φ, ?_, ?_, ?_⟩
  · apply RingHom.IsIntegral.tower_top π φ
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (fun x => Algebra.IsIntegral.isIntegral x)
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  · intro p
    have : (Ideal.comap π p.asIdeal).IsPrime := Ideal.comap_isPrime π p.asIdeal
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T)
      (Ideal.comap π p.asIdeal) (⊥ : Ideal T) (by
        rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (inj_P _)]
        exact bot_le)
    rw [Ideal.under_def] at hQc
    have hIQ : I ≤ Q := by
      apply Ideal.map_le_iff_le_comap.2
      rw [hQc]
      intro x hx
      simp [RingHom.mem_ker.1 hx]
    have hQ' : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨Q.map (Ideal.Quotient.mk I), hQ'⟩, ?_⟩
    ext1
    apply Ideal.comap_injective_of_surjective π hπ
    simp only [PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap,
      Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hIQ, hQc]
  · exact ⟨T, inferInstance, inferInstance, Ideal.Quotient.mk I, aic_integralClosure _,
      Ideal.Quotient.mk_surjective⟩

end LateralTheory.E.CoverIntegralClosure
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescentInduction
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.DescStepPf

def Bounds : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  ((chains R).obj E).IsStrictlyLE 0 ∧ (res R F).IsStrictlyGE 0 ∧ ∀ m, Injective ((res R F).X m)

def LevelIdent : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ⟶ E') (p : ℕ) (j : ℤ),
  (Function.Bijective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j)) ∧
  (Function.Injective (pull R (disc.map (f.app (op (SimplexCategory.mk p)))) F j) ↔
    Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (((chains R).map f).f (-(p : ℤ)))) (res R F) j))

def CxDesc : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ m, Injective (I.X m)) →
  ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (n : ℤ),
  (∀ (p : ℕ) (j : ℤ), j < n → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I j)) →
  (∀ p : ℕ, Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-(p : ℤ)))) I n)) →
  (∀ j : ℤ, Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j)) →
  (∀ j : ℤ, j < n + 1 → Function.Bijective (cpull g I j)) ∧ Function.Injective (cpull g I (n + 1))

theorem DescStep_of (hB : Bounds) (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep := by
  intro _ R _ F E E' f n hc he
  obtain ⟨h1, h2, h3⟩ := hB R F E
  obtain ⟨h1', -, -⟩ := hB R F E'
  have := h2
  have := h1
  have := h1'
  exact hX R (res R F) h3 ((chains R).map f) n
    (fun p j hj => ((hL R F f p j).1).1 ((hc (op (SimplexCategory.mk p))).1 j hj))
    (fun p => ((hL R F f p n).2).1 (hc (op (SimplexCategory.mk p))).2)
    (fun j => ((hL R F f 0 j).1).1 (he j))

end LateralTheory.E.DescStepPf

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EqvQAPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EqvQAPf

theorem prim_of_aic (q : ℕ) [NeZero q] (S : Type) [CommRing S] (hS : AIC S) (hq : IsUnit (q : S)) :
    Nonempty (Prim q S) := by
  rcases subsingleton_or_nontrivial S with hs | hs
  · exact ⟨⟨0, hq, Subsingleton.elim _ _⟩⟩
  have hm : ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).Monic :=
    (Polynomial.cyclotomic.monic q ℤ).map _
  have hd : 0 < ((Polynomial.cyclotomic q ℤ).map (Int.castRingHom S)).natDegree := by
    rw [(Polynomial.cyclotomic.monic q ℤ).natDegree_map, Polynomial.natDegree_cyclotomic]
    exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  obtain ⟨a, ha⟩ := hS _ hm hd
  exact ⟨⟨a, hq, by rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]; simpa using ha⟩⟩

theorem bij_of_sub {A B : Type*} [AddZeroClass A] [AddZeroClass B] [Subsingleton A] [Subsingleton B] (f : A →+ B) :
    Function.Bijective f :=
  ⟨fun x y _ => Subsingleton.elim x y, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end LateralTheory.E.EqvQAPf

open LateralTheory.E.t_E1Cut in
theorem LateralTheory.E.t_E1Cut.EqvQA_of (hAcyc : AcycQA) (hQA : QAClosed) (hH0 : EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions) (hLC : LCGood) : EqvQA := by
  intro h1 h9 hb1 hb2 q _ S _ J hS hJ hq i n
  have hqJ : IsUnit (q : S ⧸ J) := by simpa using hq.map (Ideal.Quotient.mk J)
  have hSJ : QA (S ⧸ J) := (hQA S hS).2.2 J
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (h9 (ZMod q) (tw q i)).1 (sp S) n hn
    haveI := (h9 (ZMod q) (tw q i)).1 (sp (S ⧸ J)) n hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
  · obtain ⟨ζ⟩ := LateralTheory.E.EqvQAPf.prim_of_aic q S (hQA S hS).1 hq
    obtain ⟨e, he⟩ := hH0 h9 q i
    have key : ∀ φ, pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0 (e S ζ φ) =
        e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J)) (lcMap (Ideal.Quotient.mk J) φ) :=
      fun φ => he S (S ⧸ J) (Ideal.Quotient.mk J) ζ φ
    have hcomp : (pull _ (spMap (Ideal.Quotient.mk J)) (tw q i) 0) =
        (e (S ⧸ J) (ζ.map (Ideal.Quotient.mk J))) ∘
          (fun φ => lcMap (Ideal.Quotient.mk J) φ) ∘ (e S ζ).symm := by
      funext x
      obtain ⟨φ, rfl⟩ := (e S ζ).surjective x
      simp only [Function.comp_apply, AddEquiv.symm_apply_apply]
      exact key φ
    rw [hcomp]
    exact (e _ _).bijective.comp ((hLC S J hJ (ZMod q)).comp (e S ζ).symm.bijective)
  · haveI := hAcyc h1 h9 hb1 hb2 q S hS hq n i hn
    haveI := hAcyc h1 h9 hb1 hb2 q (S ⧸ J) hSJ hqJ n i hn
    exact LateralTheory.E.EqvQAPf.bij_of_sub _
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAICPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.EtAICPf

def Split : Prop := ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], AIC T →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j))

def DomOpen : Prop := ∀ (T D : Type) [CommRing T] [IsDomain T] [CommRing D] [IsDomain D] [Algebra T D] [Algebra.Etale T D],
  AIC T → IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap T D)))

theorem EtAIC_of (hS : Split) (hD : DomOpen) : LateralTheory.E.t_E1Cut.EtAIC := by
  intro T C _ _ _ _ _ hT
  obtain ⟨n, e, he, hdom⟩ := hS T C hT
  refine ⟨n, e, he, fun j => ?_⟩
  have : Algebra.Etale C (Localization.Away (e j)) := inferInstance
  have : Algebra.Etale T (Localization.Away (e j)) := Algebra.Etale.comp T C _
  have h := hD T (Localization.Away (e j)) hT
  rwa [IsScalarTower.algebraMap_eq T C (Localization.Away (e j))] at h

end LateralTheory.E.EtAICPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.FinEtSectionPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.FinEtSectionPf

def Pieces : Prop := LateralTheory.E.t_E1Cut.EtLift → LateralTheory.E.t_E1Cut.EtAIC → ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Algebra.Etale S C], LateralTheory.E.t_E1Cut.QA S →
  ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j,
    IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))))

def FinOpen : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] [Module.Finite S C] (e : C), IsIdempotentElem e →
  IsOpenImmersion (Spec.map (CommRingCat.ofHom ((algebraMap C (Localization.Away e)).comp (algebraMap S C)))) →
  ∃ ε : S, IsIdempotentElem ε ∧
    Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away e)).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum S)) ∧
    ∃ h : Localization.Away e →+* Localization.Away ε,
      h.comp ((algebraMap C (Localization.Away e)).comp (algebraMap S C)) = algebraMap S (Localization.Away ε)

def Glue : Prop := ∀ (S C : Type) [CommRing S] [CommRing C] [Algebra S C] (n : ℕ) (e : Fin n → C),
  CompleteOrthogonalIdempotents e → Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) →
  ∀ ε : Fin n → S, (∀ j, IsIdempotentElem (ε j)) →
  (∀ j, Set.range (PrimeSpectrum.comap ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C))) =
      (PrimeSpectrum.basicOpen (ε j) : Set (PrimeSpectrum S))) →
  (∀ j, ∃ h : Localization.Away (e j) →+* Localization.Away (ε j),
      h.comp ((algebraMap C (Localization.Away (e j))).comp (algebraMap S C)) = algebraMap S (Localization.Away (ε j))) →
  Nonempty (C →ₐ[S] S)

theorem FinEtSection_of (hL : LateralTheory.E.t_E1Cut.EtLift) (hA : LateralTheory.E.t_E1Cut.EtAIC) (hP : Pieces) (hF : FinOpen) (hG : Glue) : LateralTheory.E.t_E1Cut.FinEtSection := by
  intro S C _ _ _ _ _ hQA hsurj
  obtain ⟨n, e, he, hoi⟩ := hP hL hA S C hQA
  choose ε hε hr hh using fun j => hF S C (e j) (he.idem j) (hoi j)
  exact hG S C n e he hsurj ε hε hr hh

end LateralTheory.E.FinEtSectionPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HensIdemCut
section
noncomputable section
open Polynomial

namespace LateralTheory.E.HensIdemCut

def LJac : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → I.map φ ≤ Ideal.jacobson ⊥

def LMonic : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  φ.IsIntegral → ∀ b : B, b * b - b ∈ I.map φ → ∃ (N : ℕ) (f : A[X]), f.Monic ∧ f.eval₂ φ b = 0 ∧
    f.map (Ideal.Quotient.mk I) = X ^ N * (X - C 1) ^ N

def LFactor : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (f : A[X]) (g₀ h₀ : (A ⧸ I)[X]),
  f.Monic → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ → f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
  ∃ g h : A[X], g.Monic ∧ h.Monic ∧ f = g * h ∧ g.map (Ideal.Quotient.mk I) = g₀ ∧ h.map (Ideal.Quotient.mk I) = h₀

def LIdem : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) (B : Type) [CommRing B] (φ : A →+* B),
  I.map φ ≤ Ideal.jacobson ⊥ → ∀ (b : B), b * b - b ∈ I.map φ → ∀ (N : ℕ) (g h : A[X]),
  g.map (Ideal.Quotient.mk I) = X ^ N → h.map (Ideal.Quotient.mk I) = (X - C 1) ^ N →
  g.eval₂ φ b * h.eval₂ φ b = 0 → ∃ x : B, IsIdempotentElem x ∧ x - b ∈ I.map φ

theorem goal_of (hJ : LJac) (hM : LMonic) (hF : LFactor) (hI : LIdem) : LateralTheory.E.t_E1Cut.HensIdem := by
  intro A _ I _ B _ φ hφ
  refine ⟨hJ A I B φ hφ, ?_⟩
  intro e he
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective e
  have hb : b * b - b ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simpa [IsIdempotentElem] using he
  obtain ⟨N, f, hfm, hf0, hfI⟩ := hM A I B φ hφ b hb
  have hcop : IsCoprime ((X : (A ⧸ I)[X]) ^ N) ((X - C 1) ^ N) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - C 1) from ⟨1, -1, by rw [C_1]; ring⟩).pow
  obtain ⟨g, h, -, -, rfl, hg, hh⟩ :=
    hF A I f _ _ hfm ((monic_X).pow N) ((monic_X_sub_C 1).pow N) hcop hfI
  obtain ⟨x, hx, hxb⟩ := hI A I B φ (hJ A I B φ hφ) b hb N g h hg hh (by rw [← eval₂_mul]; exact hf0)
  exact ⟨x, hx, Ideal.Quotient.eq.mpr hxb⟩

end LateralTheory.E.HensIdemCut
end
end

