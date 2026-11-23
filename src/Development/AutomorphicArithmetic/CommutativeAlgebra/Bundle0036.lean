module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0070
public import Development.EtaleCohomology.EtaleSheaves.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0034
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMayerVietorisConnectingExact
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0027
public import Development.EtaleCohomology.EtaleTrace.LocalSplitting.Cover2
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.EtaleCohomology.EtaleSheaves.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyClassKilledOnNbhdPair
section
open CategoryTheory Limits

namespace UpperTheory.NaturalityElementwise

variable {J : Type} [SmallCategory J]

private lemma sq_el {A B C D : AddCommGrpCat.{1}} {p : A ⟶ B} {q : B ⟶ D} {r : A ⟶ C} {s : C ⟶ D}
    (h : p ≫ q = r ≫ s) (x : A) : q.hom (p.hom x) = s.hom (r.hom x) := by
  have := congrArg (fun g => g.hom x) h
  simpa using this

private lemma nat_el {F G : J ⥤ AddCommGrpCat.{1}} (η : F ⟶ G) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (η.app b).hom ((F.map f).hom x) = (G.map f).hom ((η.app a).hom x) :=
  sq_el (η.naturality f) x

private lemma w_el {F : J ⥤ AddCommGrpCat.{1}} (c : Cocone F) {a b : J} (f : a ⟶ b) (x : F.obj a) :
    (c.ι.app b).hom ((F.map f).hom x) = (c.ι.app a).hom x := by
  have := congrArg (fun g => g.hom x) (c.w f)
  simpa using this

private lemma comp_el {F : J ⥤ AddCommGrpCat.{1}} {a b c : J} (f : a ⟶ b) (g : b ⟶ c) (x : F.obj a) :
    (F.map (f ≫ g)).hom x = (F.map g).hom ((F.map f).hom x) := by
  simp

end UpperTheory.NaturalityElementwise

open UpperTheory.NaturalityElementwise in
theorem UpperTheory.etaleCohomology_class_killed_on_nbhd_pair :
    LateralTheory.E.NeighbourhoodKilling.PairFive := by
  intro J _ _ T j x hx

  have h0 : (T.cYm.ι.app j).hom ((T.fg.app j).hom x) = 0 := by
    rw [← sq_el (T.fg_w j) x, hx, map_zero]
  obtain ⟨j1, f1, h1⟩ := T.injYm j _ h0

  have h2 : (T.fg.app j1).hom ((T.Rm.map f1).hom x) = 0 := by
    rw [nat_el T.fg f1 x, h1]
  obtain ⟨w, hw⟩ := T.exR j1 _ h2

  have h3 : T.dlL.hom ((T.cWp.ι.app j1).hom w) = 0 := by
    rw [sq_el (T.dl_w j1) w, hw, w_el T.cR f1 x, hx]
  obtain ⟨y, hy⟩ := T.exWL _ h3
  obtain ⟨j2, y', rfl⟩ := T.surYp y

  let a : j1 ⟶ IsFiltered.max j1 j2 := IsFiltered.leftToMax j1 j2
  let b : j2 ⟶ IsFiltered.max j1 j2 := IsFiltered.rightToMax j1 j2
  have h4 : (T.cWp.ι.app _).hom ((T.Wp.map a).hom w - (T.rs.app _).hom ((T.Yp.map b).hom y')) = 0 := by
    rw [map_sub, w_el T.cWp a w, ← sq_el (T.rs_w _) ((T.Yp.map b).hom y'), w_el T.cYp b y', hy,
      sub_self]
  obtain ⟨j4, c, h5⟩ := T.injWp _ _ h4
  refine ⟨j4, f1 ≫ a ≫ c, ?_⟩
  have h6 : (T.Wp.map c).hom ((T.Wp.map a).hom w)
      = (T.rs.app j4).hom ((T.Yp.map c).hom ((T.Yp.map b).hom y')) := by
    rw [map_sub, sub_eq_zero] at h5
    rw [h5, nat_el T.rs c]
  rw [comp_el, ← hw, comp_el, ← nat_el T.dl a w, ← nat_el T.dl c, h6]
  exact T.cx j4 _
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsEtaleNbhdPrimitiveRootOfIsUnitNatCast
section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

private theorem evalRoot {A : Type} [CommRing A] (q : ℕ) :
    Polynomial.eval (AdjoinRoot.root (Polynomial.cyclotomic q A))
      (Polynomial.cyclotomic q (AdjoinRoot (Polynomial.cyclotomic q A))) = 0 := by
  rw [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
    Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

private theorem unitDeriv {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    IsUnit (AdjoinRoot.mk (Polynomial.cyclotomic q A)
      (Polynomial.derivative (Polynomial.cyclotomic q A))) := by
  rcases subsingleton_or_nontrivial (AdjoinRoot (Polynomial.cyclotomic q A)) with h | h
  · exact isUnit_of_subsingleton _
  · have hq' : IsUnit ((q : ℕ) : AdjoinRoot (Polynomial.cyclotomic q A)) := by
      simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))
    have := LateralTheory.E.LeafClosedSH0PfPrim.derivUnit q _ hq' (evalRoot q)
    rwa [← Polynomial.map_cyclotomic q (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))),
      Polynomial.derivative_map, Polynomial.eval_map_algebraMap, AdjoinRoot.aeval_eq] at this

private theorem injOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.of, RingHom.comp_apply, AdjoinRoot.mk_eq_zero] at ha
  refine (Polynomial.cyclotomic.monic q A).not_dvd_of_degree_lt
    (Polynomial.C_ne_zero.2 h0) ?_ ha
  rw [Polynomial.degree_cyclotomic, Polynomial.degree_C h0]
  exact_mod_cast Nat.totient_pos.2 (NeZero.pos q)

private theorem surjOf {A : Type} [CommRing A] [Nontrivial A] (q : ℕ) [NeZero q] :
    Function.Surjective
      (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A)))) := by
  intro p
  have := (Polynomial.cyclotomic.monic q A).finite_adjoinRoot
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := AdjoinRoot (Polynomial.cyclotomic q A)) p.asIdeal ⊥ (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 (injOf q)]
      exact bot_le)
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩

private noncomputable def rootPrim {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit ((q : ℕ) : A)) :
    Prim q (AdjoinRoot (Polynomial.cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (Polynomial.cyclotomic q A))), by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
    exact evalRoot q⟩

theorem UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}), IsUnit ((q : ℕ) : Γ(X, ⊤)) → ∀ x : X, ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (_ : Prim q Γ(V, ⊤)), f y = x := by
  intro q _ X hq x
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  obtain ⟨p, hp⟩ : x ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hxW
  have hnt : Nontrivial Γ(X, W) := by
    rcases subsingleton_or_nontrivial Γ(X, W) with h | h
    · exact absurd (Subsingleton.elim _ _) p.2.ne_top
    · exact h
  have hqW : IsUnit ((q : ℕ) : Γ(X, W)) := by
    simpa using hq.map (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
  have het : Algebra.Etale Γ(X, W) (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    GlobalTheory.etale_adjoinRoot_of_isUnit_derivative (Polynomial.cyclotomic.monic q _) (unitDeriv q hqW)
  let φ : CommRingCat.of Γ(X, W) ⟶ CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W))) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 ((RingHom.etale_algebraMap).2 het)
  obtain ⟨y0, hy0⟩ := surjOf (A := Γ(X, W)) q p
  let y : Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))) := y0
  have hy : Spec.map φ y = p := hy0
  refine ⟨Spec (CommRingCat.of (AdjoinRoot (Polynomial.cyclotomic q Γ(X, W)))),
    Spec.map φ ≫ hW.fromSpec, inferInstance, y,
    Prim.map (Scheme.ΓSpecIso _).inv.hom (rootPrim q hqW), ?_⟩
  rw [Scheme.Hom.comp_apply, hy, hp]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPrimitiveFreeOfAcyLocallyExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

private theorem sec_comp {F G H : Shv ℤ} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_zero {F G : Shv ℤ} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

private theorem UpperTheory.sec_map_res_comm {F G : Shv ℤ} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U)
    (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  show (φ.hom.app (op V)).hom ((F.obj.map g.op).hom x) =
    (G.obj.map g.op).hom ((φ.hom.app (op U)).hom x)
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, φ.hom.naturality]

private theorem UpperTheory.injective_sec_map_of_mono {F G : Shv ℤ} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (fun x : Sec F U => Sec.map φ x) := by
  have : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

private theorem UpperTheory.acy_of_isZero (Q : Scheme.{0} → Prop) (G : Shv ℤ) (hG : IsZero G) :
    Acy Q G := by
  intro P hP n _
  have hid : (𝟙 G : G ⟶ G) = 0 := hG.eq_of_src _ _
  have hsub : ∀ {U : Scheme.{0}} (x : Sec G U), x = 0 := fun {U} x => by
    calc x = Sec.map (𝟙 G) x := rfl
      _ = 0 := by rw [hid, sec_zero]
  exact UpperTheory.subsingleton_hypercohomology_free_of_supp_of_sections_vanish Q G (fun U _ => ⟨fun x y => by rw [hsub x, hsub y]⟩) P hP n

theorem UpperTheory.exists_primitive_free_of_acy_locally_exact :
    ∀ (C : Cx ℤ) (a : ℤ) [C.IsStrictlyGE a] (Q : Scheme.{0} → Prop), (∀ {V U : Scheme.{0}}, (V ⟶ U) → Q U → Q V) → (∀ s, Acy Q (C.X s)) → (∀ (U : Scheme.{0}), Q U → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ c : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) c = Sec.res g b) → ∀ P : PSh, Supp Q P → ∀ (j : ℤ) (f : (free ℤ).obj P ⟶ C.X j), f ≫ C.d j (j + 1) = 0 → ∃ g : (free ℤ).obj P ⟶ C.X (j - 1), g ≫ C.d (j - 1) j = f := by
  intro C a _ Q hQ hacy hexact P hP j f hf
  have step : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) →
      Acy Q (kernel (C.d (i + 1) (i + 1 + 1))) ∧ ∀ P : PSh, Supp Q P →
        ∀ f : (free ℤ).obj P ⟶ kernel (C.d (i + 1) (i + 1 + 1)),
          ∃ h, h ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
            (C.d_comp_d _ _ _) = f := by
    intro i hi
    have w : kernel.ι (C.d i (i + 1)) ≫ kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
        (C.d_comp_d _ _ _) = 0 := by
      rw [← cancel_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp]
    have hex : (ShortComplex.mk (kernel.ι (C.d i (i + 1)))
        (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _)) w).Exact := by
      apply ShortComplex.exact_of_f_is_kernel
      refine KernelFork.IsLimit.ofι _ _
        (fun g' hg' => kernel.lift (C.d i (i + 1)) g' (by
          rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
            ← Category.assoc, hg', zero_comp]))
        (fun g' hg' => kernel.lift_ι _ _ _)
        (fun g' hg' m hm => by
          rw [← cancel_mono (kernel.ι (C.d i (i + 1))), kernel.lift_ι]
          exact hm)
    have hloc : ∀ U : Scheme.{0}, Q U → ∀ b : Sec (kernel (C.d (i + 1) (i + 1 + 1))) U,
        Loc U fun V g => ∃ c, Sec.map (kernel.lift (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1))
          (C.d_comp_d _ _ _)) c = Sec.res g b := by
      intro U hU b
      have hb : Sec.map (C.d (i + 1) (i + 1 + 1))
          (Sec.map (kernel.ι (C.d (i + 1) (i + 1 + 1))) b) = 0 := by
        rw [← sec_comp, kernel.condition, sec_zero]
      have h1 := hexact U hU (i + 1) _ hb
      rw [show i + 1 - 1 = i by omega] at h1
      obtain ⟨S, hS, hSp⟩ := h1
      refine ⟨S, hS, fun V g hg => ?_⟩
      obtain ⟨c, hc⟩ := hSp V g hg
      refine ⟨c, UpperTheory.injective_sec_map_of_mono (kernel.ι (C.d (i + 1) (i + 1 + 1))) V ?_⟩
      show Sec.map _ (Sec.map _ c) = Sec.map _ (Sec.res g b)
      rw [← sec_comp, kernel.lift_ι, hc, UpperTheory.sec_map_res_comm]
    exact UpperTheory.acy_and_lift_of_locally_surjective_exact Q @hQ _ _ _ _ _ w inferInstance hex hloc hi (hacy i)
  have hAcy : ∀ i : ℤ, Acy Q (kernel (C.d i (i + 1))) := by
    intro i
    have below (n : ℤ) (hn : n < a) : Acy Q (kernel (C.d n (n + 1))) :=
      UpperTheory.acy_of_isZero Q _
        (IsZero.of_mono (kernel.ι _) (isZero_of_isStrictlyGE C a n hn))
    refine Int.inductionOn' (motive := fun n => Acy Q (kernel (C.d n (n + 1)))) i (a - 1)
      (below (a - 1) (by omega)) (fun n _ ih => (step n ih).1) ?_
    intro n hn _
    exact below (n - 1) (by omega)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [show i + 1 - 1 = i by omega]
  obtain ⟨h, hh⟩ := (step i (hAcy i)).2 P hP (kernel.lift _ f hf)
  refine ⟨h, ?_⟩
  rw [← kernel.lift_ι (C.d (i + 1) (i + 1 + 1)) (C.d i (i + 1)) (C.d_comp_d _ _ _),
    ← Category.assoc, hh, kernel.lift_ι]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.H1PlEqZeroOfLeISupOfLocalZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.SeparatedH1Cohomology

private theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (k : V ⟶ U) (n : ℕ)
    (a : Sec F U) : Sec.res k (n • a) = n • Sec.res k a :=
  map_nsmul (F.obj.map k.op).hom n a

private theorem exists_h0_restriction_eq_of_le_open {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] {O P : E.Opens} (h : P ≤ O) (c : Ht q (sch.obj P) 0 1) :
    ∃ a : Ht q (sch.obj O) 0 1, pl q 1 (E.homOfLE h) 0 a = c := by
  obtain ⟨-, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero (ZMod q) (tw q 1)
  by_cases hP : Nonempty (P : Scheme.{0})
  · haveI : IsIntegral (P : Scheme.{0}) := isIntegral_of_isOpenImmersion (P.ι ≫ j)
    haveI : ConnectedSpace (P : Scheme.{0}) := inferInstance
    obtain ⟨k, hk⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q 1 (P : Scheme.{0}) (ζ.map (P.ι ≫ j).appTop.hom) ((e P).symm c)
    refine ⟨e O (k • twGen 1 (ζ.map (O.ι ≫ j).appTop.hom)), ?_⟩
    have h1 : c = e P (k • twGen 1 (ζ.map (P.ι ≫ j).appTop.hom)) := by
      rw [← hk, AddEquiv.apply_symm_apply]
    have hk : E.homOfLE h ≫ O.ι ≫ j = P.ι ≫ j := by simp
    rw [h1, he, res_nsmul', (GlobalTheory.T.tateTwist_sections_locally_generated q 1).2.2.2.1, ← hk]
    congr 1
  · have hb : P = ⊥ := le_bot_iff.1 fun p hp => (hP ⟨(⟨p, hp⟩ : P)⟩).elim
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := E) (tw q 1) 0
    exact ⟨0, Subsingleton.elim _ _⟩

private theorem two {q : ℕ} [NeZero q] {X E : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (j : E ⟶ X) [IsOpenImmersion j] (O₁ O₂ : E.Opens) (hcov : O₁ ⊔ O₂ = ⊤) (y : Ht q (sch.obj E) 1 1)
    (h₁ : pl q 1 O₁.ι 1 y = 0) (h₂ : pl q 1 O₂.ι 1 y = 0) : y = 0 := by
  obtain ⟨d, hd, -⟩ := UpperTheory.Cb.exists_mayerVietoris_connecting_exact (ZMod q) (tw q 1)
  have hc : Cover2 (ZMod q) (sch.map O₁.ι) (sch.map O₂.ι) := LateralTheory.EtaleTrace.LSplitPf.Sch.cover2 (ZMod q) O₁ O₂ hcov
  have : PreservesLimitsOfShape WalkingCospan sch := by
    unfold sch
    infer_instance
  let e := ((isPullback_opens_inf O₁ O₂).map sch).isoPullback
  obtain ⟨-, hz, hx⟩ := hd _ _ hc 0
  obtain ⟨c, hcy⟩ := (hx y).1 ⟨h₁, h₂⟩
  obtain ⟨a, ha⟩ := exists_h0_restriction_eq_of_le_open ζ j (inf_le_left : O₁ ⊓ O₂ ≤ O₁) (pull (ZMod q) e.hom (tw q 1) 0 c)
  have hf : pullback.fst (sch.map O₁.ι) (sch.map O₂.ι) = e.inv ≫ sch.map (E.homOfLE inf_le_left) := by
    simp [e]
  have h0 : d _ _ hc 0 c = 0 := by
    refine (hz c).2 ⟨a, 0, ?_⟩
    rw [map_zero, sub_zero, hf, pull_comp]
    change c = pull _ e.inv _ 0 (pl q 1 _ 0 a)
    rw [ha, ← pull_comp, e.inv_hom_id, pull_id]
  exact hcy.symm.trans h0

private theorem step {q : ℕ} [NeZero q] {X : Scheme.{0}} [IsIntegral X] (ζ : Prim q Γ(X, ⊤))
    (A B : X.Opens) (x : Ht q (sch.obj X) 1 1) (hA : pl q 1 A.ι 1 x = 0) (hB : pl q 1 B.ι 1 x = 0) :
    pl q 1 (A ⊔ B).ι 1 x = 0 := by
  have key : ∀ C : X.Opens, pl q 1 C.ι 1 x = 0 →
      pl q 1 ((A ⊔ B).ι ⁻¹ᵁ C).ι 1 (pl q 1 (A ⊔ B).ι 1 x) = 0 := by
    intro C hC
    have h1 : ((A ⊔ B).ι ⁻¹ᵁ C).ι ≫ (A ⊔ B).ι = ((A ⊔ B).ι ∣_ C) ≫ C.ι := (morphismRestrict_ι _ _).symm
    change pull _ _ _ _ (pull _ _ _ _ x) = 0
    rw [← pull_comp, ← sch.map_comp, h1, sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 C.ι 1 x) = 0
    rw [hC, map_zero]
  refine two ζ (A ⊔ B).ι ((A ⊔ B).ι ⁻¹ᵁ A) ((A ⊔ B).ι ⁻¹ᵁ B) ?_ _ (key A hA) (key B hB)
  refine eq_top_iff.2 fun p _ => ?_
  have hp : (A ⊔ B).ι p ∈ A ⊔ B := p.2
  exact TopologicalSpace.Opens.mem_sup.2 (TopologicalSpace.Opens.mem_sup.1 hp)

end UpperTheory.Cb.SeparatedH1Cohomology

theorem UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (V : X.Opens), V ≤ ⨆ i, U i → ∀ x : Ht q (sch.obj X) 1 1, (∀ i, pl q 1 (U i).ι 1 x = 0) → pl q 1 V.ι 1 x = 0 := by
  intro q _ X _ hζ _ n
  obtain ⟨ζ⟩ := hζ
  induction n with
  | zero =>
    intro U V hV x _
    have hb : V = ⊥ := le_bot_iff.1 (hV.trans (iSup_of_empty U).le)
    subst hb
    haveI := LateralTheory.E.E8.leafEmptyVanish (ZMod q) (X := X) (tw q 1) 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    intro U V hV x hx
    have hW := ih (fun i => U i.castSucc) (⨆ i : Fin n, U i.castSucc) le_rfl x (fun i => hx _)
    have hS := UpperTheory.Cb.SeparatedH1Cohomology.step ζ _ _ x hW (hx (Fin.last n))
    have hle : V ≤ (⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n) := hV.trans (iSup_le fun i => by
      induction i using Fin.lastCases with
      | last => exact le_sup_right
      | cast i => exact le_sup_of_le_left (le_iSup (fun i : Fin n => U i.castSucc) i))
    have hι : V.ι = X.homOfLE hle ≫ ((⨆ i : Fin n, U i.castSucc) ⊔ U (Fin.last n)).ι := by simp
    rw [hι]
    change pull _ (sch.map _) _ _ x = 0
    rw [sch.map_comp, pull_comp]
    change pull _ _ _ _ (pl q 1 _ 1 x) = 0
    rw [hS, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFiniteFromNormalizationOfPerfectField
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

theorem UpperTheory.isFinite_fromNormalization_of_perfectField :
    ∀ (k : Type) [Field k] [PerfectField k] {D T : Scheme.{0}} (t : T ⟶ Sp k) [LocallyOfFiniteType t] (f : D ⟶ T) [LocallyOfFiniteType f] [QuasiCompact f] [QuasiSeparated f] [IsIntegral D], IsFinite f.fromNormalization := by
  intro k _ _ D T t _ f _ _ _ _
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  rw [f.fromNormalization_app hU]
  letI := (f.app U).hom.toAlgebra
  have h : Module.Finite Γ(T, U) (integralClosure Γ(T, U) Γ(D, f ⁻¹ᵁ U)) := by
    rcases (f ⁻¹ᵁ U).1.eq_empty_or_nonempty with hE | hN
    · have hb : f ⁻¹ᵁ U = ⊥ := SetLike.ext' hE
      haveI : Subsingleton Γ(D, f ⁻¹ᵁ U) :=
        CommRingCat.subsingleton_of_isTerminal (D.sheaf.isTerminalOfEqEmpty hb)
      infer_instance
    · obtain ⟨x, hx⟩ := hN
      obtain ⟨V, hV, hxV, hVle⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp D.isBasis_affineOpens) hx
      haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
      haveI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, hx⟩⟩
      have hkt : (t.appLE ⊤ U (by simp)).hom.FiniteType :=
        LocallyOfFiniteType.finiteType_appLE t (isAffineOpen_top _) hU (by simp)
      let kA : k →+* Γ(T, U) :=
        (t.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      have hkA : kA.FiniteType :=
        hkt.comp (RingHom.FiniteType.of_surjective _
          (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective)
      letI : Algebra k Γ(T, U) := kA.toAlgebra
      haveI : Algebra.FiniteType k Γ(T, U) := hkA
      haveI : IsNoetherianRing Γ(T, U) := Algebra.FiniteType.isNoetherianRing k Γ(T, U)
      have heq : (D.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom =
          (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom := by
        rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
        congr 1
        simp [Scheme.Hom.appLE]
      let φ : Γ(T, U) →+* D.functionField :=
        (D.germToFunctionField V).hom.comp (f.appLE U V hVle).hom
      letI : Algebra Γ(T, U) D.functionField := φ.toAlgebra
      have h1 : (D.germToFunctionField V).hom.EssFiniteType := GlobalTheory.essFiniteType_germ hV _ _
      have h2 : (f.appLE U V hVle).hom.EssFiniteType :=
        (LocallyOfFiniteType.finiteType_appLE f hU hV hVle).essFiniteType
      haveI : Algebra.EssFiniteType Γ(T, U) D.functionField := h2.comp h1
      haveI := UpperTheory.module_finite_integralClosure_of_finiteType_perfect k Γ(T, U) D.functionField
      let ψ : Γ(D, f ⁻¹ᵁ U) →ₐ[Γ(T, U)] D.functionField :=
        { (D.germToFunctionField (f ⁻¹ᵁ U)).hom with
          commutes' := fun a => by
            change (D.germToFunctionField (f ⁻¹ᵁ U)).hom ((f.app U).hom a) = φ a
            exact congrArg (fun g => g a) heq }
      exact GlobalTheory.finite_integralClosure_of_family (ι := Unit) (L := fun _ => D.functionField)
        (fun _ => ψ) (fun b hb => D.germToFunctionField_injective (f ⁻¹ᵁ U)
          (by rw [map_zero]; exact hb ()))
  rw [CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ ?_
  · exact RingHom.Finite.of_surjective _
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective
  · exact (RingHom.finite_algebraMap).mpr h
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.PrimitiveRootEqPowLocally
section
open CategoryTheory AlgebraicGeometry GlobalTheory.EtC

theorem UpperTheory.primitive_root_eq_pow_locally :
    ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] (ξ ζ : Prim q A) (p : Ideal A) [p.IsPrime], ∃ (f : A) (a : (ZMod q)ˣ), f ∉ p ∧ ∀ (B : Type) [CommRing B] (φ : A →+* B), IsUnit (φ f) → φ ξ.1 = (φ ζ.1) ^ (a : ZMod q).val := by
  intro q _ A _ ξ ζ p _
  have hpow : ∀ η : Prim q A, η.1 ^ q = 1 := by
    intro η
    obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have h1 := congrArg (Polynomial.aeval η.1) hg
    simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, map_mul, η.2.2, zero_mul] at h1
    exact sub_eq_zero.mp h1
  have hq' : IsUnit ((q : ℕ) : A ⧸ p) := by
    simpa using ζ.2.1.map (Ideal.Quotient.mk p)
  haveI : NeZero ((q : ℕ) : A ⧸ p) := ⟨hq'.ne_zero⟩
  have prim : ∀ η : Prim q A, IsPrimitiveRoot (Ideal.Quotient.mk p η.1) q := by
    intro η
    have h0 : Ideal.Quotient.mk p (Polynomial.aeval η.1 (Polynomial.cyclotomic q ℤ)) = 0 := by
      rw [η.2.2, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot,
      Polynomial.eval_map]
    have e : (Ideal.Quotient.mk p).comp (algebraMap ℤ A) = Int.castRingHom (A ⧸ p) :=
      RingHom.ext_int _ _
    rw [e] at h0
    exact h0
  obtain ⟨k, hk, hkξ⟩ := (prim ζ).eq_pow_of_pow_eq_one (prim ξ).pow_eq_one
  have hcop : k.Coprime q := ((prim ζ).pow_iff_coprime (NeZero.pos q) k).1 (hkξ ▸ prim ξ)
  have hcq : (ζ.1 ^ k) ^ q = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hpow ζ, one_pow]
  have hf : (∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) * (ξ.1 - ζ.1 ^ k) = 0 := by
    rw [geom_sum₂_mul, hpow ξ, hcq, sub_self]
  refine ⟨∑ i ∈ Finset.range q, ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i), ZMod.unitOfCoprime k hcop, ?_, ?_⟩
  · intro hmem
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hc : Ideal.Quotient.mk p (ζ.1 ^ k) = Ideal.Quotient.mk p ξ.1 := by
      rw [map_pow, hkξ]
    have hcu : IsUnit (Ideal.Quotient.mk p ξ.1) := by
      refine (Units.ofPowEqOne _ q ?_ (NeZero.ne q)).isUnit
      rw [← map_pow, hpow ξ, map_one]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at hz
    have hsum : ∑ i ∈ Finset.range q, Ideal.Quotient.mk p (ξ.1 ^ i * (ζ.1 ^ k) ^ (q - 1 - i)) =
        ∑ i ∈ Finset.range q, (Ideal.Quotient.mk p ξ.1) ^ (q - 1) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_mul, map_pow, map_pow, hc, ← pow_add]
      congr 1
      have := Finset.mem_range.mp hi
      omega
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hz
    exact (hq'.mul (hcu.pow _)).ne_zero hz
  · intro B _ φ hφ
    have h1 := congrArg φ hf
    rw [map_mul, map_zero, hφ.mul_right_eq_zero, map_sub, sub_eq_zero] at h1
    rw [h1, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hk]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.RelativeCohomologyConnectingNaturality
section
open CategoryTheory GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.E4 LateralTheory.E.LeafGhostCut in
theorem UpperTheory.relativeCohomology_connecting_naturality :
    LateralTheory.E.NeighbourhoodKilling.ObsNat := by
  intro q _ U E U' E' f f' u e comm i m w
  obtain ⟨w, rfl⟩ := w.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp only [zcomp, Cocycle.ofHom_coe, Cocycle.mk_coe]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, rmap, LateralTheory.E.GlueRelPfNat.map_fst,
    Cochain.comp_assoc_of_second_is_zero_cochain]
end

