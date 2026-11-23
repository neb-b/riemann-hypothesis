module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamPush
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private noncomputable def sqPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) (A : Sq p) : Sq (h ≫ p) :=
  ⟨A.U, pullback h A.v, A.u, pullback.fst h A.v, pullback.snd h A.v ≫ A.r,
    (IsPullback.of_hasPullback h A.v).paste_vert A.pb⟩

private def resHom {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) : Sec F U →+ Sec F V :=
  (F.obj.map g.op).hom.toAddMonoidHom

private theorem pushK_w {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback.fst h A.v ≫ h = (pullback.snd h A.v ≫ t.k) ≫ B.v := by
  rw [Category.assoc, t.hv]
  exact pullback.condition

private noncomputable def pushK {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pullback h A.v ⟶ pullback h B.v :=
  pullback.lift (pullback.fst h A.v) (pullback.snd h A.v ≫ t.k) (pushK_w h t)

private theorem pushK_fst {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.fst h B.v = pullback.fst h A.v := pullback.lift_fst _ _ _

private theorem pushK_snd {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v = pullback.snd h A.v ≫ t.k := pullback.lift_snd _ _ _

private theorem pushK_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S} {A B : Sq p} (t : A.To B) :
    pushK h t ≫ pullback.snd h B.v ≫ B.r = (pullback.snd h A.v ≫ A.r) ≫ t.g := by
  rw [← Category.assoc, pushK_snd, Category.assoc, t.hr, Category.assoc]

private noncomputable def toPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {A B : Sq p} (t : A.To B) :
    (sqPush h p A).To (sqPush h p B) :=
  ⟨t.g, pushK h t, t.hu, pushK_fst h t, pushK_r h t⟩

private theorem res_pushK {R : Type} [CommRing R] {F : Shv R} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') {p : Z' ⟶ S}
    {A B : Sq p} (t : A.To B) (a : Sec F B.V) :
    Sec.res (pushK h t) (Sec.res (pullback.snd h B.v) a) = Sec.res (pullback.snd h A.v) (Sec.res t.k a) := by
  rw [res_res, res_res, pushK_snd]

private noncomputable def familyPushforward {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {F : Shv R'} {G : Shv R} (τ : Fam0 (h ≫ p) F G) : Fam0 p F G where
  app A := (τ.app (sqPush h p A)).comp (resHom F (pullback.snd h A.v))
  nat {A B} t a := (τ.nat (toPush h p t) (Sec.res (pullback.snd h B.v) a)).trans
    (congrArg (τ.app (sqPush h p A)) (res_pushK h t a))

private noncomputable def famPush {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) {R' R : Type} [CommRing R']
    [CommRing R] {I : Cx R'} {J : Cx R} (τ : Fam (h ≫ p) I J) : Fam p I J where
  deg s := familyPushforward h p (τ.deg s)
  comm A s t a := (τ.comm (sqPush h p A) s t (Sec.res (pullback.snd h A.v) a)).trans
    (congrArg ((τ.deg t).app (sqPush h p A)) (map_res (I.d s t) (pullback.snd h A.v) a))

private theorem sum_push (hS : SumComp) (hF : FibFin) {q : ℕ} {i : ℤ} {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S)
    [IsFinite h] [IsFinite p] (w : Wt Z) (A : Sq p) (a : Sec (tw q i) A.V) (b : Sec (tw q i) A.U)
    (hb : IsSum w (sqPush h p A) (Sec.res (pullback.snd h A.v) a) b) : IsSum (w.push h) A a b := by
  intro Ω _ _ x
  haveI := A.finite
  refine (hb Ω x).trans ((hS (pullback.snd h A.v) A.r Ω x _
    (fun z => w Ω (z ≫ pullback.fst h A.v) • Sec.res z (Sec.res (pullback.snd h A.v) a))).trans ?_)
  refine finsum_congr fun y => finsum_congr fun hy => ?_
  have hfin := hF (pullback.snd h A.v) Ω y
  have hbij := fib_bijOn (IsPullback.of_hasPullback h A.v) (Ω := Ω) y
  have hsum := finsum_mem_eq_of_bijOn (f := fun z => w Ω (z ≫ pullback.fst h A.v))
    (g := fun z' => w Ω z') _ hbij (fun _ _ => rfl)
  show _ = (∑ᶠ (z' : gp Ω ⟶ Z) (_ : z' ∈ fib h (y ≫ A.v)), w Ω z') • Sec.res y a
  rw [← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_smul]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  rw [res_res]
  congr 2

private theorem self_r {Z Z' S : Scheme.{0}} (h : Z ⟶ Z') (p : Z' ⟶ S) :
    pullback.fst h (𝟙 Z') ≫ h ≫ p = (pullback.snd h (𝟙 Z') ≫ p) ≫ 𝟙 S := by
  rw [Category.comp_id, ← Category.assoc, pullback.condition, Category.comp_id]

private theorem res_self {R : Type} [CommRing R] {F : Shv R} {Z Z' : Scheme.{0}} (h : Z ⟶ Z') (a : Sec F Z') :
    Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a) = Sec.res (pullback.snd h (𝟙 Z')) a := by
  rw [res_res, pullback.condition, Category.comp_id]

theorem UpperTheory.Gal.TranscendenceTraces.famPush_of :
    SumComp → FibFin → FamPush := by
  intro hS hF q i Z Z' S h p _ _ w τ hτ
  refine ⟨famPush h p τ, ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb, hbs⟩ := hτ (sqPush h p A) (Sec.res (pullback.snd h A.v) a)
    refine ⟨b, ?_, sum_push hS hF h p w A a b hbs⟩
    show (τ.deg 0).app (sqPush h p A)
      (Sec.res (pullback.snd h A.v) (Sec.map (resι (ZMod q) (tw q i)) a)) = _
    exact (congrArg ((τ.deg 0).app (sqPush h p A)) (map_res _ _ a)).symm.trans hb
  · intro n a
    let t : (sqPush h p (Sq.self p)).To (Sq.self (h ≫ p)) :=
      ⟨𝟙 S, pullback.fst h (𝟙 Z'), Category.id_comp _, Category.comp_id _, self_r h p⟩
    have hn : Sec.res (𝟙 S) ((τ.deg n).app (Sq.self (h ≫ p)) (Sec.res h a)) =
        (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.fst h (𝟙 Z')) (Sec.res h a)) :=
      (τ.deg n).nat t (Sec.res h a)
    show (τ.deg n).app (sqPush h p (Sq.self p)) (Sec.res (pullback.snd h (𝟙 Z')) a) = _
    exact (congrArg ((τ.deg n).app (sqPush h p (Sq.self p))) (res_self h a).symm).trans
      (hn.symm.trans (res_id _))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFinSec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces
open scoped TensorProduct

namespace UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

private theorem sepClosed_of_isAlgebraic (K L : Type) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] [IsSepClosed K] : IsSepClosed L := by
  refine IsSepClosed.of_exists_root _ fun p hm hirr hsep => ?_
  have hdeg : p.degree ≠ 0 := fun h => hirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure L) p hdeg
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L) := Algebra.IsAlgebraic.trans K L _
  haveI : IsPurelyInseparable L (AlgebraicClosure L) :=
    IsPurelyInseparable.tower_top K L (AlgebraicClosure L)
  have hs : IsSeparable L r := Polynomial.Separable.of_dvd hsep (minpoly.dvd L r hr)
  obtain ⟨x, rfl⟩ := IsPurelyInseparable.inseparable' r hs
  refine ⟨x, (algebraMap L (AlgebraicClosure L)).injective ?_⟩
  rw [map_zero, ← hr, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]

private theorem sh_of_finite (O T : Type) [CommRing O] [CommRing T] [Algebra O T]
    [Module.Finite O T] (hO : SH O) (hT : HenselianLocalRing T) : SH T := by
  obtain ⟨hH, hS⟩ := hO
  haveI := hH
  haveI := hT
  refine ⟨hT, ?_⟩
  haveI : IsLocalHom (algebraMap O T) := ⟨fun a ha => by
    by_contra h
    have h1 : a ∈ IsLocalRing.maximalIdeal O := h
    rw [← GlobalTheory.comap_eq_maximalIdeal_of_finite (IsLocalRing.maximalIdeal T)] at h1
    exact (Ideal.mem_comap.1 h1) ha⟩
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap O T)).toAlgebra
  haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨p, hp, h0⟩ := Algebra.IsIntegral.isIntegral (R := O) t
    refine IsIntegral.isAlgebraic ⟨p.map (IsLocalRing.residue O), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have h2 : (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField T)).comp
        (IsLocalRing.residue O) = (IsLocalRing.residue T).comp (algebraMap O T) := rfl
    rw [h2, ← Polynomial.hom_eval₂, h0, map_zero]
  exact sepClosed_of_isAlgebraic (IsLocalRing.ResidueField O) _

private theorem exists_ringHom (hS : SHSec) (B C T : Type) [CommRing B] [CommRing C] [CommRing T]
    [Algebra B C] [Algebra.Etale B C] [Module.FaithfullyFlat B C] [Algebra B T] (hT : SH T) :
    ∃ f : C →+* T, ∀ b, f (algebraMap B C b) = algebraMap B T b := by
  obtain ⟨s⟩ := hS T (T ⊗[B] C) hT
  refine ⟨s.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C).toRingHom, fun b => ?_⟩
  have h1 : (Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b) =
      algebraMap T (T ⊗[B] C) (algebraMap B T b) := by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply B T (T ⊗[B] C)]
  change s ((Algebra.TensorProduct.includeRight : C →ₐ[B] T ⊗[B] C) (algebraMap B C b)) = _
  rw [h1]
  exact s.commutes _

end UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable

open UpperTheory.Gal.TranscendenceTraces.FiniteSectionsSeparable in
theorem UpperTheory.Gal.TranscendenceTraces.finSec_of :
    SHSec → FinSec := by
  intro hS O B C _ _ _ _ _ _ _ _ hO
  obtain ⟨hH, -⟩ := id hO
  haveI := hH
  obtain ⟨ι, _, T, _, _, e, hT⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing O B
  have key : ∀ i, ∃ f : C →+* T i, ∀ b, f (algebraMap B C b) = e b i := by
    intro i
    haveI := (hT i).2
    have hs := sh_of_finite O (T i) hO (hT i).1
    letI : Algebra B (T i) := ((Pi.evalRingHom T i).comp (e : B →+* Π i, T i)).toAlgebra
    exact exists_ringHom hS B C (T i) hs
  choose f hf using key
  refine ⟨{ toRingHom := (e.symm : (Π i, T i) →+* B).comp (Pi.ringHom f), commutes' := fun b => ?_ }⟩
  have h : Pi.ringHom f (algebraMap B C b) = e b := funext fun i => hf i b
  change e.symm (Pi.ringHom f (algebraMap B C b)) = b
  rw [h]
  exact e.symm_apply_apply b
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFunSec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem res_zsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ℤ) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := by
  simp

private theorem sec_eq_of_isEmpty {R : Type} [CommRing R] {F : Shv R} (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b :=
  (_root_.GlobalTheory.EtC.sec_ext_glue R F W).1 a b (GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.2 W _)

theorem UpperTheory.Gal.TranscendenceTraces.funSec_of :
    FunSec := by
  intro q _ i U ζ φ hφ
  let V : ℤ → U.Opens := fun n => ⟨{x | φ x = n}, hφ.isOpen_fiber n⟩
  have hmem : ∀ (n : ℤ) (v : (V n : Scheme)), φ ((V n).ι v) = n := by
    intro n v
    have h1 : (V n).ι v ∈ Set.range (V n).ι := ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  have hcov : ∀ u : U, ∃ n, ∃ v, (V n).ι v = u := by
    intro u
    refine ⟨φ u, ?_⟩
    have h1 : u ∈ Set.range (V (φ u)).ι := by
      rw [Scheme.Opens.range_ι]
      exact rfl
    exact h1
  obtain ⟨y, hy⟩ := (_root_.GlobalTheory.EtC.sec_sep_glue_of_points (ZMod q) (tw q i) U ℤ (fun n => (V n : Scheme)) (fun n => (V n).ι)
    (fun n => inferInstance) hcov).2 (fun n => n • Sec.res (V n).ι (twGen i ζ)) (by
      intro n m
      by_cases h : n = m
      · subst h
        rw [res_zsmul, res_zsmul, res_res, res_res, pullback.condition]
      · haveI : IsEmpty ↥(pullback (V n).ι (V m).ι) := by
          refine ⟨fun p => h ?_⟩
          have e1 := hmem n (pullback.fst (V n).ι (V m).ι p)
          have e2 := hmem m (pullback.snd (V n).ι (V m).ι p)
          have hc : (V n).ι (pullback.fst (V n).ι (V m).ι p) =
              (V m).ι (pullback.snd (V n).ι (V m).ι p) :=
            congrArg (fun f : pullback (V n).ι (V m).ι ⟶ U => f p) pullback.condition
          rw [hc] at e1
          exact e1.symm.trans e2
        exact sec_eq_of_isEmpty _ _ _)
  refine ⟨y, ?_⟩
  intro Ω _ _ x
  have hr : Set.range x ⊆ Set.range (V (φ (pt x))).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show φ (x s) = φ (pt x)
    rw [pt_eq]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ (V (φ (pt x))).ι = x := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  calc Sec.res x y = Sec.res (k ≫ (V (φ (pt x))).ι) y := by rw [hk]
    _ = Sec.res k ((φ (pt x)) • Sec.res (V (φ (pt x))).ι (twGen i ζ)) := by
        rw [← res_res, hy]
    _ = φ (pt x) • Sec.res x (twGen i ζ) := by rw [res_zsmul, res_res, hk]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGalTrans
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_pow_mem_of_fixed (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Normal K L] (q : ℕ) [ExpChar K q] (x : L) (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ n, x ^ q ^ n ∈ (algebraMap K L).range := by
  classical
  rw [← mem_perfectClosure_iff_pow_mem q, mem_perfectClosure_iff_natSepDegree_eq_one]
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hspl : ((minpoly K x).map (algebraMap K L)).Splits := Normal.splits inferInstance x
  rw [Polynomial.natSepDegree_eq_of_splits _ hspl, Finset.card_eq_one]
  refine ⟨x, ?_⟩
  ext y
  simp only [Multiset.mem_toFinset, Polynomial.mem_aroots, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' hint.isAlgebraic hy
    rw [← hσ, hx σ]
  · intro h
    rw [h]
    exact ⟨minpoly.ne_zero hint, minpoly.aeval K x⟩

private lemma fixed_pow_mem (A L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] (q : ℕ) [ExpChar (FractionRing A) q] (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) :
    ∃ (n : ℕ) (a : A), b ^ q ^ n = algebraMap A (integralClosure A L) a := by
  have hx : ∀ σ : L ≃ₐ[FractionRing A] L, σ (b : L) = b := fun σ => by
    have h := algebraMap_galRestrict_apply A (K := FractionRing A) (L := L)
      (B := integralClosure A L) σ b
    rw [hb] at h
    exact h.symm
  obtain ⟨n, k, hk⟩ := exists_pow_mem_of_fixed (FractionRing A) L q (b : L) hx
  have hint : IsIntegral A (algebraMap (FractionRing A) L k) := by
    rw [hk]
    exact (b ^ q ^ n).2
  have hk' : IsIntegral A k :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A (FractionRing A) L)
      (algebraMap (FractionRing A) L).injective).mp hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hk'
  refine ⟨n, a, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, ← hk, ← ha, ← IsScalarTower.algebraMap_apply]
  rfl

private lemma eq_of_fixed (A L Ω : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Normal (FractionRing A) L] [Field Ω] (φ φ' : integralClosure A L →+* Ω)
    (h : φ.comp (algebraMap A _) = φ'.comp (algebraMap A _)) (b : integralClosure A L)
    (hb : ∀ g : integralClosure A L ≃ₐ[A] integralClosure A L, g b = b) : φ b = φ' b := by
  obtain ⟨q, hq⟩ := ExpChar.exists (FractionRing A)
  obtain ⟨n, a, ha⟩ := fixed_pow_mem A L q b hb
  have h1 : φ b ^ q ^ n = φ' b ^ q ^ n := by
    rw [← map_pow, ← map_pow, ha]
    exact congrArg (fun f : A →+* Ω => f a) h
  cases hq with
  | zero => simpa using h1
  | prime hp =>
    have hA : (q : A) = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_natCast, map_zero, CharP.cast_eq_zero]
    have hΩ : (q : Ω) = 0 := by
      have := congrArg (fun f : A →+* Ω => f q) h
      simp only [RingHom.comp_apply, map_natCast] at this
      rw [← map_natCast (φ.comp (algebraMap A _)) q, hA, map_zero]
    haveI : CharP Ω q := (CharP.charP_iff_prime_eq_zero hp).mpr hΩ
    haveI : ExpChar Ω q := ExpChar.prime hp
    exact iterateFrobenius_inj Ω q n h1

theorem UpperTheory.Gal.TranscendenceTraces.galTrans_of : InvTrans → GalTrans := by
  intro hInv A L Ω _ _ _ _ _ _ _ _ _ _ φ φ' h
  let G := integralClosure A L ≃ₐ[A] integralClosure A L
  haveI : Finite G :=
    Finite.of_equiv _ (galRestrict A (FractionRing A) L (integralClosure A L)).toEquiv
  let A' := FixedPoints.subring (integralClosure A L) G
  haveI : SMulCommClass G A' (integralClosure A L) := ⟨fun g a b => by
    change g • ((a : integralClosure A L) * b) = (a : integralClosure A L) * (g • b)
    rw [smul_mul', show g • (a : integralClosure A L) = a from a.2 g]⟩
  haveI : Algebra.IsInvariant A' (integralClosure A L) G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  obtain ⟨g, hg⟩ := hInv A' (integralClosure A L) G Ω φ φ' (by
    ext a
    exact eq_of_fixed A L Ω φ φ' h a fun g => a.2 g)
  exact ⟨g, hg⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGenBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem genPt_exists_spec {S : Scheme.{0}} (s : S) : ∃ t : S, t ⤳ s ∧ GenPt t := by
  have hC : IsIrreducible (irreducibleComponent s) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent s) := isClosed_irreducibleComponent
  have ht : IsGenericPoint hC.genericPoint (irreducibleComponent s) :=
    hC.isGenericPoint_genericPoint hcl
  refine ⟨hC.genericPoint, ht.specializes mem_irreducibleComponent, ?_⟩
  intro t' h'
  have hsub : irreducibleComponent s ⊆ closure {t'} := by
    rw [← ht.def]
    exact h'.closure_subset
  have heq : closure ({t'} : Set S) = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  have ht' : IsGenericPoint t' (irreducibleComponent s) := heq
  exact ht'.eq ht

private theorem genPt_open {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (s : U) :
    GenPt (j s) ↔ GenPt s := by
  have he := j.isOpenEmbedding
  constructor
  · intro h t hts
    exact he.injective (h _ (hts.map he.continuous))
  · intro h t hts
    have hmem : t ∈ Set.range j := hts.mem_open he.isOpen_range ⟨s, rfl⟩
    obtain ⟨t', rfl⟩ := hmem
    have : t' ⤳ s := he.isInducing.specializes_iff.1 hts
    rw [h t' this]

private theorem genPt_integral (S : Scheme.{0}) [IsIntegral S] (s : S) :
    GenPt s ↔ s = genericPoint S := by
  constructor
  · intro h
    exact (h _ (genericPoint_specializes s)).symm
  · rintro rfl t ht
    exact (ht.antisymm (genericPoint_specializes t)).eq

theorem UpperTheory.Gal.TranscendenceTraces.genBasic_of :
    GenBasic := by
  refine ⟨fun S => ?_, fun j _ s => genPt_open j s, fun S _ s => genPt_integral S s⟩
  rw [dense_iff_inter_open]
  rintro N hN ⟨s, hs⟩
  obtain ⟨t, hts, ht⟩ := genPt_exists_spec s
  exact ⟨t, hts.mem_open hN hs, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageFin
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

set_option backward.isDefEq.respectTransparency false in
private theorem isFinite_sigma_desc_of_finite (ι : Type) [Finite ι] :
    ∀ {S : Scheme.{0}} (Z : ι → Scheme.{0}) (p : ∀ a, Z a ⟶ S), (∀ a, IsFinite (p a)) →
      IsFinite (Sigma.desc p) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro S Z p hp
    have := ih (fun a => Z (e a)) (fun a => p (e a)) (fun a => hp _)
    let i : (∐ fun a => Z (e a)) ≅ ∐ Z := Sigma.whiskerEquiv e (fun _ => Iso.refl _)
    have h : i.hom ≫ Sigma.desc p = Sigma.desc (fun a => p (e a)) := by
      apply Sigma.hom_ext
      intro a
      simp [i]
    have h' : Sigma.desc p = i.inv ≫ Sigma.desc (fun a => p (e a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    rw [h']
    infer_instance
  | h_empty =>
    intro S Z p hp
    have : IsEmpty (∐ Z : Scheme.{0}) := ⟨fun x => by
      obtain ⟨i, _, _⟩ := (sigmaOpenCover Z).exists_eq x
      exact i.elim⟩
    infer_instance
  | h_option ih =>
    intro S Z p hp
    have h1 := ih (fun a => Z (some a)) (fun a => p (some a)) (fun a => hp _)
    have h0 := hp none
    let i : (Z none ⨿ ∐ fun a => Z (some a)) ≅ ∐ Z :=
      { hom := coprod.desc (Sigma.ι Z none) (Sigma.desc fun a => Sigma.ι Z (some a))
        inv := Sigma.desc fun o => match o with
          | none => coprod.inl
          | some a => Sigma.ι (fun a => Z (some a)) a ≫ coprod.inr
        hom_inv_id := by
          apply coprod.hom_ext
          · simp
          · apply Sigma.hom_ext
            intro a
            simp
        inv_hom_id := by
          apply Sigma.hom_ext
          rintro (_ | a) <;> simp }
    have h : i.hom ≫ Sigma.desc p = coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      apply coprod.hom_ext
      · simp [i]
      · apply Sigma.hom_ext
        intro a
        simp [i]
    have h' : Sigma.desc p = i.inv ≫ coprod.desc (p none) (Sigma.desc fun a => p (some a)) := by
      rw [← h, Iso.inv_hom_id_assoc]
    have c : IsFinite (coprod.desc (p none) (Sigma.desc fun a => p (some a))) := inferInstance
    have d0 : IsIso i.inv := ⟨i.hom, i.inv_hom_id, i.hom_inv_id⟩
    have d : IsFinite i.inv := inferInstance
    rw [h']
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem UpperTheory.Gal.TranscendenceTraces.imageFin_of :
    ImageOne → ImageFin := by
  intro hOne S Y B bS bY _ _ ι _ Z p f hp hf
  have hk : (Sigma.desc fun a => pullback.lift (f a) (p a) (hf a)) ≫ pullback.snd bY bS = Sigma.desc p := by
    apply Sigma.hom_ext
    intro a
    simp
  obtain ⟨k, hkdef⟩ : ∃ k : ∐ Z ⟶ pullback bY bS, k = Sigma.desc fun a => pullback.lift (f a) (p a) (hf a) := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hι : ∀ a, Sigma.ι Z a ≫ k = pullback.lift (f a) (p a) (hf a) := by
    intro a
    simp [hkdef]
  have hfin : IsFinite (k ≫ pullback.snd bY bS) := by
    rw [hk]
    exact isFinite_sigma_desc_of_finite ι Z p hp
  obtain ⟨h1, h2⟩ := hOne k (pullback.snd bY bS)
  have hh : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι = pullback.lift (f a) (p a) (hf a) := by
    intro a
    rw [Category.assoc, Scheme.Hom.toImage_imageι, hι]
  have hpa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS = p a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_snd]
  have hfa : ∀ a, (Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.fst bY bS = f a := by
    intro a
    rw [← Category.assoc, hh, pullback.lift_fst]
  refine ⟨k.image, k.imageι ≫ pullback.snd bY bS, k.imageι ≫ pullback.fst bY bS,
    fun a => Sigma.ι Z a ≫ k.toImage, h1, fun a => ?_, hpa, hfa, ?_⟩
  · have : IsFinite ((Sigma.ι Z a ≫ k.toImage) ≫ k.imageι ≫ pullback.snd bY bS) := by
      rw [hpa]
      exact hp a
    exact IsFinite.of_comp _ (k.imageι ≫ pullback.snd bY bS)
  · intro T x y hs hf'
    rw [← cancel_mono k.imageι]
    apply pullback.hom_ext
    · simpa using hf'
    · simpa using hs
end

