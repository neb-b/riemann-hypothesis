module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendScalarsUliftHomAdditive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial

namespace GlobalTheory.EtC.GmStep

variable (R : Type) [CommRing R]

def rowD (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) :
    H R (disc.obj (E.obj (op ⦋p⦌))) F s →+ H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s :=
  ∑ j : Fin (p + 2), ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s

def RowExact (E : Spc) (F : Shv R) (s : ℤ) (p : ℕ) : Prop :=
  ∀ y : H R (disc.obj (E.obj (op ⦋p + 1⦌))) F s, rowD R E F s (p + 1) y = 0 → ∃ z, rowD R E F s p z = y

variable {R}

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
private theorem map_rowDifferential_of_commute_faces_lemma {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s) :
    φ (p + 1) (_root_.GlobalTheory.EtC.GmStep.rowD R E F s p y) =
      _root_.GlobalTheory.EtC.GmStep.rowD R E' F' s' p (φ p y) := by
  change φ (p + 1) ((AddMonoidHom.eval y) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E.δ j)) F s)) =
    (AddMonoidHom.eval (φ p y)) (∑ j : Fin (p + 2),
      ((-1 : ℤ) ^ (j : ℕ)) • pull R (disc.map (E'.δ j)) F' s')
  simp only [map_sum, map_zsmul]
  exact Finset.sum_congr rfl fun j _ => congrArg (fun x => ((-1 : ℤ) ^ (j : ℕ)) • x) (hc p j y)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.rowExact_transfer {E E' : _root_.GlobalTheory.EtC.Spc}
    {F F' : _root_.GlobalTheory.EtC.Shv R} {s s' : ℤ}
    (φ : ∀ p : ℕ, _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s →+
      _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E'.obj (op ⦋p⦌))) F' s')
    (hφ : ∀ p, Function.Bijective (φ p))
    (hc : ∀ (p : ℕ) (j : Fin (p + 2))
      (y : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.disc.obj (E.obj (op ⦋p⦌))) F s),
      φ (p + 1) (_root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E.δ j)) F s y) =
        _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.disc.map (E'.δ j)) F' s' (φ p y))
    (p : ℕ) (h : _root_.GlobalTheory.EtC.GmStep.RowExact R E F s p) : _root_.GlobalTheory.EtC.GmStep.RowExact R E' F' s' p := by
  intro y' hy'
  obtain ⟨y, rfl⟩ := (hφ (p + 1)).2 y'
  have hy : _root_.GlobalTheory.EtC.GmStep.rowD R E F s (p + 1) y = 0 := by
    apply (hφ (p + 1 + 1)).1
    rw [map_rowDifferential_of_commute_faces_lemma φ hc, hy', map_zero]
  obtain ⟨z, rfl⟩ := h y hy
  exact ⟨φ p z, (map_rowDifferential_of_commute_faces_lemma φ hc p z).symm⟩

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  LaurentPolynomial.eval₂ ((LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f) (laurentVarUnit B)

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) := by
  simp [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_C]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (m : ℤ) :
    _root_.GlobalTheory.EtC.GmStep.laurentMap f (LaurentPolynomial.T m) = LaurentPolynomial.T m := by
  have hu : ((_root_.GlobalTheory.EtC.laurentVarUnit B : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T 1 := rfl
  have hinv : (((_root_.GlobalTheory.EtC.laurentVarUnit B)⁻¹ : (LaurentPolynomial B)ˣ) :
      LaurentPolynomial B) = LaurentPolynomial.T (-1) := by
    rw [← Units.inv_mul_cancel_left (_root_.GlobalTheory.EtC.laurentVarUnit B)
      (LaurentPolynomial.T (-1)), hu, ← LaurentPolynomial.T_add]
    simp
  rw [_root_.GlobalTheory.EtC.GmStep.laurentMap, LaurentPolynomial.eval₂_T]
  refine Int.induction_on m ?_ (fun k ih => ?_) (fun k ih => ?_)
  · simp
  · rw [zpow_add_one, Units.val_mul, ih, hu, ← LaurentPolynomial.T_add]
  · rw [zpow_sub_one, Units.val_mul, ih, hinv, ← LaurentPolynomial.T_add, sub_eq_add_neg]

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C =
      (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f :=
  RingHom.ext fun a => _root_.GlobalTheory.EtC.GmStep.laurentMap_C f a

open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (p : LaurentPolynomial A) :
    (_root_.GlobalTheory.EtC.GmStep.laurentMap f p).coeff = Finsupp.mapRange f f.map_zero p.coeff := by
  refine LaurentPolynomial.induction_on' p (fun p q hp hq => ?_) (fun n a => ?_)
  · rw [map_add (f := _), AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add, hp, hq,
      Finsupp.mapRange_add (map_add f)]
  · rw [map_mul, _root_.GlobalTheory.EtC.GmStep.laurentMap_C, _root_.GlobalTheory.EtC.GmStep.laurentMap_T,
      ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.mapRange_single]


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_isIntegral {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : f.IsIntegral) : (_root_.GlobalTheory.EtC.GmStep.laurentMap f).IsIntegral := by
  letI := (_root_.GlobalTheory.EtC.GmStep.laurentMap f).toAlgebra
  intro x
  change IsIntegral (LaurentPolynomial A) x
  refine LaurentPolynomial.induction_on' x (fun p q hp hq => hp.add hq) (fun n b => ?_)
  refine IsIntegral.mul ?_ ?_
  · obtain ⟨P, hm, hP⟩ := hf b
    refine ⟨P.map LaurentPolynomial.C, hm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    change Polynomial.eval₂ ((_root_.GlobalTheory.EtC.GmStep.laurentMap f).comp LaurentPolynomial.C)
      (LaurentPolynomial.C b) P = 0
    rw [_root_.GlobalTheory.EtC.GmStep.laurentMap_comp_C, ← Polynomial.hom_eval₂, hP, map_zero]
  · rw [← _root_.GlobalTheory.EtC.GmStep.laurentMap_T f n]
    exact isIntegral_algebraMap


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.laurentMap_ker {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (hk : RingHom.ker f ≤ nilradical A) :
    RingHom.ker (_root_.GlobalTheory.EtC.GmStep.laurentMap f) ≤ nilradical (LaurentPolynomial A) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  have hc : ∀ n, f (x.coeff n) = 0 := by
    intro n
    have h := congrArg (fun g => g n) (_root_.GlobalTheory.EtC.GmStep.laurentMap_coeff f x)
    rw [hx] at h
    simpa using h.symm
  rw [← AddMonoidAlgebra.sum_coeff_single x, Finsupp.sum]
  refine Ideal.sum_mem _ fun n _ => ?_
  rw [LaurentPolynomial.single_eq_C_mul_T]
  refine Ideal.mul_mem_right _ _ ?_
  exact mem_nilradical.mpr ((mem_nilradical.mp (hk (RingHom.mem_ker.mpr (hc n)))).map _)


open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial in
variable (R : Type) [CommRing R] in
variable {R} in
theorem _root_.GlobalTheory.EtC.GmStep.spec_integral_surj {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (hi : φ.IsIntegral) (hk : RingHom.ker φ ≤ nilradical A) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) := by
  refine ⟨IsIntegralHom.SpecMap_iff.mpr hi, ⟨?_⟩⟩
  letI := φ.toAlgebra
  haveI : Algebra.IsIntegral A B := ⟨hi⟩
  intro P
  haveI := P.isPrime
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P.asIdeal (⊥ : Ideal B)
    (fun a ha => nilradical_le_prime P.asIdeal
      (hk (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ha)))))
  refine ⟨⟨Q, hQ⟩, ?_⟩
  change PrimeSpectrum.comap φ ⟨Q, hQ⟩ = P
  exact PrimeSpectrum.ext hQP

variable (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A']

abbrev baseHom : Spec (CommRingCat.of A') ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A A'))

abbrev laurentHom : Spec (CommRingCat.of (LaurentPolynomial A')) ⟶ Spec (CommRingCat.of (LaurentPolynomial A)) :=
  Spec.map (CommRingCat.ofHom (laurentMap (algebraMap A A')))

def constSq : Arrow.mk (yoneda.map (laurentHom A A')) ⟶ Arrow.mk (yoneda.map (baseHom A A')) :=
  Arrow.homMk (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A' →+* LaurentPolynomial A'))))
    (yoneda.map (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : A →+* LaurentPolynomial A)))) (by
      simp only [Arrow.mk_hom, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [laurentMap_comp_C])

def cechC : cech (laurentHom A A') ⟶ cech (baseHom A A') := Arrow.mapCechNerve (constSq A A')

def augK (k : ℕ) : disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌)) ⟶ sch.obj (Spec (CommRingCat.of (LaurentPolynomial A))) :=
  disc.map ((cechAug (laurentHom A A')).app (op ⦋k⦌))

def rowOne (q : ℕ) (i : ℤ) (k : ℕ) :
    Ht q (disc.obj ((cech (baseHom A A')).obj (op ⦋k⦌))) 0 (i - 1) →+ Ht q (disc.obj ((cech (laurentHom A A')).obj (op ⦋k⦌))) 1 i where
  toFun a := (cup q (pull _ (disc.map ((cechC A A').app (op ⦋k⦌))) (tw q (i - 1)) 0 a)
    (pull _ (augK A A' k) (tw q 1) 1 (kum q (laurentVar A)))).cast (by ring) (by ring)
  map_zero' := by simp only [map_zero, AddMonoidHom.zero_apply]; exact GmPhi.cast_zero _ _
  map_add' a b := by simp only [map_add (f := _), AddMonoidHom.add_apply]; exact GmPhi.cast_add _ _ _ _

end GlobalTheory.EtC.GmStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyFlatEtaleSheafLocallyDivisible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.FlatLoc

theorem zmod_dvd_of_mul_eq_zero (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (r : ZMod Q)
    (hr : (e : ZMod Q) * r = 0) : ∃ s : ZMod Q, r = (q : ZMod Q) * s := by
  have he : e ≠ 0 := by
    rintro rfl; exact NeZero.ne Q (by rw [← hQ, mul_zero])
  have h1 : ((e * r.val : ℕ) : ZMod Q) = 0 := by push_cast; rw [ZMod.natCast_zmod_val]; exact hr
  rw [ZMod.natCast_eq_zero_iff] at h1
  have h2 : e * q ∣ e * r.val := by rw [mul_comm e q, hQ]; exact h1
  obtain ⟨t, ht⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero he) h2
  refine ⟨t, ?_⟩
  rw [← ZMod.natCast_zmod_val r, ht]; push_cast; ring

theorem flat_dvd (Q q e : ℕ) [NeZero Q] (hQ : q * e = Q) (N : Type*) [AddCommGroup N]
    [Module (ULift.{1} (ZMod Q)) N] [Module.Flat (ULift.{1} (ZMod Q)) N] (n : N) (hn : e • n = 0) :
    ∃ n' : N, n = q • n' := by
  have hs : ∑ _i : Unit, (e : ULift.{1} (ZMod Q)) • n = 0 := by
    simpa [Nat.cast_smul_eq_nsmul] using hn
  obtain ⟨k, a, y, hx, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (f := fun _ : Unit => (e : ULift.{1} (ZMod Q))) (x := fun _ : Unit => n) hs
  have hb : ∀ j, ∃ s : ZMod Q, (a () j).down = (q : ZMod Q) * s := fun j => by
    refine zmod_dvd_of_mul_eq_zero Q q e hQ _ ?_
    have := congrArg ULift.down (ha j)
    simpa using this
  choose s hs using hb
  refine ⟨∑ j, (ULift.up (s j) : ULift.{1} (ZMod Q)) • y j, ?_⟩
  rw [show n = ∑ j, a () j • y j from hx (), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod Q)), smul_smul]
  congr 1
  apply ULift.ext
  simp [hs j]

theorem flat_loc : ∀ (Q q e : ℕ) [NeZero Q], q * e = Q → ∀ (M : Shv (ZMod Q)), FlatS M → ∀ (U : Scheme.{0}) (x : Sec M U),
    e • x = 0 → Loc U fun V g => ∃ y : Sec M V, Sec.res g x = q • y := by
  intro Q q e _ hQ M hM U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have hnat : ∀ {W V : Scheme.{0}} (k : W ⟶ V) (p : P.obj (op V)),
      (φ.app (op W)).hom ((P.map k.op).hom p) = Sec.res k ((φ.app (op V)).hom p) := fun k p => by
    have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.naturality k.op)) p
    simpa using this
  have hres : ∀ {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (s : Sec M U),
      Sec.res k (Sec.res g s) = Sec.res (k ≫ g) s := by
    intro W V U k g s
    simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine loc_trans U _ (loc_mono U _ _ (hsurj U x) fun V g hpg => ?_)
  obtain ⟨p, hp⟩ := hpg
  have hep : (φ.app (op V)).hom (e • p) = 0 := by
    rw [map_nsmul, hp]
    show e • (M.obj.map g.op).hom x = 0
    rw [← map_nsmul, hx, map_zero]
  refine loc_mono V _ _ (hinj V (e • p) hep) fun W k hk => ?_
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    obtain ⟨p', hp'⟩ := flat_dvd Q q e hQ _ ((P.map k.op).hom p) (by rw [← map_nsmul]; exact hk)
    refine ⟨(φ.app (op W)).hom p', ?_⟩
    rw [← hres, ← hp, ← hnat, hp', map_nsmul]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    refine ⟨0, ?_⟩
    rw [smul_zero]
    exact (sec_ext_glue (ZMod Q) M W).1 _ _ (loc_of_isEmpty W _)

end GlobalTheory.EtC.FlatLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFGLDepthStagesLowAImports
section
namespace GlobalTheory.DepthStages

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def rebase (G : LogFGL v d) (X : Matrix (Fin d) (Fin d) C) (γ : Fin d → Fin d → PowerSeries C) :
    Fin d → Fin d → PowerSeries C :=
  fun a => G.sumF fun b => rescaleCurve (X a b) (γ b)

def glue {ι : Type} (lab : Fin d → ι) (S : ι → Finset (Fin d)) (x : ι → Matrix (Fin d) (Fin d) C) :
    Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => if a ∈ S (lab a) then x (lab a) a b else if a = b then 1 else 0

end

end GlobalTheory.DepthStages
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem map_twoSided_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ _ _ μ _ u a
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  have := hfd
  have := (hmat α ν).1
  let T := twoSidedEquiv F E u a

  have hdet : LinearEquiv.det T =
      (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u) ^ Fintype.card ν *
        (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a) ^
          Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, _root_.GlobalTheory.KSp.det_restrictScalars_twoSidedMul F E α ν (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x ↦ rfl)]
    simp
  have hT : (fun x ↦ (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, _root_.GlobalTheory.KSp.map_linearEquiv_haar F (Matrix α ν E) μ T, hdet, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.DetPowShape

noncomputable def detZ (i : ℕ) : MvPolynomial (Σ _ : Fin i, Fin i) ℤ :=
  Matrix.det (Matrix.of fun a b : Fin i =>
    (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) ℤ))

theorem detPow_eq_map (C : Type) [Field C] (i c : ℕ) :
    detPow C i c = MvPolynomial.map (Int.castRingHom C) (detZ i ^ c) := by
  rw [map_pow, detZ, RingHom.map_det]
  unfold detPow
  congr 2
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem weight_eq_sum {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    Finsupp.weight w α = ∑ x, α x * w x := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [smul_eq_mul]

theorem det_wh {R : Type} [CommRing R] {i : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) :
    MvPolynomial.IsWeightedHomogeneous w (Matrix.det (Matrix.of fun a b : Fin i =>
      (MvPolynomial.X ⟨b, a⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))) 1 := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := MvPolynomial.IsWeightedHomogeneous.prod (R := R) (w := w) Finset.univ
    (fun j => (MvPolynomial.X ⟨j, σ j⟩ : MvPolynomial (Σ _ : Fin i, Fin i) R))
    (fun j => w ⟨j, σ j⟩) (fun j _ => MvPolynomial.isWeightedHomogeneous_X R w _)
  rw [hw σ] at hp
  have hc : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Σ _ : Fin i, Fin i) R) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  simp only [Matrix.of_apply]
  rw [hc]
  simpa using hp.C_mul ((Equiv.Perm.sign σ : ℤ) : R)

theorem sum_of_mem_support {C : Type} [Field C] {i c : ℕ} (w : (Σ _ : Fin i, Fin i) → ℕ)
    (hw : ∀ σ : Equiv.Perm (Fin i), ∑ j, w ⟨j, σ j⟩ = 1) (α) (hα : α ∈ (detPow C i c).support) :
    ∑ x, α x * w x = c := by
  have h := (det_wh (R := C) w hw).pow c
  rw [← weight_eq_sum]
  have := h (MvPolynomial.mem_support_iff.1 hα)
  simpa using this

theorem detPow_shape : ∀ (C : Type) [Field C] [CharZero C] (i c : ℕ),
    (detPow C i c).IsHomogeneous (i * c) ∧ (∀ α, ∃ n : ℤ, (detPow C i c).coeff α = n) ∧
    (detPow C i c).coeff (∑ a : Fin i, Finsupp.single ⟨a, a⟩ c) = 1 ∧
    ∀ α ∈ (detPow C i c).support, (∀ a : Fin i, ∑ b : Fin i, α ⟨b, a⟩ = c) ∧
      (∀ b : Fin i, ∑ a : Fin i, α ⟨b, a⟩ = c) := by
  intro C _ _ i c
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := C)
      (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i))).pow c
    simpa [Fintype.card_fin, detPow] using this
  · intro α
    exact ⟨(detZ i ^ c).coeff α, by rw [detPow_eq_map, MvPolynomial.coeff_map]; simp⟩
  · let f : Fin i → (Σ _ : Fin i, Fin i) := fun a => ⟨a, a⟩
    have hf : Function.Injective f := fun x y h => congrArg Sigma.fst h
    have h1 : (∑ a : Fin i, Finsupp.single (⟨a, a⟩ : Σ _ : Fin i, Fin i) c) =
        Finsupp.mapDomain f (∑ a : Fin i, Finsupp.single a c) := by
      change _ = Finsupp.mapDomain.addMonoidHom f _
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, f]
    have h2 : MvPolynomial.killCompl hf (detPow C i c) =
        MvPolynomial.monomial (∑ a : Fin i, Finsupp.single a c) 1 := by
      unfold detPow
      rw [map_pow, GlobalTheory.LeadingMinors.killCompl_det_X (k := C) hf
        (fun a b : Fin i => (⟨b, a⟩ : Σ _ : Fin i, Fin i)) id (fun a => rfl),
        MvPolynomial.monomial_pow, one_pow]
      · congr 1
        rw [Finset.smul_sum]
        simp
      · rintro a b hab ⟨x, hx⟩
        obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hx
        exact hab ((eq_of_heq h2).symm.trans h1)
    rw [h1, ← MvPolynomial.coeff_killCompl hf, h2, MvPolynomial.coeff_monomial, if_pos rfl]
  · intro α hα
    constructor
    · intro a
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.2 = a then 1 else 0) (fun σ => by
          rw [← Equiv.sum_comp σ.symm]
          simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h
    · intro b
      have h := sum_of_mem_support (C := C) (c := c)
        (fun x => if x.1 = b then 1 else 0) (fun σ => by simp) α hα
      rw [Fintype.sum_sigma] at h
      simpa using h

end GlobalTheory.DetPowShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableCutoffGramBoundMixedBlockStatement
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cutoffGramBoundMixedBlock : ∀ (r p0 : ℕ), Measurable (hB (r := r) p0) := by
  first | exact @GlobalTheory.IntBall.measurable_hB | exact GlobalTheory.IntBall.measurable_hB | (intros; apply GlobalTheory.IntBall.measurable_hB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements : ∀ (Λ : Type 1) [Ring Λ] (N : CommRingCat.{0} ⥤ ModuleCat.{1} Λ), (PreservesFilteredColimitsOfSize.{0, 0} N ↔ PreservesFilteredColimitsOfSize.{0, 0} (N ⋙ forget₂ (ModuleCat.{1} Λ) AddCommGrpCat.{1})) ∧ (PreservesFilteredColimitsOfSize.{0, 0} N ↔ ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → (∀ x : N.obj c.pt, ∃ j y, (N.map (c.ι.app j)).hom y = x) ∧ ∀ j (y : N.obj (D.obj j)), (N.map (c.ι.app j)).hom y = 0 → ∃ (k : J) (f : j ⟶ k), (N.map (D.map f)).hom y = 0) := by
  first | (exact @GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements) | (exact GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements) | (intros; apply GlobalTheory.EtC.FilteredElements.preservesFilteredColimits_modules_iff_elements  <;> assumption)
end

