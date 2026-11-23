module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.Bundle0002
public import Development.EtaleCohomology.TateTwists.Bundle0008

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerSequence.GmSepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.GmSepPf

def ev (V : Scheme.{0}) (a : Γ(V, ⊤)) : CommRingCat.of (Polynomial ℤ) ⟶ Γ(V, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) a)

def lineMap (V : Scheme.{0}) (a : Γ(V, ⊤)) : V ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  ΓSpec.adjunction.homEquiv V (op (CommRingCat.of (Polynomial ℤ))) (ev V a).op

theorem lineMap_inj (V : Scheme.{0}) (a b : Γ(V, ⊤)) (h : lineMap V a = lineMap V b) : a = b := by
  have h1 := (ΓSpec.adjunction.homEquiv _ _).injective h
  have h2 := congrArg (fun f => f.hom Polynomial.X) (Quiver.Hom.op_inj h1)
  simpa [ev] using h2

theorem ev_comp {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) : ev V a ≫ g.appTop = ev W (g.appTop a) := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro n; simp [ev]
  · simp [ev]

theorem lineMap_nat {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) :
    g ≫ lineMap V a = lineMap W (g.appTop a) := by
  unfold lineMap
  refine (ΓSpec.adjunction.homEquiv_naturality_left g (ev V a).op).symm.trans ?_
  congr 1
  apply Quiver.Hom.unop_inj
  exact ev_comp g a

theorem gamma_sep (V : Scheme.{0}) (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) (a b : Γ(V, ⊤))
    (h : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → g.appTop a = g.appTop b) : a = b := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have hsh := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.etaleTopology.{0})
    (yoneda.obj (Spec (CommRingCat.of (Polynomial ℤ))))
  apply lineMap_inj
  refine (hsh S hS).isSeparatedFor.ext (fun W g hg => ?_)
  change g ≫ lineMap V a = g ≫ lineMap V b
  rw [lineMap_nat, lineMap_nat, h W g hg]

theorem gmSep : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := by
  intro V u h
  have h0 : ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom (ULift.up (Additive.ofMul u))
      = ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom 0 := by
    rw [map_zero]; exact h
  have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op V)
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op V)) 0 h0
  apply Units.ext
  refine gamma_sep V _ hm u.1 (1 : Γ(V, ⊤)) (fun W g hg => ?_)
  have h1 := congrArg (fun z : (Scheme.Γ ⋙ unitsF).obj (op W) => ((Additive.toMul z.down : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) hg
  exact h1

theorem GmSep_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := gmSep

end LateralTheory.E.H2CurveOrder.GmSepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
open LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

theorem cycPow : CycPow := by
  intro q A _ ζ
  obtain ⟨hq, hz⟩ := ζ.2
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have : Subsingleton A := by
      simp at hz
      exact subsingleton_of_zero_eq_one hz.symm
    exact ⟨1, Subsingleton.elim _ _, fun _ _ => Or.inr this⟩
  have hqz : ζ.1 ^ q = 1 := by
    obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (aeval ζ.1) hG
    simp [hz] at this
    exact sub_eq_zero.1 this
  have h1 : ζ.1 * ζ.1 ^ (q - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hq0]; exact hqz
  have hu : IsUnit ζ.1 := ⟨⟨ζ.1, ζ.1 ^ (q - 1), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, rfl, fun c hc => ?_⟩
  have hc' : ζ.1 ^ c = 1 := by simpa using congrArg Units.val hc
  set d := Nat.gcd c q with hd
  have hdz : ζ.1 ^ d = 1 := pow_gcd_eq_one.2 ⟨hc', hqz⟩
  by_cases hdq : d = q
  · left; rw [← hdq]; exact Nat.gcd_dvd_left c q
  right
  obtain ⟨G, hG⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ (Nat.mem_properDivisors.2 ⟨Nat.gcd_dvd_right c q, lt_of_le_of_ne (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right c q)) hdq⟩)
  have hG' := congrArg (Polynomial.map (Int.castRingHom A)) hG
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_cyclotomic] at hG'
  have r1 : (X - C ζ.1) ∣ (X ^ d - 1 : A[X]) := dvd_iff_isRoot.2 (by simp [hdz])
  have r2 : (X - C ζ.1) ∣ cyclotomic q A := dvd_iff_isRoot.2 (by
    have := hz
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at this)
  obtain ⟨a, ha⟩ := r1
  obtain ⟨b, hb⟩ := r2
  have hE : (X ^ q - 1 : A[X]) = (X - C ζ.1) ^ 2 * (a * b * G.map (Int.castRingHom A)) := by
    rw [hG', ha, hb]; ring
  have hD := congrArg (fun p => eval ζ.1 (derivative p)) hE
  simp [derivative_mul, derivative_pow] at hD
  have hu' : IsUnit ((q : A) * ζ.1 ^ (q - 1)) := hq.mul (hu.pow _)
  have h0 : (q : A) * ζ.1 ^ (q - 1) = 0 := by simpa using hD
  rw [h0] at hu'
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')

theorem emptySec : EmptySec := by
  intro R _ F V hs y
  have : IsEmpty V := by
    refine ⟨fun x => ?_⟩
    have h1 : (1 : V.presheaf.stalk x) = 0 := by
      rw [← map_one (V.presheaf.germ ⊤ x trivial).hom, Subsingleton.elim (1 : Γ(V, ⊤)) 0, map_zero]
    exact one_ne_zero h1
  exact LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.shfSep R F V y (LateralTheory.EtaleFoundations.LocBasicPf.loc_empty V _)

theorem LeafKumMuInj_of (hL : TwLocGen) (hG : GmSep) : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuInj :=
  LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.LeafKumMuInj_of hL hG cycPow emptySec

end LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPowPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf

def powCof {A : Type*} [CommRing A] (u v : A) (q : ℕ) : A := ∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)

theorem powCof_mul {A : Type*} [CommRing A] (u v : A) (q : ℕ) : powCof u v q * (u - v) = u ^ q - v ^ q :=
  geom_sum₂_mul u v q

theorem powCof_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (u v : A) (q : ℕ) :
    φ (powCof u v q) = powCof (φ u) (φ v) q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [powCof, map_sum, map_mul, map_pow]

theorem powCof_self {A : Type*} [CommRing A] (v : A) (q : ℕ) : powCof v v q = (q : A) * v ^ (q - 1) := by
  unfold powCof
  rw [Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]
  · simp
  · intro i hi
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega

theorem field_step {K : Type} [Field K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z w : K)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) (hw : w ^ q = 1) :
    ∃ a : Fin q, powCof w (z ^ (a : ℕ)) q ≠ 0 := by
  have : NeZero (q : K) := ⟨hq⟩
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z := by
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]
    rw [Polynomial.aeval_def, algebraMap_int_eq] at hz
    exact hz
  have hp : IsPrimitiveRoot z q := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨i, hi, hzi⟩ := hp.eq_pow_of_pow_eq_one hw
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [← hzi, powCof_self]
  have hz0 : z ≠ 0 := fun h => by
    have := hp.pow_eq_one; rw [h, zero_pow (NeZero.ne q)] at this; exact zero_ne_one this
  exact mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))

theorem isUnit_of_basicOpen_top {V : Scheme.{0}} (t : Γ(V, ⊤)) (h : V.basicOpen t = ⊤) : IsUnit t := by
  apply V.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ V.basicOpen t := by rw [h]; trivial
  exact (V.mem_basicOpen_top t x).1 hx'

theorem pow_pf : LeafKumMuSurjPow := by
  intro q _ U ζ u hu
  let s : Fin q → Γ(U, ⊤) := fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q
  have hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a)) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    let φ := (U.Γevaluation x).hom
    have hq : (q : U.residueField x) ≠ 0 := by
      have := ζ.2.1.map φ
      simpa using this.ne_zero
    have hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by
      have := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
      rw [ζ.2.2, map_zero] at this
      exact this
    have hw : (φ (u : Γ(U, ⊤))) ^ q = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    obtain ⟨a, ha⟩ := field_step q hq _ _ hz hw
    refine ⟨a, ?_⟩
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]
    show φ (s a) ≠ 0
    simp only [s]
    rw [powCof_map, map_pow]
    exact ha
  let 𝒰 := U.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩
  intro V f hf
  obtain ⟨a', g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  let a : Fin q := a'
  refine ⟨(a : ℕ), ?_⟩
  have hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a)) := by
    apply isUnit_of_basicOpen_top
    rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
    intro x _
    show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)
    exact (g.base x).2
  have hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0 := by
    simp only [s]
    rw [powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul,
      prim_pow_q ζ, one_pow, sub_self]
  have key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ) := fun ψ h => by
    have h2 := congrArg ψ hzero
    rw [map_mul, map_zero] at h2
    rw [← map_pow]
    exact sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))
  apply key
  exact hunit

theorem LeafKumMuSurjPow_of : LeafKumMuSurjPow := pow_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPrimPf
section
open Polynomial CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
noncomputable section
namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf

theorem cyc_cond (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    ∃ p₁ p₂ : B[X], ∃ n : ℕ, derivative (cyclotomic q B) * p₁ + cyclotomic q B * p₂ = (1 : B[X]) ^ n := by
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q B
  obtain ⟨c, hc⟩ : ∃ c : B, c * q = 1 := ⟨↑hq.unit⁻¹, by simp⟩
  refine ⟨C c * X * G, C c * X * derivative G - G, 1, ?_⟩
  have hd := congrArg derivative hG
  rw [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero] at hd
  have key : (1 : B[X]) = C c * X * (C (q : B) * X ^ (q - 1)) - (X ^ q - 1) := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · subst h0; simp at hc; have : Subsingleton B := subsingleton_of_zero_eq_one hc; exact Subsingleton.elim _ _
    · have : X * X ^ (q - 1) = (X : B[X]) ^ q := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      calc (1 : B[X]) = C (c * q) * (X * X ^ (q - 1)) - (X ^ q - 1) := by rw [hc, this]; simp
        _ = _ := by rw [C_mul]; ring
  rw [pow_one, key, hd, hG]
  ring

def cycPair (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) : StandardEtalePair B where
  f := cyclotomic q B
  monic_f := cyclotomic.monic q B
  g := 1
  cond := cyc_cond q B hq

theorem cycPair_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q ℤ) = 0 := by
  have h : aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1
  rw [← map_cyclotomic_int, ← algebraMap_int_eq, aeval_map_algebraMap] at h
  exact h

theorem cycX_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    aeval (cycPair q B hq).X (cyclotomic q B) = 0 := (cycPair q B hq).hasMap_X.1

theorem root_hasMap (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).HasMap (AdjoinRoot.root (cyclotomic q B)) := by
  refine ⟨?_, ?_⟩
  · show aeval _ (cyclotomic q B) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · show IsUnit (aeval _ (1 : B[X]))
    simp

def cycTo (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring →ₐ[B] AdjoinRoot (cyclotomic q B) :=
  (cycPair q B hq).lift _ (root_hasMap q B hq)

def cycFrom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    AdjoinRoot (cyclotomic q B) →ₐ[B] (cycPair q B hq).Ring :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId B _) (cycPair q B hq).X
    (by exact (aeval_def _ _).symm.trans (cycX_root q B hq))

theorem cycFrom_root (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycFrom q B hq (AdjoinRoot.root _) = (cycPair q B hq).X := AdjoinRoot.liftAlgHom_root _ _ _ _

theorem cycTo_X (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    cycTo q B hq (cycPair q B hq).X = AdjoinRoot.root _ := StandardEtalePair.lift_X _ _ _

def cycEquiv (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    (cycPair q B hq).Ring ≃ₐ[B] AdjoinRoot (cyclotomic q B) :=
  AlgEquiv.ofAlgHom (cycTo q B hq) (cycFrom q B hq)
    (AdjoinRoot.algHom_ext (by
      show cycTo q B hq (cycFrom q B hq (AdjoinRoot.root _)) = AdjoinRoot.root _
      rw [cycFrom_root, cycTo_X]))
    ((cycPair q B hq).hom_ext (by
      show cycFrom q B hq (cycTo q B hq (cycPair q B hq).X) = (cycPair q B hq).X
      rw [cycTo_X, cycFrom_root]))

theorem cyc_comap_surj (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap B (cycPair q B hq).Ring)) := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : IsEmpty (PrimeSpectrum B) := PrimeSpectrum.isEmpty_iff_subsingleton.2 hB
    intro x; exact isEmptyElim x
  · have hfree : Module.Free B (AdjoinRoot (cyclotomic q B)) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis
    have : Module.Free B (cycPair q B hq).Ring := Module.Free.of_equiv (cycEquiv q B hq).symm.toLinearEquiv
    have hq0 : q ≠ 0 := by rintro rfl; simp at hq
    have hd : 0 < (cyclotomic q B).natDegree := by
      rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (Nat.pos_of_ne_zero hq0)
    have : Nontrivial (AdjoinRoot (cyclotomic q B)) :=
      nontrivial_of_ne _ 0 ((AdjoinRoot.powerBasis' (cyclotomic.monic q B)).basis.ne_zero ⟨0, hd⟩)
    have : Nontrivial (cycPair q B hq).Ring := (cycEquiv q B hq).toEquiv.nontrivial
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem prim_of_hom (q : ℕ) (B : Type) [CommRing B] (hq : IsUnit (q : B)) {A : Type} [CommRing A]
    (ψ : (cycPair q B hq).Ring →+* A) : Nonempty (Prim q A) := by
  refine ⟨⟨ψ (cycPair q B hq).X, ?_, ?_⟩⟩
  · have h := (hq.map (algebraMap B (cycPair q B hq).Ring)).map ψ
    simpa using h
  · rw [show ψ (cycPair q B hq).X = ψ.toIntAlgHom (cycPair q B hq).X from rfl, Polynomial.aeval_algHom_apply, cycPair_X, map_zero]

theorem LeafKumMuSurjPrim_pf : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := by
  intro q _ B _ hq U hU
  let φ : CommRingCat.of B ⟶ CommRingCat.of (cycPair q B hq).Ring :=
    CommRingCat.ofHom (algebraMap B (cycPair q B hq).Ring)
  let x : U ⟶ Spec (CommRingCat.of B) := hU.some
  have hE : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.2 ((RingHom.etale_algebraMap (R := B) (S := (cycPair q B hq).Ring)).2 inferInstance)
  have hS : Surjective (Spec.map φ) := ⟨cyc_comap_surj q B hq⟩
  have hE' : Etale (pullback.fst x (Spec.map φ)) := inferInstance
  have hS' : Surjective (pullback.fst x (Spec.map φ)) := inferInstance
  refine ⟨Sieve.generate (Presieve.singleton (pullback.fst x (Spec.map φ))),
    Precoverage.generate_mem_toGrothendieck ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2 ⟨hS'.surj, hE'⟩), ?_⟩
  rintro V f ⟨W, g, _, ⟨⟩, rfl⟩
  exact prim_of_hom q B hq ((Scheme.Γ.map (g ≫ pullback.snd x (Spec.map φ)).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (cycPair q B hq).Ring)).inv.hom)

theorem LeafKumMuSurjPrim_of : LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf.LeafKumMuSurjPrim := LeafKumMuSurjPrim_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPrimPf
end
end

