module

public import Development.EtaleCohomology.KummerTheory.Bundle0012
public import Development.EtaleCohomology.KummerTheory.Bundle0013
public import Development.EtaleCohomology.KummerTheory.Bundle0014

@[expose] public section

-- bundled from Development.EtaleCohomology.KummerTheory.AdicLimPfCok
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.CokPf

variable (l : ℕ) [Fact l.Prime]

def T (E : Spc) (n i : ℤ) (k : ℕ) : Submodule ℤ_[l] (Hl l E n i) :=
  LinearMap.ker (((l : ℤ_[l]) ^ k) • (LinearMap.id : Hl l E n i →ₗ[ℤ_[l]] Hl l E n i))

theorem T_mono (E : Spc) (n i : ℤ) : Monotone (T l E n i) := by
  intro a b hab x hx
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx ⊢
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add, mul_comm, mul_smul, hx, smul_zero]

theorem stab (E : Spc) (n i : ℤ) [Module.Finite ℤ_[l] (Hl l E n i)] :
    ∃ K : ℕ, ∀ m, T l E n i m ≤ T l E n i K := by
  have : IsNoetherian ℤ_[l] (Hl l E n i) := inferInstance
  obtain ⟨K, hK⟩ := monotone_stabilizes_iff_noetherian.mpr this ⟨T l E n i, T_mono l E n i⟩
  refine ⟨K, fun m => ?_⟩
  rcases le_total m K with h | h
  · exact T_mono l E n i h
  · exact (hK m h).symm.le

theorem cok (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) [Module.Finite ℤ_[l] (Hl l E (n + 1) i)] :
    ∃ M : ℕ, 0 < M ∧ ∀ (k : ℕ) (z : Ht (l ^ k) E n i), ∃ x : Hl l E n i, lev l x k = M • z := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨K, hK⟩ := stab l E (n + 1) i
  refine ⟨l ^ K, pow_pos (Fact.out : l.Prime).pos K, fun k z => ?_⟩
  obtain ⟨u, d, h⟩ := hB k
  let D : Hl l E (n + 1) i := ⟨fun a => d a n z, fun a => (h a n).2.2.2.2.1 z⟩
  have hD : D ∈ T l E (n + 1) i k := by
    simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    apply Subtype.ext; funext a
    change (l ^ k) • d a n z = 0
    rw [← map_nsmul, KerPf.smul_zero_of l E n i k k le_rfl, map_zero]
  have hD' := hK k hD
  simp only [T, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hD'
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hD'
  have hz : ∀ a, d a n ((l ^ K) • z) = 0 := fun a => by
    have := congrArg (fun v : Hl l E (n + 1) i => v.1 a) hD'
    change (l ^ K) • d a n z = 0 at this
    rw [map_nsmul]; exact this
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ (k + a)) E n i // red (l ^ (k + a)) (l ^ k) E n i w = (l ^ K) • z}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin (k + a) n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).2.1 ((l ^ K) • z)).1 (hz a)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (k + (a + 1))) (l ^ (k + a)) E n i w.1, by
    rw [(@hA (l ^ (k + (a + 1))) (l ^ (k + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ k)
      (pow_dvd_pow l (by omega)) n i w.1]
    exact w.2⟩
  obtain ⟨s, hs⟩ := KerPf.seqSec S t
  let x : Hl l E n i := ⟨fun j => red (l ^ (k + j)) (l ^ j) E n i (s j).1, fun j => by
    have A := (@hA (l ^ (k + (j + 1))) (l ^ (j + 1)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    have B := (@hA (l ^ (k + (j + 1))) (l ^ (k + j)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ j)
      (pow_dvd_pow l (by omega)) n i (s (j + 1)).1
    exact A.trans (B.symm.trans (congrArg (fun w : S j => red (l ^ (k + j)) (l ^ j) E n i w.1) (hs j)))⟩
  exact ⟨x, (s k).2⟩

end LateralTheory.KummerTheory.CokPf

namespace LateralTheory.KummerTheory

theorem AdicCok_holds : AdicCok := fun hA l _ E i hB hFin n _ => CokPf.cok l hA E i hB hFin n

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.NrmMkPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.NrmMkPf

def eta₃ (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (freeP R).obj P ⟶ F.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom (fun y => a U.unop y.down))
  naturality U V g := by
    refine ModuleCat.free_hom_ext (fun y => ?_)
    simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.whiskeringRight_obj_map, Functor.comp_obj, Functor.comp_map,
      ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ha _ _ g.unop y.down).symm

def phi (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x)) :
    (free R).obj P ⟶ F :=
  ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology (eta₃ R P F a ha) F.property)

theorem phi_gen (R : Type) [CommRing R] (P : PSh) (F : Shv R)
    (a : ∀ U : Scheme.{0}, P.obj (op U) → Sec F U)
    (ha : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (a U x) = a V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) :
    ((phi R P F a ha).hom.app (op U)).hom (freeGen R P U x) = a U x := by
  have e := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta₃ R P F a ha) F.property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
  refine e.trans ?_
  erw [ModuleCat.freeDesc_apply]
  rfl

theorem aux (R : Type) [CommRing R] {E : Spc} {I : Cx R} (n j : ℤ)
    (φ : ∀ p : ℕ, -(p : ℤ) + n = j → ((free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X j)) (p q : ℕ) (hpq : q = p)
    (hi : -(p : ℤ) = -(q : ℤ)) (hp : -(p : ℤ) + n = j) (hq : -(q : ℤ) + n = j) :
    (((chains R).obj E).XIsoOfEq hi).hom ≫ (chainsXIso R E q).hom ≫ φ q hq = (chainsXIso R E p).hom ≫ φ p hp := by
  subst hpq; simp

end LateralTheory.KummerTheory.NrmMkPf

namespace LateralTheory.KummerTheory
open NrmMkPf in
theorem NrmMk_of : NrmMk := by
  intro R _ E I n a ha
  let φ : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ((free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s) :=
    fun p s h => phi R _ (I.X s) (fun U x => a p s h U x) (fun V U g x => ha p s h V U g x)
  refine ⟨Cochain.mk (fun i j hij => if hi : i ≤ 0 then
      (((chains R).obj E).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
        (chainsXIso R E (-i).toNat).hom ≫ φ ((-i).toNat) j (by omega) else 0), ?_⟩
  intro p s h U x
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega)]
  rw [aux R n s (fun q hq => φ q s hq) p (-(-(p : ℤ))).toNat (by omega) _ h]
  simp only [Iso.inv_hom_id_assoc]
  exact phi_gen R _ (I.X s) _ _ U x
end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.PlaceResGoodPf
section
noncomputable section

open IsLocalRing

namespace LateralTheory.KummerTheory

attribute [local instance] Ideal.Quotient.field

section
variable {k K : Type} [Field k] [Field K] [Algebra k K] (A : LocalSubring K)

lemma good_sub_mem (hA : PlaceGood k K A) (a : K) (ha : a ∈ A.toSubring) :
    ∃ c : k, (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) ∈ maximalIdeal A.toSubring := by
  obtain ⟨c, hc⟩ := hA.2 a ha
  refine ⟨c, ?_⟩
  rcases hc with h | h
  · have : (⟨a - algebraMap k K c, sub_mem ha (hA.1 c)⟩ : A.toSubring) = 0 := by
      ext; simp [h]
    rw [this]; exact zero_mem _
  · rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    apply h
    have hK : (a - algebraMap k K c) * (w : K) = 1 := by
      simpa using congrArg (fun z : A.toSubring => (z : K)) hw
    rw [inv_eq_of_mul_eq_one_right hK]; exact w.2

end

theorem PlaceResGood_of : PlaceResGood := by
  intro k K _ _ _ _ A hA y S hAS hS Q _ hQ
  let kS : k →+* S := (algebraMap k K).codRestrict S (fun c => hAS (hA.1 c))

  have stepA : ∀ a (ha : a ∈ A.toSubring), ∃ c : k, (⟨a, hAS ha⟩ : S) - kS c ∈ Q := by
    intro a ha
    obtain ⟨c, hc⟩ := good_sub_mem A hA a ha
    refine ⟨c, ?_⟩
    have := hQ (Ideal.mem_map_of_mem (Subring.inclusion hAS) hc)
    convert this using 1
    rfl

  let φ : k →+* S ⧸ Q := (Ideal.Quotient.mk Q).comp kS
  let _ : Algebra k (S ⧸ Q) := φ.toAlgebra
  have hSm : ∀ s, s ∈ Algebra.adjoin A.toSubring {y} → s ∈ S := fun s hs => by rw [hS]; exact hs
  let y' : S := ⟨y, hSm y (Algebra.subset_adjoin (Set.mem_singleton y))⟩
  have gen : ∀ s (hs : s ∈ Algebra.adjoin A.toSubring {y}),
      Ideal.Quotient.mk Q (⟨s, hSm s hs⟩ : S) ∈ Algebra.adjoin k {Ideal.Quotient.mk Q y'} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx; subst hx
      exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap r =>
      obtain ⟨c, hc⟩ := stepA r.1 r.2
      have e : Ideal.Quotient.mk Q (⟨algebraMap A.toSubring K r, hSm _ (Subalgebra.algebraMap_mem _ r)⟩ : S)
          = algebraMap k (S ⧸ Q) c := by
        rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk]
        change Ideal.Quotient.mk Q _ - Ideal.Quotient.mk Q (kS c) = 0
        rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hc
      rw [e]; exact Subalgebra.algebraMap_mem _ c
    | add x z hx hz ihx ihz =>
      have : (⟨x + z, hSm _ (add_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ + ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_add (f := _)]; exact add_mem ihx ihz
    | mul x z hx hz ihx ihz =>
      have : (⟨x * z, hSm _ (mul_mem hx hz)⟩ : S) = ⟨x, hSm _ hx⟩ * ⟨z, hSm _ hz⟩ := rfl
      rw [this, map_mul]; exact mul_mem ihx ihz
  have top : Algebra.adjoin k {Ideal.Quotient.mk Q y'} = ⊤ := by
    refine eq_top_iff.mpr fun t _ => ?_
    obtain ⟨⟨s, hs⟩, rfl⟩ := Ideal.Quotient.mk_surjective t
    exact gen s (by rw [hS] at hs; exact hs)
  have : Algebra.FiniteType k (S ⧸ Q) := ⟨⟨{Ideal.Quotient.mk Q y'}, by simpa using top⟩⟩
  have : Module.Finite k (S ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ Q)
  have surj := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := S ⧸ Q)).2
  have stepS : ∀ s : S, ∃ c : k, s - kS c ∈ Q := by
    intro s
    obtain ⟨c, hc⟩ := surj (Ideal.Quotient.mk Q s)
    refine ⟨c, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk Q s - φ c = 0
    rw [← hc]; exact sub_self _

  set B := LocalSubring.ofPrime S Q
  refine ⟨fun c => LocalSubring.le_ofPrime S Q (hAS (hA.1 c)), ?_⟩
  intro b hb
  let bb : B.toSubring := ⟨b, hb⟩
  obtain ⟨t, ht⟩ := (IsLocalization.AtPrime.equivQuotMaximalIdeal Q B.toSubring).surjective
    (Ideal.Quotient.mk (maximalIdeal B.toSubring) bb)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨c, hc⟩ := stepS s
  refine ⟨c, ?_⟩
  by_cases h0 : b = algebraMap k K c
  · exact Or.inl h0
  right
  intro hinv
  have hmem : bb - algebraMap S B.toSubring (kS c) ∈ maximalIdeal B.toSubring := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← ht,
      IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk, ← map_sub, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_comap.mp (show s - kS c ∈ (maximalIdeal B.toSubring).comap (algebraMap S B.toSubring) by
      rw [← Ideal.under_def, IsLocalization.AtPrime.under_maximalIdeal B.toSubring Q]; exact hc)
  rw [mem_maximalIdeal, mem_nonunits_iff] at hmem
  apply hmem
  refine isUnit_iff_exists_inv.mpr ⟨⟨_, hinv⟩, ?_⟩
  ext
  change (b - algebraMap k K c) * (b - algebraMap k K c)⁻¹ = 1
  exact mul_inv_cancel₀ (sub_ne_zero.mpr h0)

end LateralTheory.KummerTheory
end
end

-- bundled from Development.EtaleCohomology.KummerTheory.ShSectPf
section
open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ShSectPf

theorem isUnit_of_map {A K : Type} [CommRing A] [IsLocalRing A] [Field K] (φ : A →+* K)
    (hφ : ∀ a ∈ maximalIdeal A, φ a = 0) {a : A} (h : IsUnit (φ a)) : IsUnit a := by
  by_contra ha
  have := hφ a ((mem_maximalIdeal a).2 ha)
  rw [this] at h; exact not_isUnit_zero h

theorem alg_sect (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) : Nonempty (B →ₐ[A] A) := by
  obtain ⟨s, hsQ, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away s
  let P : StandardEtalePresentation A S := hst.nonempty_standardEtalePresentation.some
  let K := Q.ResidueField
  have hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s) := by
    rw [isUnit_iff_ne_zero]
    show algebraMap B Q.ResidueField s ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hsQ
  let ψ : S →ₐ[A] K := IsLocalization.Away.liftAlgHom s hsu
  let xb : K := ψ P.x
  have hmap := P.hasMap.map ψ
  have hder := hmap.isUnit_derivative_f

  have hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]
    rw [← hQ] at ha; exact ha
  have hloc : IsLocalHom (algebraMap A K) := ⟨fun a h => isUnit_of_map _ hkill h⟩
  let i : ResidueField A →+* K := ResidueField.lift (algebraMap A K)
  have hi : ∀ a, i (residue A a) = algebraMap A K a := fun a => ResidueField.lift_residue_apply _ a
  let _ : Algebra (ResidueField A) K := i.toAlgebra
  have hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q := by
    intro q
    rw [aeval_def, aeval_def, eval₂_map]
    congr 1
  let fb := P.f.map (residue A)
  have hint : IsIntegral (ResidueField A) xb :=
    ⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly (ResidueField A) xb).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro h0
    obtain ⟨h, hh⟩ := minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)
    have : aeval xb (derivative fb) = 0 := by
      rw [hh, derivative_mul, h0]; simp
    rw [show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _,
      hev] at this
    rw [this] at hder; exact not_isUnit_zero hder
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep
  have hd0 : X - C a0 ∣ minpoly (ResidueField A) xb := dvd_iff_isRoot.2 ha0
  have hdvd : minpoly (ResidueField A) xb ∣ X - C a0 :=
    Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0
  obtain ⟨a00, ha00⟩ := residue_surjective a0
  have hxb : xb = algebraMap A K a00 := by
    have h1 : aeval xb (X - C a0) = 0 := by
      obtain ⟨c, hc⟩ := hdvd; rw [hc, map_mul, minpoly.aeval, zero_mul]
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1, ← ha00]; exact hi a00
  have hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A := by
    intro a ha; by_contra hn
    have := ((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)
    rw [ha] at this; exact not_isUnit_zero this
  have hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q := by
    intro q; rw [hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]
  obtain ⟨r, hr, hra⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a00
    (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))
  have hrK : algebraMap A K r = xb := by
    rw [hxb, ← sub_eq_zero, ← map_sub]; exact hkill _ hra
  have hr' : P.HasMap r := by
    refine ⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩
    rw [← aeval_algebraMap_apply, hrK]; exact hmap.2
  exact ⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩

theorem ShSect_of : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  intro A _ hA Y f hf hsurj
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨y, hy⟩ := hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  let 𝒰 := Y.affineOpenCover
  let j := 𝒰.idx y
  obtain ⟨y', hy'⟩ := 𝒰.covers y
  let g := 𝒰.f j
  let φ : CommRingCat.of A ⟶ 𝒰.X j := Spec.preimage (g ≫ f)
  have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
  have het : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  algebraize [φ.hom]
  have hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A := by
    rw [hφ, Scheme.Hom.comp_apply]
    simp only [g, j] at hy' ⊢
    rw [hy', hy]
  have hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal hpt
    exact this
  have : y'.asIdeal.IsPrime := PrimeSpectrum.isPrime y'
  obtain ⟨ψ⟩ := alg_sect A (𝒰.X j) y'.asIdeal hQ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  exact ψ.commutes a

end LateralTheory.KummerTheory.ShSectPf
end

