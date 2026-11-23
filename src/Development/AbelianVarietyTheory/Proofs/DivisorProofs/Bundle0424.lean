module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthNonnegIntegralOperatorIntegralVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0374
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0240
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.ChernSpec

open GlobalTheory.EtC.ClsSpec

set_option backward.isDefEq.respectTransparency false

theorem sec_neg {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) {U : Scheme.{0}}
    (a b : Sec ((res R F).X s) U) : a = b := by
  have hZ : IsZero ((res R F).X s) :=
    CochainComplex.isZero_of_isStrictlyGE ((injectiveResolution F).cochainComplex) 0 s hs
  have h := hZ.eq_of_src (𝟙 _) 0
  have ha : Sec.map (𝟙 _) a = Sec.map (0 : (res R F).X s ⟶ _) a := by rw [h]
  have hb : Sec.map (𝟙 _) b = Sec.map (0 : (res R F).X s ⟶ _) b := by rw [h]
  simp [Sec.map] at ha hb
  rw [ha, hb]

theorem lineUnit_face_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 2 U) (i : Fin 3) :
    lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := by
  rw [← face_res, ClsSpec.lineUnit_res]

theorem rep_unique (q : ℕ) [NeZero q] {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1))
    (γ γ' : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w))
    (h0' : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ' 0 2 (by simp) U x = 0)
    (h1' : ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ' 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2' : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ' 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    γ = γ' := by
  refine (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1 _ _ fun p s hs U x => ?_
  match p with
  | 0 =>
    obtain rfl : s = 2 := by omega
    rw [h0, h0']
  | 1 =>
    obtain rfl : s = 1 := by omega
    refine ClsSpec.sep (ClsSpec.loc_mono (root_loc (hE U ⟨x.face 0⟩) (lineUnit L x)) fun V g ⟨v, hv⟩ => ?_)
    have hv' : v ^ q = lineUnit L (x.res g) := by rw [ClsSpec.lineUnit_res]; exact hv
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 1 1 _ V U g x,
      h1 V _ v hv', h1' V _ v hv']
  | 2 =>
    obtain rfl : s = 0 := by omega
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← lineUnit_face_res] at hv hw
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γ' 2 0 _ V U g x,
      h2 V _ v w hv hw, h2' V _ v w hv hw]
  | p + 3 => exact sec_neg _ _ (by omega) _ _

theorem rep_comp (q : ℕ) {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1))
    (γ : Cochain ((chains (ZMod q)).obj E') (res _ (tw q 1)) 2)
    (h0 : ∀ (U : Scheme.{0}) (x : Sx E' 0 U), ev γ 0 2 (by simp) U x = 0)
    (h1 : ∀ (U : Scheme.{0}) (x : Sx E' 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev γ 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v))
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E' 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) x →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 1 1 (by simp) U x =
        Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit (f ≫ L) (x.face 2) →
      w ^ q = lineUnit (f ≫ L) (x.face 0) →
      ev ((Cochain.ofHom ((chains (ZMod q)).map f)).comp γ (zero_add 2)) 2 0 (by simp) U x =
        kumT q U v + kumT q U w - kumT q U (v * w)) := by
  refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h0 U _
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]; exact h1 U _ v hv
  · rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.2.1 f γ]
    refine h2 U _ v w ?_ ?_
    · rw [← map_face]; exact hv
    · rw [← map_face]; exact hw

theorem face_forms (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2)
    (h2 : ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) :
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
      w ^ q = lineUnit L (x.face 0) → ev γ 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w) :=
  fun U x v w hv hw => h2 U x v w (by rw [sub_zero_one]; exact hv) (by rw [sub_one_one]; exact hw)

theorem firstChernClassTateTwist_pullback (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)) (hE' : Inv q E') :
    pull _ f _ _ (c1 q L) = c1 q (f ≫ L) := by
  have hE : Inv q E := fun U ⟨x⟩ => hE' U ⟨x.map f⟩
  obtain ⟨γ, hγ, h0, h1, h2⟩ := firstChernClassTateTwist_cocycle_representative q hE' L
  obtain ⟨γ', hγ', h0', h1', h2'⟩ := firstChernClassTateTwist_cocycle_representative q hE (f ≫ L)
  obtain ⟨k0, k1, k2⟩ := rep_comp q f L γ.1 h0 h1 (face_forms q L γ.1 h2)
  have key := rep_unique q hE (f ≫ L) _ γ'.1 k0 k1 k2 h0' h1' (face_forms q (f ≫ L) γ'.1 h2')
  rw [← hγ, ← hγ']
  change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map f)) γ (zero_add 2)) = _
  congr 1
  exact Cocycle.ext key

end GlobalTheory.EtC.ChernSpec

namespace GlobalTheory.EtC.ChernSpec
open GlobalTheory.EtC.ClsSpec
set_option backward.isDefEq.respectTransparency false

theorem isOneCochain_add (q : ℕ) [NeZero q] {E : Spc} (L M N : E ⟶ ofCat (glCat 1)) (hE : Inv q E)
    (hN : ∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) :
    c1 q N = c1 q L + c1 q M := by
  obtain ⟨γL, hL, l0, l1, l2⟩ := firstChernClassTateTwist_cocycle_representative q hE L
  obtain ⟨γM, hM, m0, m1, m2⟩ := firstChernClassTateTwist_cocycle_representative q hE M
  obtain ⟨γN, hN', n0, n1, n2⟩ := firstChernClassTateTwist_cocycle_representative q hE N
  have l2' := face_forms q L γL.1 l2
  have m2' := face_forms q M γM.1 m2
  have n2' := face_forms q N γN.1 n2
  have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
  obtain ⟨b, hb, hbv⟩ : ∃ b : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 0) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (b U x) = b V (x.res g)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → w ^ q = lineUnit M x →
        b U x = kumT q U v + kumT q U w - kumT q U (v * w) := by
    rcases kumT_cases q with ht | ht
    · exact exists_two_family ht hq₁ (fun U x => lineUnit L x) (fun U x => lineUnit M x)
        (fun V U g x => ClsSpec.lineUnit_res L g x) (fun V U g x => ClsSpec.lineUnit_res M g x)
    · refine ⟨fun _ _ => 0, fun V U g x => map_zero _, fun U x v w _ _ => ?_⟩
      rw [ht]
      simp
  obtain ⟨β, hβ1, hβ0⟩ := exists_single (R := ZMod q) (E := E) (I := res _ (tw q 1)) (n := 1) 1 0 (by simp) b hb
  rw [← hL, ← hM, ← hN', eq_comm, ← sub_eq_zero, ← CohomologyClass.mk_add, ← CohomologyClass.mk_sub,
    CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ 1 (by norm_num)]
  refine ⟨β, ?_⟩
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.2.1
  intro p t ht U x
  rw [Cocycle.coe_sub, Cocycle.coe_add, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).2.1,
    ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).1 _ _ p t ht U x).1]
  match p with
  | 0 =>
    obtain rfl : t = 2 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).1 x, hβ0 _ _ _ _ _ (by decide), smap_zero, l0, m0, n0]
    simp
  | 1 =>
    obtain rfl : t = 1 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 0 0 1 (by simp) ht x]
    rw [Finset.sum_eq_zero fun i _ => by rw [hβ0 _ _ _ _ _ (by decide), smul_zero], smul_zero, add_zero, hβ1]
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and (root_loc (hq₁ U x) (lineUnit L x))
      (root_loc (hq₁ U x) (lineUnit M x))) fun V g ⟨⟨v, hv⟩, w, hw⟩ => ?_)
    rw [← ClsSpec.lineUnit_res] at hv hw
    rw [res_map, hb, hbv V _ v w hv hw, res_sub, res_add,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 1 1 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 1 1 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 1 1 _ V U g x, l1 V _ v hv, m1 V _ w hw,
      n1 V _ (v * w) (by rw [mul_pow, hv, hw, hN]), smap_sub, smap_add]
  | 2 =>
    obtain rfl : t = 0 := by omega
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values (ZMod q) (by norm_num) β U).2 1 (-1) 0 (by simp) ht x]
    rw [hβ0 _ _ _ _ _ (by decide), smap_zero, zero_add, Fin.sum_univ_three, hβ1, hβ1, hβ1]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg]
    rw [Int.negOnePow_even 2 (by decide), one_smul, ← sub_eq_add_neg]
    have hU := hE U ⟨(x.face 0).face 0⟩
    refine ClsSpec.sep (ClsSpec.loc_mono (ClsSpec.loc_and
      (ClsSpec.loc_and (root_loc hU (lineUnit L (x.face 2))) (root_loc hU (lineUnit L (x.face 0))))
      (ClsSpec.loc_and (root_loc hU (lineUnit M (x.face 2))) (root_loc hU (lineUnit M (x.face 0)))))
      fun V g ⟨⟨⟨a, ha⟩, c, hc⟩, ⟨a', ha'⟩, c', hc'⟩ => ?_)
    rw [← lineUnit_face_res] at ha hc ha' hc'
    have hN2 : ∀ i, lineUnit N ((x.res g).face i) = lineUnit L ((x.res g).face i) * lineUnit M ((x.res g).face i) :=
      fun i => hN V _
    simp only [res_add, res_sub, neg_one_sq, one_smul]
    rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γL.1 2 0 _ V U g x, (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γM.1 2 0 _ V U g x,
      (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties (ZMod q)).2.1 γN.1 2 0 _ V U g x, l2' V _ a c ha hc, m2' V _ a' c' ha' hc',
      n2' V _ (a * a') (c * c') (by rw [mul_pow, ha, ha', hN2]) (by rw [mul_pow, hc, hc', hN2])]
    rw [hb, hb, hb, face_res, face_res, face_res,
      hbv V _ c c' (by rw [hc]) (by rw [hc']),
      hbv V _ (a * c) (a' * c') (by rw [lineUnit_face, mul_pow, ha, hc]) (by rw [lineUnit_face, mul_pow, ha', hc']),
      hbv V _ a a' ha ha']
    have e : a * c * (a' * c') = a * a' * (c * c') := by rw [mul_mul_mul_comm]
    rw [e]
    abel
  | p + 3 => exact sec_neg _ _ (by omega) _ _

end GlobalTheory.EtC.ChernSpec

theorem _root_.GlobalTheory.EtC.firstChernClassTateTwist_cocycle_naturality_additivity : ∀ (q : ℕ) [NeZero q], (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk γ = c1 q L ∧ (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧ (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x → ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧ ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) → ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧ (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' → pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧ ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E → (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) → c1 q N = c1 q L + c1 q M := by
  intro q _
  exact ⟨fun L hE => firstChernClassTateTwist_cocycle_representative q hE L, fun f L hE' => GlobalTheory.EtC.ChernSpec.firstChernClassTateTwist_pullback q f L hE',
    fun L M N hE hN => GlobalTheory.EtC.ChernSpec.isOneCochain_add q L M N hE hN⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH1Bijective
section
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh.Cx

theorem fnMap_h1_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (hA0 : K.M1.Ac0)
    (hA1 : K.M1.Ac1) (hB0 : K.M2.Ac0) : Function.Bijective K.fnMap.h1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hc : K.D1 c.1 = 0 := c.2
    rw [CxMap.h1, QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨g, hg⟩ := hx
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    refine ⟨g, ?_⟩
    have hf : ∀ T T' (φ : T ⟶ T'), c.1.1 T T' φ = g T' - K.M0.map φ (g T) := by
      intro T T' φ
      have := congrArg (fun p => p.1 T T' φ) hg
      exact this.symm
    have h2c : ∀ T T' (φ : T ⟶ T'),
        c.1.2 T' - K.M1.map φ (c.1.2 T) - K.d0 T' (c.1.1 T T' φ) = 0 := by
      intro T T' φ
      have := congrArg (fun p => p.2.1 T T' φ) hc
      simpa [Cx.D1] using this
    have hw := hA0 (fun T => c.1.2 T - K.d0 T (g T)) (by
      intro T T' φ
      have := h2c T T' φ
      rw [hf, map_sub, K.diffZero_natural] at this
      simp only [map_sub]
      rw [← sub_eq_zero, ← this]; abel)
    refine Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_) (funext fun T => ?_)
    · simp [Cx.D0, hf]
    · have := congrFun hw T
      simp only [Pi.zero_apply, sub_eq_zero] at this
      simp [Cx.D0, this]
  · intro y
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hc : (Cx.single K.M0).D1 c.1 = 0 := c.2
    have hδ : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (c.1.1 T T' φ) - c.1.1 T T'' (φ ≫ ψ) + c.1.1 T' T'' ψ = 0 := by
      intro T T' T'' φ ψ
      have := congrArg (fun p => p.1 T T' T'' φ ψ) hc
      simpa [Cx.D1] using this
    obtain ⟨w, hw⟩ := hA1 (fun T T' φ => K.d0 T' (c.1.1 T T' φ)) (by
      intro T T' T'' φ ψ
      have h := congrArg (K.d0 T'') (hδ T T' T'' φ ψ)
      simp only [map_add (f := _), map_sub, map_zero, K.diffZero_natural] at h ⊢
      rw [← sub_eq_zero, ← neg_eq_zero, ← h]; abel)
    have hdw := hB0 (fun T => K.d1 T (w T)) (by
      intro T T' φ
      have h := congrArg (K.d1 T') (hw T T' φ)
      rw [K.diffOne_diffZero, map_sub, K.diffOne_natural] at h
      exact (sub_eq_zero.mp h.symm))
    let z : K.Z1 := ⟨(c.1.1, w), by
      show K.D1 _ = 0
      refine Prod.ext (funext fun T => funext fun T' => funext fun T'' => funext fun φ =>
        funext fun ψ => ?_) (Prod.ext (funext fun T => funext fun T' => funext fun φ => ?_)
        (funext fun T => ?_))
      · simpa [Cx.D1] using hδ T T' T'' φ ψ
      · simp [Cx.D1, hw T T' φ]
      · simpa [Cx.D1] using congrFun hdw T⟩
    refine ⟨QuotientAddGroup.mk z, ?_⟩
    rw [CxMap.h1, QuotientAddGroup.map_mk]
    congr 1
end GlobalTheory.CxCoh.Cx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForgetPositiveH2Bijective
section
open CategoryTheory GlobalTheory.CxCoh

namespace GlobalTheory.CxCoh

theorem fnMap_h2_bijective (C : Type 1) [Category.{0} C] (K : Cx C) (h11 : K.M1.Ac1) (h12 : K.M1.Ac2)
    (h20 : K.M2.Ac0) (h21 : K.M2.Ac1) (h30 : K.M3.Ac0) : Function.Bijective K.fnMap.h2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = 0 at hc
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range] at hc
    obtain ⟨⟨f, ω0⟩, hf⟩ := hc
    have hz : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
        K.M0.map ψ (f T T' φ) - f T T'' (φ ≫ ψ) + f T' T'' ψ = a.1.1 T T' T'' φ ψ := by
      intro T T' T'' φ ψ
      have := congrArg (fun x => x.1 T T' T'' φ ψ) hf
      simp [Cx.D1, Cx.fnMap, CxMap.z2, CxMap.p2] at this
      exact this
    have ha := a.2
    obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
    obtain ⟨ω, hω⟩ := h11 (fun T T' φ => a.1.2.1 T T' φ + K.d0 T' (f T T' φ)) (by
      intro T T' T'' φ ψ
      rw [ha2 T T' T'' φ ψ, ← hz T T' T'' φ ψ]
      simp only [map_add (f := _), map_sub, K.diffZero_natural]
      abel)
    have hη : (fun T => a.1.2.2 T - K.d1 T (ω T)) = 0 := by
      apply h20
      intro T T' φ
      have e := hω T T' φ
      have e2 : a.1.2.1 T T' φ = ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) := by
        rw [← e]; abel
      rw [ha3 T T' φ, e2]
      simp only [map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddMonoidHom.mem_range]
    refine ⟨(f, ω), ?_⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext T T' T'' φ ψ
      exact hz T T' T'' φ ψ
    · funext T T' φ
      have e := hω T T' φ
      change ω T' - K.M1.map φ (ω T) - K.d0 T' (f T T' φ) = _
      rw [← e]; abel
    · funext T
      have e := congrFun hη T
      change K.d1 T (ω T) = _
      simp only [Pi.zero_apply, sub_eq_zero] at e
      exact e.symm
  · intro c
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨hb1, -, -, -⟩ := b.2
    obtain ⟨f, hf⟩ := h12 (fun T T' T'' φ ψ => K.d0 T'' (b.1.1 T T' T'' φ ψ)) (by
      intro T T' T'' T''' φ ψ χ
      rw [← K.diffZero_natural, ← map_add (f := _), hb1, map_add (f := _)])
    obtain ⟨g, hg⟩ := h21 (fun T T' φ => K.d1 T' (-f T T' φ)) (by
      intro T T' T'' φ ψ
      have e := hf T T' T'' φ ψ
      have e2 : f T T'' (φ ≫ ψ) = K.M1.map ψ (f T T' φ) + f T' T'' ψ - K.d0 T'' (b.1.1 T T' T'' φ ψ) := by
        rw [e]; abel
      rw [e2]
      simp only [map_neg, map_add (f := _), map_sub, K.diffOne_diffZero, K.diffOne_natural]
      abel)
    have h3 : (fun T => K.d2 T (g T)) = 0 := by
      apply h30
      intro T T' φ
      have e := hg T T' φ
      have e2 : g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ) := by rw [e]; abel
      rw [e2, map_add (f := _), K.diffTwo_comp_diffOne, add_zero, K.diffTwo_natural]
    let a : K.Z2 := ⟨(b.1.1, fun T T' φ => -f T T' φ, g), by
      refine ⟨hb1, fun T T' T'' φ ψ => ?_, fun T T' φ => ?_, fun T => ?_⟩
      · rw [hf T T' T'' φ ψ]; simp only [map_neg, map_sub, map_add (f := _)]; abel
      · have e := hg T T' φ
        change g T' = K.M2.map φ (g T) + K.d1 T' (-f T T' φ)
        rw [e]; abel
      · exact congrFun h3 T⟩
    refine ⟨QuotientAddGroup.mk a, ?_⟩
    change (QuotientAddGroup.mk (K.fnMap.z2 a) : (Cx.single K.M0).H2) = QuotientAddGroup.mk b
    congr 1
end GlobalTheory.CxCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBounds
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem natCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    refine le_trans (le_min ih (by simp)) (v.map_add _ _)

theorem intCast_isInt {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  cases n with
  | ofNat k => simpa using natCast_isInt v k
  | negSucc k =>
    rw [Int.cast_negSucc, v.map_neg]
    exact_mod_cast natCast_isInt v (k + 1)

theorem detDepth_bounds : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C),
    IsSatFrame v u → 0 ≤ detDepth G u c ∧ detDepth G u c ≤ content v (detPow C i c) ∧
    detDepth G u c ≤ (((i * c : ℝ) / (p - 1) : ℝ) : EReal) := by
  intro C _ _ v p hp hv i d c G u hu
  obtain ⟨hhom, hint, -, -⟩ := _root_.GlobalTheory.DetPowShape.detPow_shape C i c
  have h0 : 0 ≤ detDepth G u c := by
    unfold detDepth
    exact _root_.GlobalTheory.DepthNonneg.depth_nonneg C v (Fin i) (fun _ => d) (fun _ => G) (fun _ => Fin i) (fun _ => u)
      (detPow C i c) (fun _ a e => hu.1 a e)
      (fun α => by obtain ⟨n, hn⟩ := hint α; rw [hn]; exact intCast_isInt v n)
  have h1 : detDepth G u c ≤ content v (detPow C i c) := by
    unfold detDepth
    exact GlobalTheory.T.differentialOperatorDepth_le_dividedPowerContent C v (Fin i) (fun _ => d) (fun _ => i) (fun _ => G) (fun _ => u)
      (detPow C i c) (i * c) hhom (fun _ => hu)
  exact ⟨h0, h1, h1.trans (_root_.GlobalTheory.DetPowContent.content_detPow_bounds C v p hp hv i c).1⟩

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraProductCuspidalGLFrobeniusPow
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem hc_congr_deg {F : Type} [Field F] (a b b' : ℕ) (α : GL (Fin a) F → ℂ)
    (β : (m : ℕ) → GL (Fin m) F → ℂ) (n : ℕ) (h : b = b') :
    hc a b α (β b) n = hc a b' α (β b') n := by
  subst h; rfl

theorem deg_map_mul (L : List (ℕ × ℕ)) (c : ℕ) :
    deg (L.map fun p => (p.1, p.2 * c)) = deg L := by
  unfold deg
  rw [List.map_map]
  rfl

theorem J_gal : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t : F ≃+* F) (j : ℕ),
    (∀ x, t x = x ^ (ringChar F ^ j)) → ∀ (L : List (ℕ × ℕ)) (n : ℕ) (x : GL (Fin n) F),
    J θ L n (gal (t : F →+* F) n x) = J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) n x := by
  intro F _ _ θ t j ht L
  induction L with
  | nil => intro n x; rfl
  | cons p L ih =>
    intro n x
    rw [List.map_cons, J_cons, J_cons, GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism F t]
    have h1 : (fun y => cusp θ p.1 p.2 (gal (t : F →+* F) p.1 y)) = cusp θ p.1 (p.2 * ringChar F ^ j) := by
      funext y; exact GlobalTheory.T.cuspidalCharacterGLFiniteField_frobenius_pow F θ t j ht p.1 p.2 y
    have h2 : (fun y => J θ L (deg L) (gal (t : F →+* F) (deg L) y)) =
        J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j)) (deg L) := by
      funext y; exact ih (deg L) y
    rw [h1, h2]
    exact congrFun (hc_congr_deg p.1 (deg L) _ _ (J θ (L.map fun p => (p.1, p.2 * ringChar F ^ j))) n
      (deg_map_mul L _).symm) x

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfIsIntegralAlgebraicNumbers
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isAlgebraic_of_isIntegral_algebraicNumbers {x : ℂ}
    (hx : IsIntegral (integralClosure ℚ ℂ).toSubring x) : IsAlgebraic ℚ x := by
  have hx' : IsIntegral (integralClosure ℚ ℂ) x := hx
  exact (isIntegral_trans (R := ℚ) (A := integralClosure ℚ ℂ) x hx').isAlgebraic

theorem fam_value_isAlgebraic : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by
  intro ι _ act w N f τ₀ Ω hN hb hf hq hj hΩ i
  refine isAlgebraic_of_isIntegral_algebraicNumbers
    (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N f (integralClosure ℚ ℂ).toSubring τ₀ Ω hN hb hf (fun k => ?_) ?_ hΩ i)
  · obtain ⟨a, ha, hal⟩ := hq k
    exact ⟨a, ha, fun n => (hal n).isIntegral⟩
  · exact isIntegral_algebraMap (R := (integralClosure ℚ ℂ).toSubring) (A := ℂ)
      (x := ⟨jT τ₀, hj.isIntegral⟩)

end GlobalTheory.QFam
end

