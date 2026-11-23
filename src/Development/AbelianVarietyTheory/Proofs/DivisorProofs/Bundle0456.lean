module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeLocallyExactOfComponentSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.ConeSec

variable {R : Type} [CommRing R]

lemma smap_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

lemma smap_add {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

lemma smap_neg {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (-a) x = -Sec.map a x := rfl

lemma smap_sub {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a - b) x = Sec.map a x - Sec.map b x := rfl

lemma smap_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

lemma smap_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := (a.hom.app (op U)).hom.map_add x y

lemma smap_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := (a.hom.app (op U)).hom.map_neg x

lemma sres_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := a.hom.naturality g.op
  exact congrArg (fun t => t.hom x) this.symm

lemma smap_zero {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := (a.hom.app (op U)).hom.map_zero

lemma sres_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := (F.obj.map g.op).hom.map_add x y

end GlobalTheory.EtC.ConeSec


open GlobalTheory.EtC.ConeSec in
theorem GlobalTheory.EtC.cone_sec_exact : ∀ (R : Type) [CommRing R] {I J : Cx R} (f : I ⟶ J) (U : Scheme.{0}) (n : ℤ), (∀ (b₁ : Sec (I.X (n + 1)) U) (b₂ : Sec (J.X n) U), Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 → Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec (I.X n) V) (a₂ : Sec (J.X (n - 1)) V), Sec.map (I.d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map (f.f n) a₁ + Sec.map (J.d (n - 1) n) a₂ = Sec.res g b₂) → ∀ b : Sec ((mappingCone f).X n) U, Sec.map ((mappingCone f).d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec ((mappingCone f).X (n - 1)) V, Sec.map ((mappingCone f).d (n - 1) n) a = Sec.res g b := by
  intro R _ I J f U n hyp b hb
  obtain ⟨b₁, hb₁⟩ : ∃ x, Sec.map ((mappingCone.fst f).1.v n (n + 1) rfl) b = x := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x, Sec.map ((mappingCone.snd f).v n n (add_zero n)) b = x := ⟨_, rfl⟩
  have h1 : Sec.map (I.d (n + 1) (n + 2)) b₁ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_fst_v f n (n + 1) (n + 2) rfl (by ring))
    simp only [smap_comp, smap_neg, hb, smap_zero, hb₁] at e
    exact neg_eq_zero.mp e.symm
  have h2 : Sec.map (f.f (n + 1)) b₁ + Sec.map (J.d n (n + 1)) b₂ = 0 := by
    have e := congrArg (fun φ => Sec.map φ b) (mappingCone.d_snd_v f n (n + 1) rfl)
    simp only [smap_comp, smap_add, hb, smap_zero, hb₁, hb₂] at e
    exact e.symm
  have hid := congrArg (fun φ => Sec.map φ b) (mappingCone.id_X f n (n + 1) rfl)
  simp only [smap_comp, smap_add, smap_id, hb₁, hb₂] at hid
  obtain ⟨S, hS, h⟩ := hyp b₁ b₂ h1 h2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a₁, a₂, e1, e2⟩ := h V g hg
  refine ⟨Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁ + Sec.map ((mappingCone.inr f).f (n - 1)) a₂, ?_⟩
  have k1 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inl f).v n (n - 1) (by ring)) a₁) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (f.f n) a₁) -
        Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.map (I.d n (n + 1)) a₁) := by
    rw [← smap_comp, mappingCone.inl_v_d f n (n - 1) (n + 1) (by ring) (by ring), smap_sub, smap_comp, smap_comp]
  have k2 : Sec.map ((mappingCone f).d (n - 1) n) (Sec.map ((mappingCone.inr f).f (n - 1)) a₂) =
      Sec.map ((mappingCone.inr f).f n) (Sec.map (J.d (n - 1) n) a₂) := by
    rw [← smap_comp, mappingCone.inr_f_d, smap_comp]
  have k3 : Sec.res g b = Sec.map ((mappingCone.inl f).v (n + 1) n (by ring)) (Sec.res g b₁) +
      Sec.map ((mappingCone.inr f).f n) (Sec.res g b₂) := by
    rw [← hid, sres_add, sres_map, sres_map]
  rw [smap_add', k1, k2, e1, k3, ← e2, smap_add', smap_neg']
  abel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeResolutionLocalChaseOnSupport
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.ConeChase

variable {R : Type} [CommRing R]

theorem map_comp {F G K : Shv R} (a : F ⟶ G) (b : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem map_congr {F G : Shv R} {a b : F ⟶ G} (h : a = b) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a x = Sec.map b x := by rw [h]

theorem map_zero_hom {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (0 : F ⟶ G) x = 0 := rfl

theorem map_add' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) :
    Sec.map a (x + y) = Sec.map a x + Sec.map a y := map_add _ _ _

theorem map_neg' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map a (-x) = -Sec.map a x := map_neg _ _

theorem map_zero' {F G : Shv R} (a : F ⟶ G) {U : Scheme.{0}} :
    Sec.map a (0 : Sec F U) = 0 := map_zero _

theorem res_add {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) :
    Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ _ _

theorem res_zero {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero _

theorem res_map {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (a.hom.naturality g.op)
  exact this.symm

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  have := congrArg (fun t => t.hom x) (F.obj.map_comp g.op k.op)
  exact this

theorem comm' {I J : Cx R} (f : I ⟶ J) (i j : ℤ) {U : Scheme.{0}} (x : Sec (I.X i) U) :
    Sec.map (J.d i j) (Sec.map (f.f i) x) = Sec.map (f.f j) (Sec.map (I.d i j) x) :=
  map_congr (f.comm i j) x

theorem mappingCone_resolution_localChase_of_succ (E : Spc) {F G : Shv R} (φ : F ⟶ G)
    (hφ : ∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U)))
    (U : Scheme.{0}) (hU : Nonempty (Sx E 0 U)) (m n k l : ℤ) (hm : m + 1 = n) (hk : n + 1 = k) (hl : k + 1 = l)
    (b₁ : Sec ((res R F).X k) U) (b₂ : Sec ((res R G).X n) U)
    (h₁ : Sec.map ((res R F).d k l) b₁ = 0)
    (h₂ : Sec.map ((resMap R φ).f k) b₁ + Sec.map ((res R G).d n k) b₂ = 0) :
    Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X m) V),
      Sec.map ((res R F).d n k) a₁ = -Sec.res g b₁ ∧
      Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d m n) a₂ = Sec.res g b₂ := by
  obtain ⟨Lall, Lmono, -, -, Ltrans, -, -⟩ := GlobalTheory.T.etaleLocal_property_calculus_rules
  have hι := ((_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.2.2.2.2.2.2 G φ).2
  have hd := (_root_.GlobalTheory.EtC.ResBasic.res_basic R F).2.2.2.2.2.2.1
  rcases lt_or_ge n 0 with hn | hn
  · have hb₂ : b₂ = 0 := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.2.2 n hn).elim _ _
    have hb₁ : b₁ = 0 := by
      rcases lt_or_ge k 0 with hk0 | hk0
      · exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 k hk0).elim _ _
      · obtain rfl : k = 0 := by omega
        obtain rfl : l = 1 := by omega
        obtain ⟨s, rfl⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).1 b₁).1 h₁
        rw [hb₂, map_zero', add_zero, ← map_comp, map_congr hι, map_comp] at h₂
        have h3 : Sec.map φ s = 0 := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G U).2.1 (by rw [h₂, map_zero'])
        have h4 : s = 0 := (hφ U hU).1 (by rw [h3, map_zero'])
        rw [h4, map_zero']
    refine Lall _ _ fun V g => ⟨0, 0, ?_, ?_⟩
    · rw [hb₁, map_zero', res_zero, neg_zero]
    · rw [hb₂, map_zero', map_zero', res_zero, add_zero]
  · apply Ltrans
    refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.1 n k l (by omega) hk b₁ hl h₁) ?_
    rintro V g ⟨y, hy⟩
    have hc : Sec.map ((res R G).d n k) (Sec.res g b₂ + Sec.map ((resMap R φ).f n) y) = 0 := by
      rw [map_add', comm', hy, ← res_map, ← res_map, ← res_add, add_comm, h₂, res_zero]
    rcases lt_or_eq_of_le hn with hn' | hn'
    · refine Lmono _ _ _ ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).2.2.1 m n k hn' hm _ hk hc) ?_
      rintro W j ⟨z, hz⟩
      refine ⟨-Sec.res j y, z, ?_, ?_⟩
      · rw [map_neg', ← res_map, hy, res_comp]
      · rw [hz, map_neg', res_add, res_map, res_comp]; abel
    · subst hn'
      obtain rfl : k = 1 := by omega
      obtain ⟨s, hs⟩ := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R G V).1 _).1 hc
      obtain ⟨x⟩ := hU
      obtain ⟨t, rfl⟩ := (hφ V ⟨Sx.res g x⟩).2 s
      refine Lall _ _ fun W j => ⟨Sec.res j (-y + Sec.map (resι R F) t), 0, ?_, ?_⟩
      · rw [← res_map, map_add', map_neg', hy, ← map_comp, map_congr hd, map_zero_hom, add_zero, res_comp]
        exact map_neg _ _
      · rw [map_zero', add_zero, ← res_map, map_add', map_neg', ← map_comp, map_congr hι, map_comp, hs, res_comp]
        congr 1
        abel

theorem chase : ∀ (R : Type) [CommRing R] (E : Spc) {F G : Shv R} (φ : F ⟶ G), (∀ U : Scheme.{0}, Nonempty (Sx E 0 U) → Function.Bijective (Sec.map φ (U := U))) → ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b₁ : Sec ((res R F).X (n + 1)) U) (b₂ : Sec ((res R G).X n) U), Sec.map ((res R F).d (n + 1) (n + 2)) b₁ = 0 → Sec.map ((resMap R φ).f (n + 1)) b₁ + Sec.map ((res R G).d n (n + 1)) b₂ = 0 → Loc U fun V g => ∃ (a₁ : Sec ((res R F).X n) V) (a₂ : Sec ((res R G).X (n - 1)) V), Sec.map ((res R F).d n (n + 1)) a₁ = -Sec.res g b₁ ∧ Sec.map ((resMap R φ).f n) a₁ + Sec.map ((res R G).d (n - 1) n) a₂ = Sec.res g b₂ :=
  fun _ _ E _ _ φ hφ U hU n b₁ b₂ h₁ h₂ =>
    mappingCone_resolution_localChase_of_succ E φ hφ U hU (n - 1) n (n + 1) (n + 2) (by ring) rfl (by ring) b₁ b₂ h₁ h₂

end GlobalTheory.EtC.ConeChase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory

def coneSES {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : ShortComplex (Shv R) :=
  ShortComplex.mk ((mappingCone.inr u).f t) ((mappingCone.fst u).1.v t (t + 1) rfl) (by simp)

def coneSESSplitting {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).Splitting where
  r := (mappingCone.snd u).v t t (add_zero t)
  s := (mappingCone.inl u).v (t + 1) t (by omega)
  f_r := by simp [coneSES]
  s_g := by simp [coneSES]
  id := by
    rw [add_comm]
    exact mappingCone.id_X u t (t + 1) rfl

theorem coneSES_shortExact {R : Type} [CommRing R] {C J : Cx R} (u : C ⟶ J) (t : ℤ) : (coneSES u t).ShortExact :=
  (coneSESSplitting u t).shortExact

theorem sgl_isKInjective {R : Type} [CommRing R] (I : Shv R) [Injective I] : (sgl I).IsKInjective := by
  haveI : ∀ n, Injective ((sgl I).X n) := by
    intro n
    by_cases h : n = 0
    · subst h
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 I).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I n h).injective
  exact CochainComplex.isKInjective_of_injective _ 0

theorem sgl_cohomologyClass_subsingleton {R : Type} [CommRing R] (G I : Shv R) (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (sgl I) i) := by
  have hc : ∀ a b : Cochain (sgl G) (sgl I) i, a = b := by
    intro a b
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    by_cases hp : p = 0
    · have hq : q ≠ 0 := by omega
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 I q hq).eq_of_tgt _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G p hp).eq_of_src _ _
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := x.mk_surjective
  obtain ⟨b, rfl⟩ := y.mk_surjective
  exact congrArg CohomologyClass.mk (Cocycle.ext (hc _ _))

theorem ext_injective_subsingleton {R : Type} [CommRing R] (G I : Shv R) [Injective I] (i : ℤ) (hi : i ≠ 0) :
    Subsingleton (CohomologyClass (sgl G) (res R I) i) := by
  obtain ⟨hK, -, -, hq, -⟩ := _root_.GlobalTheory.EtC.ResBasic.res_basic R I
  haveI := hK
  haveI := hq
  haveI := sgl_isKInjective I
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (resAug I)).1 hq
  have h63 := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have hsurj : Function.Surjective (cpush (sgl G) (resAug I) i) := by
    intro y
    refine ⟨cpush (sgl G) e.inv i y, ?_⟩
    rw [← h63.2.2.1 (sgl G) e.inv (resAug I) i y, ← he,
      (h63.2.2.2.2 _ _ ⟨e.homotopyInvHomId⟩ (sgl G) i).2, (h63.1 (sgl G) _ i y).2]
  haveI := sgl_cohomologyClass_subsingleton G I i hi
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

theorem cone_terms_ext_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J),
    (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) →
    ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  intro R _ G C J u hJ hC t i hi
  obtain ⟨z, hz⟩ := GlobalTheory.T.etaleCohomology_coefficient_longExactSequence R (coneSES u t) (coneSES_shortExact u t)
  have hex := (hz (sgl G) i).1
  haveI := hJ t
  haveI hsJ : Subsingleton (CohomologyClass (sgl G) (res R (J.X t)) i) := ext_injective_subsingleton G (J.X t) i hi.ne'
  haveI hsC : Subsingleton (CohomologyClass (sgl G) (res R (C.X (t + 1))) i) := hC (t + 1) i hi
  constructor
  intro x y
  obtain ⟨w, hw⟩ := (hex x).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  obtain ⟨w', hw'⟩ := (hex y).1 (Subsingleton.elim (α := CohomologyClass (sgl G) (res R (C.X (t + 1))) i) _ _)
  rw [← hw, ← hw', @Subsingleton.elim _ hsJ w w']

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularForm
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory

theorem heightOne_eq_span_irreducible : ∀ (k F : Type) [Field k] [Field F] [Algebra k F] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F), A = Algebra.adjoin k (Set.range u) → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∃ t : A, Irreducible t ∧ p = Ideal.span {t} := by
  intro k F _ _ _ d u hu A hA p hp hh
  subst hA
  haveI := hp
  haveI : UniqueFactorizationMonoid (Algebra.adjoin k (Set.range u)) :=
    hu.aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
  refine ⟨g, ?_, hg⟩
  have hne : g ≠ 0 := by
    rintro rfl
    exact p.ne_bot_of_height_eq_one hh (by rw [hg]; simp)
  rw [hg] at hp
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

theorem mem_traceDual_localization_iff_forall_regularForm : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  intro k F K _ _ _ _ _ _ _ _ _ d u hu A _ hA B hB hsm τ hτ p hp hh z
  obtain ⟨t, ht, hpt⟩ := heightOne_eq_span_irreducible k F d u hu A hA p hp hh
  have h2 : ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → Q.height = 1 :=
    fun Q hQ hov => GlobalTheory.T.height_eq_one_of_liesOver_height_one k F K A B hB p hp hh Q hQ hov
  have h3 := fun Q hQ hov => GlobalTheory.T.exists_uniformizer_ramification_of_height_one k F K d u hu A hA B hB p hp t ht hpt Q hQ (h2 Q hQ hov) hov
  rw [GlobalTheory.T.trace_mem_localization_iff_forall_prime_alt k F K d u hu A hA B hB p hp hh t ht hpt h2 h3 z]
  constructor
  · intro hl Q hQ hov
    obtain ⟨s, e, he, hs, hun, htd⟩ := h3 Q hQ hov
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mpr
      (hl Q hQ hov s e he hs hun htd)
  · intro hr Q hQ hov s e he hs hun htd
    exact (GlobalTheory.T.regular_topForm_pole_order_height_one_prime k F K d u hu A hA B hB hsm τ hτ Q hQ (h2 Q hQ hov) t s e ht he hs hun htd z).mp (hr Q hQ hov)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalised
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticGaussianNormalised : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  intro l _ _
  have hS : CompanionTheory.ThKR.Mp.SecEx l := CompanionTheory.ThKR.Mp.secEx_of CompanionTheory.ThKR.Mp.mkElt CompanionTheory.ThKR.Mp.nrmUp
  have hO : CompanionTheory.ThKR.Mp.Surj l := CompanionTheory.ThKR.Mp.surj_of CompanionTheory.ThKR.Mp.ddNe hS
  have hC : CompanionTheory.ThKR.Mp.Cover l :=
    CompanionTheory.ThKR.Mp.cover_of CompanionTheory.ThKR.Mp.topG hO CompanionTheory.ThKR.Mp.ker hS CompanionTheory.ThKR.Mp.secDer
  haveI : IsTopologicalGroup (CompanionTheory.ThKR.Mp.G l) := CompanionTheory.ThKR.Mp.topG
  refine ⟨CompanionTheory.ThKR.Mp.G l, inferInstance, inferInstance, inferInstance, CompanionTheory.ThKR.Mp.pr, CompanionTheory.ThKR.Mp.om,
    CompanionTheory.ThKR.Mp.omS, CompanionTheory.ThKR.Mp.MpA.gs l, hC, hO, CompanionTheory.ThKR.Mp.ker, CompanionTheory.ThKR.Mp.continuous_om,
    CompanionTheory.ThKR.Mp.om_rho, CompanionTheory.ThKR.Mp.om_sch, ?_, ?_, ?_⟩
  · intro x
    rw [CompanionTheory.ThKR.Mp.MpA.gs, GroundTheory.Global.gaussianSchwartz_apply]
    have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [e, Complex.ofReal_exp]
    push_cast
    ring_nf
  · intro j
    have h := CompanionTheory.ThKR.Mp.MpA.ann_gs (l := l) j
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, one_mulVec, one_mulVec] at h
    exact h
  · intro g P hP
    have h := CompanionTheory.ThKR.Mp.omS_nrm g 1 (CompanionTheory.ThKR.Mp.MpA.gs l) CompanionTheory.ThKR.Mp.MpA.ann_gs
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, Matrix.mul_one, CompanionTheory.ThKR.Mp.MpA.gs_zero, CompanionTheory.ThKR.Mp.MpA.dd_one, one_pow, one_mul] at h
    have eP : P = CompanionTheory.ThKR.Mp.upperParabolic (CompanionTheory.ThKR.Mp.pr g).1 := by
      ext a b; rw [hP]; rfl
    rw [eP]
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
section
noncomputable section

open NumberField

namespace GlobalTheory.HeckeStrip

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def wt (φ : I → K →+* ℂ) (n : I → ℤ) (α : K) : ℂ :=
  ∏ i, (φ i α / ((‖φ i α‖ : ℝ) : ℂ)) ^ (-n i)

def pval (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (J : Ideal (𝓞 K)) [J.IsPrincipal] : ℂ :=
  F (Submodule.IsPrincipal.generator J) * wt φ n ((Submodule.IsPrincipal.generator J : 𝓞 K) : K)

def pSeries (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (s : ℂ) : ℂ :=
  ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
    (haveI := J.2.2; pval F φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)

theorem wt_mul (φ : I → K →+* ℂ) (n : I → ℤ) (a b : K) : wt φ n (a * b) = wt φ n a * wt φ n b := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]

theorem norm_wt (φ : I → K →+* ℂ) (n : I → ℤ) {a : K} (ha : a ≠ 0) : ‖wt φ n a‖ = 1 := by
  unfold wt
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have h : φ i a ≠ 0 := (map_ne_zero _).2 ha
  rw [norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h), one_zpow]

end GlobalTheory.HeckeStrip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundary
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_invertibleLocus_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dite_eq_left h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]

end GlobalTheory.CatCoh.Desc.Basis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistIsFreeRankOneOnGeneratorSectionStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection : ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)), Gen (tw q i) S (twGen i ζ) := by
  first | (exact @GlobalTheory.twGen_gen) | (exact GlobalTheory.twGen_gen) | (intros; apply GlobalTheory.twGen_gen  <;> assumption)
end

