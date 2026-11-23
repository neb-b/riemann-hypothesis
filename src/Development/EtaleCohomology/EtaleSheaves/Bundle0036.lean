module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0025
public import Development.EtaleCohomology.EtaleSheaves.Bundle0021
public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.EtaleCohomology.EtaleSheaves.Bundle0023
public import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ColimHensPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.ColimHensPf

variable {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}}
  (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) {c : Cocone D}

lemma beta_nat {j j' : J} (f : j ⟶ j') (b : B) : (D.map f).hom ((β.app j).hom b) = (β.app j').hom b := by
  have h := congrArg (fun g => g.hom b) (β.naturality f)
  simpa using h.symm

lemma iota_nat (c : Cocone D) {j j' : J} (f : j ⟶ j') (x : D.obj j) :
    (c.ι.app j').hom ((D.map f).hom x) = (c.ι.app j).hom x := by
  have h := congrArg (fun g => g.hom x) (c.w f)
  simpa using h

lemma mapI (I : Ideal B) {j j' : J} (f : j ⟶ j') {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (D.map f).hom x ∈ I.map (β.app j').hom := by
  have h : (D.map f).hom.comp (β.app j).hom = (β.app j').hom := RingHom.ext (beta_nat β f)
  have := Ideal.mem_map_of_mem (D.map f).hom hx
  rwa [Ideal.map_map, h] at this

def phi (c : Cocone D) : B →+* c.pt :=
  (c.ι.app (IsFiltered.nonempty (C := J)).some).hom.comp (β.app (IsFiltered.nonempty (C := J)).some).hom

lemma phi_eq (c : Cocone D) (j : J) (b : B) : (c.ι.app j).hom ((β.app j).hom b) = phi β c b := by
  let j0 := (IsFiltered.nonempty (C := J)).some
  show _ = (c.ι.app j0).hom ((β.app j0).hom b)
  rw [← iota_nat c (IsFiltered.leftToMax j j0), ← iota_nat c (IsFiltered.rightToMax j j0), beta_nat, beta_nat]

lemma KofI (c : Cocone D) (I : Ideal B) {j : J} {x : D.obj j} (hx : x ∈ I.map (β.app j).hom) :
    (c.ι.app j).hom x ∈ I.map (phi β c) := by
  have h : (c.ι.app j).hom.comp (β.app j).hom = phi β c := RingHom.ext (phi_eq β c j)
  have := Ideal.mem_map_of_mem (c.ι.app j).hom hx
  rwa [Ideal.map_map, h] at this

variable (hc : IsColimit c)
include hc

lemma rep (z : c.pt) : ∃ j, ∃ y : D.obj j, (c.ι.app j).hom y = z :=
  Concrete.isColimit_exists_rep D hc z

lemma rep_above (j : J) (z : c.pt) : ∃ (j' : J) (_ : j ⟶ j') (y : D.obj j'), (c.ι.app j').hom y = z := by
  obtain ⟨j1, y, rfl⟩ := rep hc z
  exact ⟨IsFiltered.max j j1, IsFiltered.leftToMax j j1, (D.map (IsFiltered.rightToMax j j1)).hom y, iota_nat c _ y⟩

lemma eq_later {j : J} (x y : D.obj j) (h : (c.ι.app j).hom x = (c.ι.app j).hom y) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = (D.map f).hom y := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq D hc x y h
  refine ⟨_, f ≫ IsFiltered.coeqHom f g, ?_⟩
  have hfg' : (D.map f).hom x = (D.map g).hom y := hfg
  calc (D.map (f ≫ IsFiltered.coeqHom f g)).hom x
        = (D.map (IsFiltered.coeqHom f g)).hom ((D.map f).hom x) := by simp
    _ = (D.map (IsFiltered.coeqHom f g)).hom ((D.map g).hom y) := by rw [hfg']
    _ = (D.map (g ≫ IsFiltered.coeqHom f g)).hom y := by simp
    _ = (D.map (f ≫ IsFiltered.coeqHom f g)).hom y := by rw [IsFiltered.coeq_condition]

lemma zero_later {j : J} (x : D.obj j) (h : (c.ι.app j).hom x = 0) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom x = 0 := by
  obtain ⟨j', f, hf⟩ := eq_later hc x 0 (by rw [h, map_zero])
  exact ⟨j', f, by rw [hf, map_zero]⟩

lemma Krep (I : Ideal B) {k : c.pt} (hk : k ∈ I.map (phi β c)) :
    ∃ j, ∃ x : D.obj j, x ∈ I.map (β.app j).hom ∧ (c.ι.app j).hom x = k := by
  have hk' : k ∈ Ideal.span (phi β c '' I) := hk
  clear hk
  induction hk' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨(IsFiltered.nonempty (C := J)).some, _, Ideal.mem_map_of_mem _ hi, phi_eq β c _ i⟩
  | zero => exact ⟨(IsFiltered.nonempty (C := J)).some, 0, zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨j1, x1, h1, rfl⟩ := hx
    obtain ⟨j2, x2, h2, rfl⟩ := hy
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom x1 +
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, add_mem (mapI β I _ h1) (mapI β I _ h2), ?_⟩
    rw [map_add (f := _), iota_nat, iota_nat]
  | smul a x _ hx =>
    obtain ⟨j2, x2, h2, rfl⟩ := hx
    obtain ⟨j1, y, rfl⟩ := rep hc a
    refine ⟨IsFiltered.max j1 j2, (D.map (IsFiltered.leftToMax j1 j2)).hom y *
      (D.map (IsFiltered.rightToMax j1 j2)).hom x2, Ideal.mul_mem_left _ _ (mapI β I _ h2), ?_⟩
    rw [map_mul, iota_nat, iota_nat, smul_eq_mul]

lemma memK_descend (I : Ideal B) {j : J} (y : D.obj j) (hy : (c.ι.app j).hom y ∈ I.map (phi β c)) :
    ∃ (j' : J) (f : j ⟶ j'), (D.map f).hom y ∈ I.map (β.app j').hom := by
  obtain ⟨j1, x, hx, hxe⟩ := Krep β hc I hy
  let l := IsFiltered.leftToMax j j1
  let r := IsFiltered.rightToMax j j1
  obtain ⟨j', g, hg⟩ := zero_later hc ((D.map l).hom y - (D.map r).hom x)
    (by rw [map_sub, iota_nat, iota_nat, hxe, sub_self])
  refine ⟨j', l ≫ g, ?_⟩
  rw [map_sub, sub_eq_zero] at hg
  have : (D.map (l ≫ g)).hom y = (D.map (r ≫ g)).hom x := by simpa using hg
  rw [this]
  exact mapI β I _ hx

lemma poly_lift (g : Polynomial c.pt) : ∃ j, g ∈ Polynomial.lifts (c.ι.app j).hom := by
  have mono : ∀ {j j' : J} (f : j ⟶ j') (g : Polynomial c.pt),
      g ∈ Polynomial.lifts (c.ι.app j).hom → g ∈ Polynomial.lifts (c.ι.app j').hom := by
    intro j j' f g ⟨q, hq⟩
    refine ⟨q.map (D.map f).hom, ?_⟩
    have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
    simp only [Polynomial.coe_mapRingHom] at hq ⊢
    rw [Polynomial.map_map, h, hq]
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨j1, h1⟩ := hp
    obtain ⟨j2, h2⟩ := hq
    exact ⟨_, add_mem (mono (IsFiltered.leftToMax j1 j2) _ h1)
      (mono (IsFiltered.rightToMax j1 j2) _ h2)⟩
  | monomial n a =>
    obtain ⟨j, y, hy⟩ := rep hc a
    exact ⟨j, Polynomial.monomial_mem_lifts n ⟨y, hy⟩⟩

omit hc in
lemma ev_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : Polynomial R) (b : R) :
    φ (p.eval b) = (p.map φ).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

omit hc in
lemma pmap (c : Cocone D) {j j' : J} (f : j ⟶ j') (p : Polynomial (D.obj j)) :
    (p.map (D.map f).hom).map (c.ι.app j').hom = p.map (c.ι.app j).hom := by
  have h : (c.ι.app j').hom.comp (D.map f).hom = (c.ι.app j).hom := RingHom.ext (iota_nat c f)
  rw [Polynomial.map_map, h]

end LateralTheory.E.ColimHensPf

namespace LateralTheory.E.ColimHensPf
open LateralTheory.E.ColimHensPf

theorem ColimHens_of : LateralTheory.E.HensCut.ColimHens := by
  intro B _ I J _ _ D β c hc ha hb hcc
  refine ⟨I.map (phi β c), ⟨?_, ?_⟩, ⟨RingEquiv.ofBijective
    (Ideal.quotientMap (I.map (phi β c)) (phi β c) Ideal.le_comap_map) ⟨?_, ?_⟩⟩⟩
  ·
    intro k hk
    rw [Ring.mem_jacobson_iff]
    intro y
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I (Ideal.mul_mem_right y _ hk)
    obtain ⟨j', f, hu⟩ := hb j x hx
    have := hu.map (c.ι.app j').hom
    rw [iota_nat, map_add (f := _), map_one, hxe, add_comm] at this
    exact this
  ·
    intro g hg a₀ hev hder
    by_cases hnt : Nontrivial c.pt
    swap
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨a₀, Subsingleton.elim _ _, by rw [sub_self]; exact zero_mem _⟩
    obtain ⟨j1, hj1⟩ := poly_lift hc g
    haveI : Nontrivial (((Functor.const J).obj c.pt).obj j1) := hnt
    obtain ⟨p, hp, -, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic hj1 hg
    obtain ⟨w, hw⟩ := hder.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I.map (phi β c))), Ideal.Quotient.eq] at hw
    obtain ⟨j2, f12, b0, hb0⟩ := rep_above hc j1 a₀
    obtain ⟨j3, f23, v, hv⟩ := rep_above hc j2 u
    set p3 := p.map (D.map (f12 ≫ f23)).hom with hp3
    set b3 := (D.map f23).hom b0 with hb3
    have hp3g : p3.map (c.ι.app j3).hom = g := by rw [hp3, pmap, hp]
    have hb3a : (c.ι.app j3).hom b3 = a₀ := by rw [hb3, iota_nat, hb0]
    have hy1 : (c.ι.app j3).hom (p3.eval b3) ∈ I.map (phi β c) := by
      rw [ev_map, hp3g, hb3a]; exact hev
    have hy2 : (c.ι.app j3).hom (p3.derivative.eval b3 * v - 1) ∈ I.map (phi β c) := by
      rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map, hp3g, hb3a, hv]; exact hw
    obtain ⟨j4, f34, h4⟩ := memK_descend β hc I _ hy1
    obtain ⟨j5, f45, h5⟩ := memK_descend β hc I ((D.map f34).hom (p3.derivative.eval b3 * v - 1))
      (by rw [iota_nat]; exact hy2)
    let h := f34 ≫ f45
    set P := p3.map (D.map h).hom with hP
    set b := (D.map h).hom b3 with hb
    have hPm : P.Monic := (hpm.map _).map _
    have hPe : P.eval b ∈ I.map (β.app j5).hom := by
      rw [hP, hb, ← ev_map]
      have := mapI β I f45 h4
      simpa [h] using this
    have hPd : IsUnit (Ideal.Quotient.mk (I.map (β.app j5).hom) (P.derivative.eval b)) := by
      have e : (D.map h).hom (p3.derivative.eval b3 * v - 1) = P.derivative.eval b * (D.map h).hom v - 1 := by
        rw [map_sub, map_mul, map_one, ev_map, ← Polynomial.derivative_map]
      have h5' : P.derivative.eval b * (D.map h).hom v - 1 ∈ I.map (β.app j5).hom := by
        rw [← e]; simpa [h] using h5
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ ((D.map h).hom v)) ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact h5'
    obtain ⟨j6, f56, a, ha1, ha2⟩ := hcc j5 P b hPm hPe hPd
    refine ⟨(c.ι.app j6).hom a, ?_, ?_⟩
    · have hr := ha1.map (f := (c.ι.app j6).hom)
      rwa [pmap, hP, pmap, hp3g] at hr
    · have := KofI β c I ha2
      rwa [map_sub, iota_nat, hb, iota_nat, hb3a] at this
  ·
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha0
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at ha0
    obtain ⟨j, x, hx, hxe⟩ := Krep β hc I ha0
    obtain ⟨j', f, hf⟩ := zero_later hc ((β.app j).hom b - x)
      (by rw [map_sub, hxe, phi_eq, sub_self])
    rw [map_sub, sub_eq_zero, beta_nat] at hf
    have hm : (β.app j').hom b ∈ I.map (β.app j').hom := by rw [hf]; exact mapI β I f hx
    apply (ha j').1
    rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  ·
    intro z
    obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨j, y, rfl⟩ := rep hc z'
    obtain ⟨w, hw⟩ := (ha j).2 (Ideal.Quotient.mk _ y)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨Ideal.Quotient.mk I b, ?_⟩
    rw [Ideal.quotientMap_mk] at hw ⊢
    rw [Ideal.Quotient.eq] at hw ⊢
    have := KofI β c I hw
    rwa [map_sub, phi_eq] at this

end LateralTheory.E.ColimHensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CompCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.CompCut

def LocAC : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ q : PrimeSpectrum W,
  IsField (Localization.AtPrime q.asIdeal) ∧ AIC (Localization.AtPrime q.asIdeal)

def NormAC : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (K : Type) [CommRing K], IsField K → AIC K → ∀ v : Spec (CommRingCat.of K) ⟶ P,
  AICSch v.normalization

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D)
      (ι : ∀ j, D.obj j ⟶ w.normalization), ClopenSys y D c ι ∧
      Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem goal_of (hS : Sys) (hL : LocAC) (hN : NormAC) : Comp := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, c, ι, hc, ⟨e⟩⟩ := hS W w hW y
  obtain ⟨hF, hA⟩ := hL W hW q
  refine ⟨J, inferInstance, inferInstance, D, c.extend e.inv, ι, ⟨⟨IsLimit.ofIsoLimit hc.1.some (Cone.extendIso c e)⟩,
    hc.2.1, hc.2.2⟩, ?_⟩
  exact hN _ hF hA _

end LateralTheory.E.CompCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagramChase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.StepSPf

def PO (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (c.π.app j0 ⁻¹ᵁ W).toScheme) n i, ∃ (k : J) (f : k ⟶ j0)
      (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
      pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
    pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map ((D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map (g ≫ f) ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp]))) _ _ y = 0

def Restr : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (W : X.Opens), IsCompact (W : Set X) → PC W.toScheme → PO q D c j0 (e.hom ⁻¹ᵁ W)

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (U V : X.Opens), U ⊔ V = ⊤ → PO q D c j0 (e.hom ⁻¹ᵁ U) → PO q D c j0 (e.hom ⁻¹ᵁ V) → PO q D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

theorem S_of_restr_chase (hR : Restr) (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated e.inv
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV
  exact hC h hmv q D c hc ha hcs hqs hu j0 X e U V hUV (hR q D c hc ha hcs hqs hu j0 X e U hU pU)
    (hR q D c hc ha hcs hqs hu j0 X e V hV pV) (hR q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW pW) n i

theorem po_res_zero {q : ℕ} {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (A : Z.Opens) (B B' : Y.Opens) (hB : B = B')
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A) (n i : ℤ) (y : Ht q (sch.obj A.toScheme) n i) :
    pull _ (sch.map (φ.resLE A B h)) _ _ y = 0 → pull _ (sch.map (φ.resLE A B' h')) (tw q i) n y = 0 := by
  subst hB; exact id

theorem restr : Restr := by
  intro q J _ _ D c hc ha hcs hqs hu j0 X e W hWc pW
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f) := ha
  set W' : (D.obj j0).Opens := e.hom ⁻¹ᵁ W with hW'def
  have hW' : IsCompact (W' : Set (D.obj j0)) := QuasiCompact.isCompact_preimage (f := e.hom) _ W.2 hWc
  have key := pW q (opensDiagram D j0 W') (opensCone D c j0 W') (isLimitOpensCone D c hc j0 W')
    (fun f => inferInstance)
    (fun j => isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ W'.2 hW'))
    (fun j => by have := hqs j.left; exact (D.map j.hom ⁻¹ᵁ W').ι.isOpenEmbedding.quasiSeparatedSpace)
    (fun j => by
      have h := (hu j.left).map ((D.map j.hom ⁻¹ᵁ W').ι.appTop.hom)
      simp only [map_natCast] at h
      exact h)
    (Over.mk (𝟙 j0)) ⟨(Scheme.isoOfEq _ (by simp [hW'def])) ≪≫ e.hom.preimageIso W⟩
  intro n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := (key n i).1 x
    exact ⟨j.left, j.hom, y, hy⟩
  · obtain ⟨k', g, hg⟩ := (key n i).2 (Over.mk f) y hy
    have hw : g.left ≫ f = k'.hom := Over.w g
    refine ⟨k'.left, g.left, ?_⟩
    exact po_res_zero (D.map g.left) _ _ _ (by rw [hw]) _ _ n i y hg

end LateralTheory.E.StepSPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GlueRelPfCone
section
noncomputable section
open CategoryTheory Limits GlobalTheory.EtC CochainComplex.HomComplex CochainComplex

namespace LateralTheory.E.GlueRelPfCone

theorem pre_pull_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (b : HK R L F m) :
    HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) (HK.pull R φ F m b) = 0 := by
  obtain ⟨b, rfl⟩ := b.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) (zcomp (Cocycle.ofHom φ) b (zero_add m)) (add_comm 1 m)) = 0
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, rfl, -(m.negOnePow • (mappingCone.snd φ).comp b.1 (zero_add m)), ?_⟩
  ext1
  simp only [zcomp, Cocycle.ofHom_coe]
  rw [δ_neg, δ_units_smul, δ_comp _ _ (zero_add m) 1 (m + 1) (m + 1) rfl (zero_add 1) rfl, mappingCone.δ_snd]
  simp [Cocycle.δ_eq_zero, Cochain.comp_assoc_of_second_is_zero_cochain, smul_smul, Int.units_mul_self]

theorem range_of_pre_zero (R : Type) [CommRing R] {K L : Cx R} (φ : K ⟶ L) (F : Shv R) (m : ℤ) (x : HK R K F m)
    (hx : HK.pre R (mappingCone.fst φ) F m (m + 1) (add_comm 1 m) x = 0) : x ∈ Set.range (HK.pull R φ F m) := by
  obtain ⟨a, rfl⟩ := x.mk_surjective
  change CohomologyClass.mk (zcomp (mappingCone.fst φ) a (add_comm 1 m)) = 0 at hx
  rw [CohomologyClass.mk_eq_zero_iff] at hx
  obtain ⟨m', hm', γ, hγ⟩ := hx
  obtain rfl : m' = m := by omega
  have hγ' : δ m' (m' + 1) γ = (mappingCone.fst φ).1.comp a.1 (add_comm 1 m') := by
    rw [hγ]; rfl
  have hb : δ m' (m' + 1) ((Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')) = 0 := by
    rw [δ_comp _ _ (zero_add m') 1 (m' + 1) (m' + 1) rfl (zero_add 1) rfl, hγ', δ_ofHom]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.inr_fst]
    simp
  let b : Cocycle L (res R F) m' := Cocycle.mk (-(m'.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp γ (zero_add m')))
    (m' + 1) rfl (by rw [δ_neg, δ_units_smul, hb]; simp)
  refine ⟨CohomologyClass.mk b, ?_⟩
  change CohomologyClass.mk (zcomp (Cocycle.ofHom φ) b (zero_add m')) = CohomologyClass.mk a
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  refine ⟨m' - 1, by omega, -((mappingCone.inl φ).comp γ (by omega)), ?_⟩
  ext1
  rw [δ_neg, δ_comp _ _ (show -1 + m' = m' - 1 by omega) 0 (m' + 1) m' (by omega) (by omega) rfl, hγ',
    mappingCone.δ_inl]
  rw [← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_comm 1 m') (by omega), mappingCone.inl_fst]
  simp [zcomp, b, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain, sub_eq_add_neg]

theorem coneExact : LateralTheory.E.GlueRelPf.ConeExact := by
  intro R _ K L φ F m x
  exact ⟨range_of_pre_zero R φ F m x, by rintro ⟨b, rfl⟩; exact pre_pull_zero R φ F m b⟩

end LateralTheory.E.GlueRelPfCone
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.HalfDegreeVanishing

theorem um_hom_val {N : ℕ} {A : Type} [CommRing A] {v w v' w' : Um N A} (hv : v = v') (hw : w = w') (p : v' ⟶ w') :
    (eqToHom hv ≫ p ≫ eqToHom hw.symm).1 = p.1 := by
  subst hv hw; simp

theorem um_functor_ext {N n : ℕ} {A : Type} [CommRing A] (F G : Fin (n + 1) ⥤ Um N A)
    (ho : ∀ i, (F.obj i).1 = (G.obj i).1) (hm : ∀ {i j : Fin (n + 1)} (f : i ⟶ j), (F.map f).1 = (G.map f).1) : F = G := by
  refine CategoryTheory.Functor.ext (fun i => Subtype.ext (ho i)) (fun i j f => ?_)
  apply Subtype.ext
  exact (hm f).trans (um_hom_val (Subtype.ext (ho i)) (Subtype.ext (ho j)) (G.map f)).symm

variable {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b))

theorem arrow_eq {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W (pe V W x)).map f).val.mulVec (wb (a := a) ((pv V W x).obj i).1) =
      (((pv V W x).map f).1.2 : Scheme.Γ.obj (op X)) • wb (a := a) ((pv V W x).obj j).1 := by
  have e := ((pv V W x).map f).2
  rw [cond] at e
  have e2 := congrArg (wb (a := a)) e
  rw [wb_mulVec] at e2
  exact e2

def gfun {n : ℕ} {X : Scheme.{0}} (x : Sx (PB (bsumOf V W)) n X) (hx : AllSec V W x) :
    Fin (n + 1) ⥤ Um b (Scheme.Γ.obj (op X)) where
  obj i := ⟨wb (a := a) ((pv V W x).obj i).1, hx i⟩
  map {i j} f := ⟨((pw W (pe V W x)).map f, ((pv V W x).map f).1.2), arrow_eq V W x f⟩
  map_id i := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_id i) (congrArg (fun p => p.1.2) ((pv V W x).map_id i)))
  map_comp f g := Subtype.ext (Prod.ext ((pw W (pe V W x)).map_comp f g) (congrArg (fun p => p.1.2) ((pv V W x).map_comp f g)))

theorem pe_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) :
    pe V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) = (E.obj (op (SimplexCategory.mk n))).map k.op (pe V W x) :=
  NatTrans.naturality_apply
    ((pullback.fst (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))) k.op x

theorem pw_res {n : ℕ} {X Y : Scheme.{0}} (k : Y ⟶ X) (e : Sx E n X) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (show GL (Fin b) (Scheme.Γ.obj (op Y)) from (pw W ((E.obj (op (SimplexCategory.mk n))).map k.op e)).map f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map k.op).hom (show GL (Fin b) (Scheme.Γ.obj (op X)) from (pw W e).map f) :=
  eq_of_heq (Functor.hcongr_hom (NatTrans.naturality_apply (W.app (op (SimplexCategory.mk n))) k.op e) f)

end LateralTheory.E.HalfDegreeVanishing
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.IdemPartPf
section
namespace LateralTheory.E.IdemPartPf

open Finset

theorem prod_erase_mul_prod_erase {A : Type} [CommRing A] {n : ℕ} (y : Fin n → A)
    (h0 : ∏ l, y l = 0) {l m : Fin n} (hlm : l ≠ m) :
    (∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k) = 0 := by
  have hl : l ∈ (univ : Finset (Fin n)).erase m := mem_erase.2 ⟨hlm, mem_univ l⟩
  rw [← mul_prod_erase _ y hl, ← mul_assoc, mul_comm (∏ k ∈ univ.erase l, y k) (y l),
    mul_prod_erase _ y (mem_univ l), h0, zero_mul]

theorem IdemPart_of : LateralTheory.E.HensCut.IdemPart := by
  intro A _ n y h0 hu
  obtain ⟨u, hu⟩ := hu
  let e : Fin n → A := fun l => (↑u⁻¹ : A) * ∏ m ∈ univ.erase l, y m
  have horth : ∀ l m, l ≠ m → e l * e m = 0 := by
    intro l m hlm
    have := prod_erase_mul_prod_erase y h0 hlm
    calc e l * e m = (↑u⁻¹ : A) * ↑u⁻¹ * ((∏ k ∈ univ.erase l, y k) * (∏ k ∈ univ.erase m, y k)) := by
          simp only [e]; ring
      _ = 0 := by rw [this, mul_zero]
  have hsum : ∑ l, e l = 1 := by
    simp only [e]
    rw [← mul_sum, ← hu, Units.inv_mul]
  refine ⟨e, ?_, horth, hsum, ?_⟩
  · intro l
    unfold IsIdempotentElem
    calc e l * e l = e l * ∑ m, e m := by
          rw [mul_sum, sum_eq_single l]
          · intro m _ hml; exact horth l m (Ne.symm hml)
          · intro h; exact absurd (mem_univ l) h
      _ = e l := by rw [hsum, mul_one]
  · intro l
    simp only [e]
    rw [mul_assoc, mul_comm (∏ m ∈ univ.erase l, y m) (y l), mul_prod_erase _ y (mem_univ l), h0, mul_zero]

end LateralTheory.E.IdemPartPf
end

