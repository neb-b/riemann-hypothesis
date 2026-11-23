module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
public import Development.EtaleCohomology.EtaleSheaves.Bundle0006
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyContinuityFilteredColimitRings
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace UpperTheory.DirectSumIndependence

private abbrev P (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    Ht q (sch.obj (Spec A)) n i →+ Ht q (sch.obj (Spec B)) n i :=
  pull _ (sch.map (Spec.map f)) (tw q i) n

private theorem pullback_comp₂ (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C)
    (x : Ht q (sch.obj (Spec A)) n i) : P q i n (f ≫ g) x = P q i n g (P q i n f x) := by
  show pull _ (sch.map (Spec.map (f ≫ g))) (tw q i) n x = _
  rw [Spec.map_comp, Functor.map_comp, pull_comp]

private theorem isUnit_of_hom {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) :
    IsUnit (q : B) := by
  simpa using h.map f.hom

private theorem chase (b1 : B1) (q : ℕ) (i : ℤ) {J : Type} [SmallCategory J] [IsFiltered J]
    (D D' : J ⥤ CommRingCat.{0}) (α : D ⟶ D') (c : Cocone D) (hc : IsColimit c)
    (c' : Cocone D') (hc' : IsColimit c') (g : c.pt ⟶ c'.pt)
    (hg : ∀ j, c.ι.app j ≫ g = α.app j ≫ c'.ι.app j)
    (hα : ∀ j, RE q i (α.app j)) (hq : ∀ j, IsUnit (q : D.obj j)) : RE q i g := by
  intro n
  change Function.Bijective (P q i n g)
  have hqc : IsUnit (q : c.pt) := by
    obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
    exact isUnit_of_hom (c.ι.app j) (hq j)
  have hqc' : IsUnit (q : c'.pt) := isUnit_of_hom g hqc
  have hqD' : ∀ j, IsUnit (q : D'.obj j) := fun j => isUnit_of_hom (α.app j) (hq j)
  have comm : ∀ j y, P q i n g (P q i n (c.ι.app j) y) =
      P q i n (c'.ι.app j) (P q i n (α.app j) y) := by
    intro j y
    rw [← pullback_comp₂, ← pullback_comp₂, hg]
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨j, y, hy⟩ := (b1 q D c hc n i).1 x hqc
    change P q i n (c.ι.app j) y = x at hy
    subst hy
    rw [comm] at hx
    obtain ⟨k, f, hf⟩ := (b1 q D' c' hc' n i).2 j (P q i n (α.app j) y) (hqD' j) hx
    change P q i n (D'.map f) (P q i n (α.app j) y) = 0 at hf
    rw [← pullback_comp₂, ← α.naturality f, pullback_comp₂] at hf
    have h0 : P q i n (D.map f) y = 0 := by
      apply (hα k n).1
      show P q i n (α.app k) (P q i n (D.map f) y) = P q i n (α.app k) 0
      rw [hf, map_zero]
    rw [← c.w f, pullback_comp₂, h0, map_zero]
  · intro z
    obtain ⟨j, y', hy'⟩ := (b1 q D' c' hc' n i).1 z hqc'
    change P q i n (c'.ι.app j) y' = z at hy'
    obtain ⟨y, rfl⟩ := (hα j n).2 y'
    refine ⟨P q i n (c.ι.app j) y, ?_⟩
    rw [← hy']
    exact comm j y

variable {J : Type} [SmallCategory J] {A Y : CommRingCat.{0}} (φ : A ⟶ Y) (D : J ⥤ CommRingCat.{0})
  (t : ∀ j, A ⟶ D.obj j) (ht : ∀ {j k : J} (f : j ⟶ k), t j ≫ D.map f = t k)

private def Dp : J ⥤ CommRingCat.{0} where
  obj j := pushout φ (t j)
  map {j k} f := pushout.desc (pushout.inl φ (t k)) (D.map f ≫ pushout.inr φ (t k)) (by
    rw [← Category.assoc, ht f, pushout.condition])
  map_id j := by
    apply pushout.hom_ext <;> simp
  map_comp {j k l} f g := by
    apply pushout.hom_ext
    · erw [pushout.inl_desc, ← Category.assoc, pushout.inl_desc, pushout.inl_desc]
    · erw [pushout.inr_desc, ← Category.assoc, pushout.inr_desc, Category.assoc, pushout.inr_desc,
        D.map_comp, Category.assoc]

private theorem inl_Dp {j k : J} (f : j ⟶ k) :
    pushout.inl φ (t j) ≫ (Dp φ D t ht).map f = pushout.inl φ (t k) :=
  pushout.inl_desc _ _ _

private theorem inr_Dp {j k : J} (f : j ⟶ k) :
    pushout.inr φ (t j) ≫ (Dp φ D t ht).map f = D.map f ≫ pushout.inr φ (t k) :=
  pushout.inr_desc _ _ _

private def toDp : D ⟶ Dp φ D t ht where
  app j := pushout.inr φ (t j)
  naturality j k f := (inr_Dp φ D t ht f).symm

variable (c : Cocone D) (hc : IsColimit c) {Y' : CommRingCat.{0}} (w : Y ⟶ Y') (φ' : c.pt ⟶ Y')
  (cc : A ⟶ c.pt) (hcc : ∀ j, t j ≫ c.ι.app j = cc) (hp : IsPushout φ cc w φ')

private def cocDp : Cocone (Dp φ D t ht) where
  pt := Y'
  ι :=
    { app j := pushout.desc w (c.ι.app j ≫ φ') (by
        rw [← Category.assoc, hcc, hp.w])
      naturality j k f := by
        refine pushout.hom_ext ?_ ?_
        · erw [← Category.assoc, inl_Dp, pushout.inl_desc, ← Category.assoc, pushout.inl_desc,
            Category.comp_id]
        · erw [← Category.assoc, inr_Dp, Category.assoc, pushout.inr_desc, ← Category.assoc, c.w f,
            ← Category.assoc, pushout.inr_desc, Category.comp_id] }

private theorem inl_coc (j : J) :
    pushout.inl φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = w :=
  pushout.inl_desc _ _ _

private theorem inr_coc (j : J) :
    pushout.inr φ (t j) ≫ (cocDp φ D t ht c w φ' cc hcc hp).ι.app j = c.ι.app j ≫ φ' :=
  pushout.inr_desc _ _ _

private theorem inl_indep [IsFiltered J] (e : Cocone (Dp φ D t ht)) (j k : J) :
    pushout.inl φ (t j) ≫ e.ι.app j = pushout.inl φ (t k) ≫ e.ι.app k := by
  rw [← e.w (IsFiltered.leftToMax j k), ← e.w (IsFiltered.rightToMax j k)]
  erw [← Category.assoc, inl_Dp, ← Category.assoc, inl_Dp]

private def resCoc (e : Cocone (Dp φ D t ht)) : Cocone D where
  pt := e.pt
  ι :=
    { app j := pushout.inr φ (t j) ≫ e.ι.app j
      naturality j k f := by
        erw [Category.comp_id, ← e.w f, ← Category.assoc, ← Category.assoc, inr_Dp]
        simp
        rfl }

private def isColDp [IsFiltered J] : IsColimit (cocDp φ D t ht c w φ' cc hcc hp) :=
  let j0 : J := (IsFiltered.nonempty (C := J)).some
  { desc := fun e => hp.desc (pushout.inl φ (t j0) ≫ e.ι.app j0)
      (hc.desc (resCoc φ D t ht e)) (by
        erw [← hcc j0, Category.assoc, hc.fac, ← Category.assoc, pushout.condition, Category.assoc])
    fac := fun e j => by
      refine pushout.hom_ext ?_ ?_
      · erw [← Category.assoc, inl_coc, hp.inl_desc]
        exact inl_indep φ D t ht e j0 j
      · erw [← Category.assoc, inr_coc, Category.assoc, hp.inr_desc, hc.fac]
        rfl
    uniq := fun e m hm => by
      refine hp.hom_ext ?_ ?_
      · erw [hp.inl_desc, ← hm j0, ← Category.assoc, inl_coc]
        rfl
      · erw [hp.inr_desc]
        refine hc.hom_ext fun j => ?_
        erw [hc.fac, ← Category.assoc, ← inr_coc φ D t ht c w φ' cc hcc hp j, Category.assoc, hm j]
        rfl }

end UpperTheory.DirectSumIndependence

theorem UpperTheory.cohomology_continuity_filtered_colimit_rings :
    LateralTheory.E.t_E3Cut.Limit := by
  intro hyp q _ i A Y φ hq hEt C c hc Y' w φ' hp
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hc
  have ht : ∀ {j k : J} (f : j ⟶ k), t.app j ≫ D.map f = t.app k := by
    intro j k f
    rw [← t.naturality f]
    simp
  exact UpperTheory.DirectSumIndependence.chase hyp.2.2.2.2.2.2.1 q i D
    (UpperTheory.DirectSumIndependence.Dp φ D (fun j => t.app j) ht)
    (UpperTheory.DirectSumIndependence.toDp φ D (fun j => t.app j) ht) (Cocone.mk C s) hs
    (UpperTheory.DirectSumIndependence.cocDp φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp)
    (UpperTheory.DirectSumIndependence.isColDp φ D (fun j => t.app j) ht (Cocone.mk C s) hs w φ' c
      (fun j => (hts j).2) hp)
    φ'
    (fun j => (UpperTheory.DirectSumIndependence.inr_coc φ D (fun j => t.app j) ht (Cocone.mk C s) w φ' c
      (fun j => (hts j).2) hp j).symm)
    (fun j => hEt _ _ (hts j).1 _ _ _ (IsPushout.of_hasPushout _ _))
    (fun j => UpperTheory.DirectSumIndependence.isUnit_of_hom (t.app j) hq)
end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedOfUnimodularSub
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

namespace UpperTheory

variable (D : Type) [CommRing D] (d : ℕ)

private abbrev Sm (X : RF) (p : ℕ) (T : Scheme.{0}) : Type :=
  {x : Fin (p + 1) → X.obj Γ(T, ⊤) // ∀ i j, X.rel (x i) (x j)}

private theorem cond2 (p : ℕ) (T : Scheme.{0}) (a b : Sx (CN (L1 D d)) p T)
    (h : sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a =
      sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) b) :
    EtLoc T fun V k => sxRes k a = sxRes k b ∨ ∃ u : Sx (CN (L2 D d)) p V,
      sxMap (CN.map ((Vec D (d + 1)).subι P2 second_property_map) ((Vec D (d + 1)).subι_rel P2 second_property_map)) u =
        sxRes k (sxMap (CN.map ((Vec D (d + 1)).subι P1 first_property_map) ((Vec D (d + 1)).subι_rel P1 first_property_map)) a) := by
  have hab : a = b := by
    let a' : Sm (L1 D d) p T := a
    let b' : Sm (L1 D d) p T := b
    have h' : ∀ i, (a'.1 i).1 = (b'.1 i).1 := fun i => congrFun (congrArg Subtype.val h) i
    exact Subtype.ext (funext fun i => Subtype.ext (h' i))
  exact ⟨⊤, Scheme.etaleTopology.top_mem T, fun V k _ => Or.inl (by rw [hab])⟩

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := by
  intro n
  refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.DedekindSpecOpenIsAffine
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private lemma exists_local_generator {B : Type} [CommRing B] [IsDedekindDomain B]
    (I : Ideal B) (p : Ideal B) [hp : p.IsPrime] :
    ∃ π ∈ I, ∃ s, s ∉ p ∧ ∀ x ∈ I, s * x ∈ Ideal.span {π} :=
  _root_.UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator I p

theorem UpperTheory.dedekind_spec_open_isAffine :
    ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (W : (Spec (CommRingCat.of B)).Opens), IsAffineOpen W := by
  intro B _ _ W
  let S : Set (PrimeSpectrum B) := ((W : Set (Spec (CommRingCat.of B)))ᶜ : Set (Spec (CommRingCat.of B)))
  have hS : IsClosed S := W.isOpen.isClosed_compl
  let I : Ideal B := PrimeSpectrum.vanishingIdeal S
  have hWc : PrimeSpectrum.zeroLocus (I : Set B) = S := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hS.closure_eq
  let D : B → (Spec (CommRingCat.of B)).Opens := fun r =>
    PrimeSpectrum.basicOpen (R := CommRingCat.of B) r
  have hbasic : ∀ r : B, IsAffineOpen (D r) := by
    intro r
    have h := (isAffineOpen_top (Spec (CommRingCat.of B))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv r)
    rwa [basicOpen_eq_of_affine] at h
  have hmain : IsAffineHom W.ι := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun x => ?_
    obtain ⟨π, hπ, s, hs, hsI⟩ := @exists_local_generator B _ _ I x.asIdeal x.isPrime
    refine ⟨D s, hs, hbasic s, ?_⟩
    have hEq : W ⊓ D s = D (s * π) := by
      ext q
      have hq : q ∈ W ↔ ¬ (I : Set B) ⊆ q.asIdeal := by
        have h1 : (I : Set B) ⊆ q.asIdeal ↔ q ∉ W := Set.ext_iff.1 hWc q
        rw [h1, not_not]
      have hDm : ∀ r : B, q ∈ D r ↔ r ∉ q.asIdeal := fun r => Iff.rfl
      change q ∈ W ∧ q ∈ D s ↔ q ∈ D (s * π)
      rw [hDm, hDm, hq]
      have hqp : q.asIdeal.IsPrime := q.isPrime
      constructor
      · rintro ⟨hIq, hsq⟩ hm
        rcases hqp.mem_or_mem hm with h | h
        · exact hsq h
        · refine hIq fun y hy => ?_
          have h2 : s * y ∈ q.asIdeal :=
            (Ideal.span_singleton_le_iff_mem q.asIdeal).2 h (hsI y hy)
          exact (hqp.mem_or_mem h2).resolve_left hsq
      · intro hm
        refine ⟨fun hsub => hm (Ideal.mul_mem_left _ _ (hsub hπ)),
          fun h => hm (Ideal.mul_mem_right _ _ h)⟩
    have h := hbasic (s * π)
    rw [← hEq] at h
    have h2 := h.preimage_of_isOpenImmersion W.ι (by simp)
    have e : W.ι ⁻¹ᵁ (W ⊓ D s) = W.ι ⁻¹ᵁ D s := by
      ext y
      exact ⟨fun hy => hy.2, fun hy => ⟨y.2, hy⟩⟩
    rwa [e] at h2
  have : IsAffine W.toScheme := isAffine_of_isAffineHom W.ι
  exact this
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsOrthogonalIdempotentsIsDomainOfEtale
section
noncomputable section

open TensorProduct Polynomial

private theorem isIntegrallyClosed_of_AIC (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.EtC.AIC T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  induction h : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ d ih =>
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      have h1 : p = 1 := hp.natDegree_eq_zero.1 h
      simp [h1] at hpx
    · obtain ⟨a, ha⟩ := hT p hp (h ▸ hpos)
      obtain ⟨q, hq⟩ := dvd_iff_isRoot.2 ha
      have hqm : q.Monic := (monic_X_sub_C a).of_mul_monic_left (hq ▸ hp)
      have hdeg : p.natDegree = 1 + q.natDegree := by
        rw [hq, (monic_X_sub_C a).natDegree_mul hqm, natDegree_X_sub_C]
      rw [hq, eval₂_mul] at hpx
      rcases mul_eq_zero.1 hpx with h1 | h1
      · refine ⟨a, ?_⟩
        simp only [eval₂_sub, eval₂_X, eval₂_C] at h1
        exact (sub_eq_zero.1 h1).symm
      · exact ih q.natDegree (by omega) q hqm h1 rfl

private theorem exists_of_idem (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] (z : C ⊗[T] FractionRing T) (hz : z * z = z) :
    ∃ s : C, algebraMap C (C ⊗[T] FractionRing T) s = z := by
  have hint : IsIntegral C z := by
    refine ⟨X ^ 2 - X, monic_X_pow_sub (n := 2) (lt_of_le_of_lt degree_X_le (by norm_num)), ?_⟩
    simp [eval₂_sub, pow_two, hz]
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := T) (S := C)
    (B := FractionRing T)).2 ⟨z, hint⟩
  have ht' : Algebra.TensorProduct.map (AlgHom.id C C)
      (integralClosure T (FractionRing T)).val t = z := congrArg Subtype.val ht
  rw [← ht']
  clear ht ht'
  induction t with
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul x y =>
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := T) y.2
    refine ⟨r • x, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← hr,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Algebra.algebraMap_eq_smul_one, smul_tmul]

private theorem core (T C : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T]
    [CommRing C] [Algebra T C] [Algebra.Etale T C] {n : ℕ}
    (g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T)) :
    ∃ (e : Fin n → C), CompleteOrthogonalIdempotents e ∧
      ∀ j, IsDomain (Localization.Away (e j)) := by
  classical
  let G : C →+* (Fin n → FractionRing T) :=
    g.toRingHom.comp (algebraMap C (C ⊗[T] FractionRing T))
  have hι : Function.Injective (algebraMap C (C ⊗[T] FractionRing T)) :=
    Algebra.TensorProduct.includeLeft_injective (S := T)
      (IsFractionRing.injective T (FractionRing T))
  have hG : Function.Injective G := g.injective.comp hι
  have hex : ∀ j : Fin n, ∃ s : C, G s = Pi.single j 1 := by
    intro j
    obtain ⟨s, hs⟩ := exists_of_idem T C (g.symm (Pi.single j 1)) (by
      apply g.injective
      rw [map_mul, g.apply_symm_apply, ← Pi.single_mul, one_mul])
    exact ⟨s, by simp [G, hs]⟩
  choose c hc using hex
  have hcoi : CompleteOrthogonalIdempotents c := by
    refine ⟨⟨fun i => hG ?_, fun i j hij => hG ?_⟩, hG ?_⟩
    · rw [map_mul, hc, ← Pi.single_mul, one_mul]
    · rw [map_mul, hc, hc, map_zero]
      ext k
      by_cases h : k = i
      · subst h; simp [Pi.single_eq_of_ne hij]
      · simp [Pi.single_eq_of_ne h]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, map_one]
        simp only [hc]
        exact Finset.univ_sum_single 1
  refine ⟨c, hcoi, fun j => ?_⟩
  have hidem : IsIdempotentElem (c j) := hcoi.idem j
  let φ : C →+* FractionRing T := (Pi.evalRingHom _ j).comp G
  have hφ : φ (c j) = 1 := by simp [φ, hc]
  have hu : IsUnit (φ (c j)) := by rw [hφ]; exact isUnit_one
  let ψ : Localization.Away (c j) →+* FractionRing T := IsLocalization.Away.lift (c j) hu
  have hψ : ∀ x, ψ (algebraMap C _ x) = φ x := fun x => IsLocalization.Away.lift_eq (c j) hu x
  have hsurj : Function.Surjective (algebraMap C (Localization.Away (c j))) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (c j) hidem
  have hone : algebraMap C (Localization.Away (c j)) (c j) = 1 :=
    (IsIdempotentElem.iff_eq_one_of_isUnit (IsLocalization.Away.algebraMap_isUnit (c j))).1
      (hidem.map _)
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨x, rfl⟩ := hsurj a
    rw [hψ] at ha
    have hx : x * c j = 0 := by
      apply hG
      rw [map_mul, hc, map_zero]
      ext k
      by_cases h : k = j
      · subst h
        simpa [φ] using ha
      · simp [Pi.single_eq_of_ne h]
    have := congrArg (algebraMap C (Localization.Away (c j))) hx
    rwa [map_mul, hone, mul_one, map_zero] at this
  exact hinj.isDomain ψ

theorem UpperTheory.exists_orthogonalIdempotents_isDomain_of_etale :
    ∀ (T C : Type) [CommRing T] [IsDomain T] [CommRing C] [Algebra T C] [Algebra.Etale T C], GlobalTheory.EtC.AIC T →
      ∃ (n : ℕ) (e : Fin n → C), CompleteOrthogonalIdempotents e ∧ ∀ j, IsDomain (Localization.Away (e j)) := by
  intro T C _ _ _ _ _ hT
  haveI := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hT
  haveI := isIntegrallyClosed_of_AIC T hT
  let e0 := Algebra.FormallyEtale.equivPiOfIsSepClosed (FractionRing T) (FractionRing T ⊗[T] C)
  haveI := Algebra.FormallyUnramified.finite_of_free (FractionRing T) (FractionRing T ⊗[T] C)
  haveI : IsArtinianRing (FractionRing T ⊗[T] C) := isArtinian_of_tower (FractionRing T) inferInstance
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (PrimeSpectrum (FractionRing T ⊗[T] C))
  let g : C ⊗[T] FractionRing T ≃+* (Fin n → FractionRing T) :=
    ((Algebra.TensorProduct.comm T C (FractionRing T)).toRingEquiv.trans e0.toRingEquiv).trans
      (RingEquiv.piCongrLeft (fun _ : Fin n => FractionRing T) eq)
  obtain ⟨e, h1, h2⟩ := core T C g
  exact ⟨n, e, h1, h2⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSpecializesLiftGenericBaseChange
section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

private lemma aux {W S T U : Scheme.{0}} (w : W ⟶ S) (i : T ⟶ S) (j : U ⟶ T) (g : U ⟶ S)
    (hg : j ≫ i = g) [Flat j] [IsPreimmersion i] (y' : ↑(pullback w g)) (x : W)
    (hx : x ⤳ (pullback.fst w g) y') (hxr : x ∈ Set.range (pullback.fst w i)) :
    ∃ x' : ↑(pullback w g), x' ⤳ y' ∧ (pullback.fst w g) x' = x := by
  subst hg
  have hfst : ∀ p, (pullback.fst w (j ≫ i)) ((pullbackLeftPullbackSndIso w i j).hom p) =
      (pullback.fst w i) ((pullback.fst (pullback.snd w i) j) p) := by
    intro p
    show ((pullbackLeftPullbackSndIso w i j).hom ≫ pullback.fst w (j ≫ i)).base p =
      (pullback.fst (pullback.snd w i) j ≫ pullback.fst w i).base p
    rw [pullbackLeftPullbackSndIso_hom_fst]
  have hy : (pullbackLeftPullbackSndIso w i j).hom ((pullbackLeftPullbackSndIso w i j).inv y') = y' := by
    show ((pullbackLeftPullbackSndIso w i j).inv ≫ (pullbackLeftPullbackSndIso w i j).hom).base y' = y'
    rw [Iso.inv_hom_id]
    rfl
  obtain ⟨z, hz⟩ := hxr
  have hxz : z ⤳ (pullback.fst (pullback.snd w i) j) ((pullbackLeftPullbackSndIso w i j).inv y') := by
    rw [← (IsPreimmersion.isEmbedding (pullback.fst w i)).isInducing.specializes_iff, hz, ← hfst, hy]
    exact hx
  obtain ⟨x'', hx'', hx''z⟩ := Flat.generalizingMap (pullback.fst (pullback.snd w i) j) hxz
  refine ⟨(pullbackLeftPullbackSndIso w i j).hom x'', ?_, ?_⟩
  · rw [← hy]
    exact hx''.map (Scheme.Hom.continuous _)
  · rw [hfst, hx''z, hz]

private lemma spec_bot {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) :
    Spec.map (CommRingCat.ofHom f) (⊥ : PrimeSpectrum B) = (⊥ : PrimeSpectrum A) := by
  apply PrimeSpectrum.ext
  exact Ideal.comap_bot_of_injective f hf

private lemma spec_field {F : Type} [Field F] (z : PrimeSpectrum F) : z = ⊥ :=
  PrimeSpectrum.ext (Ideal.eq_bot_of_prime _)

private lemma spec_gen {A : Type} [CommRing A] [IsDomain A] (a : PrimeSpectrum A)
    (h : a ⤳ (⊥ : PrimeSpectrum A)) : a = ⊥ :=
  le_bot_iff.1 ((PrimeSpectrum.le_iff_specializes _ _).2 h)

theorem UpperTheory.exists_specializes_lift_generic_base_change :
    ∀ (R Ω : Type) [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω], Function.Injective (algebraMap R Ω) → ∀ {W : Scheme.{0}} (w : W ⟶ Sp R) (y' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))) (x : W), x ⤳ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) y' → ∃ x' : ↑(pullback w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))), x' ⤳ y' ∧ (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) x' = x := by
  intro R Ω _ _ _ _ hinj W w y' x hx
  have hRK : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  letI : Algebra (FractionRing R) Ω := (IsFractionRing.lift hinj : FractionRing R →+* Ω).toAlgebra
  haveI : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have hcomp : (algebraMap (FractionRing R) Ω).comp (algebraMap R (FractionRing R)) =
      algebraMap R Ω := IsLocalization.lift_comp _
  have hg : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  apply aux w (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))
    (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) Ω))) _ hg y' x hx
  have hwx : (show PrimeSpectrum R from w x) = ⊥ := by
    apply spec_gen
    have h1 := hx.map w.continuous
    have h2 : w (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') =
        Spec.map (CommRingCat.ofHom (algebraMap R Ω))
          (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y') := by
      show (pullback.fst w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ w).base y' =
        (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R Ω))).base y'
      rw [pullback.condition]
    rw [h2, spec_field (pullback.snd w (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) y'),
      spec_bot _ hinj] at h1
    exact h1
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := w)
    (g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) x
    (⊥ : PrimeSpectrum (FractionRing R)) (by
      show (show PrimeSpectrum R from w x) = _
      rw [hwx, spec_bot _ hRK])
  exact ⟨z, hz⟩
end

