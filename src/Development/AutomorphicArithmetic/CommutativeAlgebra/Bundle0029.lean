module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0026
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CompLeft
public import Development.EtaleCohomology.KummerTheory.Bundle0001
public import Development.EtaleCohomology.WeilConjectures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0350

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMayerVietorisPreimageOfRestrictionsVanish
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.SchemePresentationCover

private theorem sch_pres : PreservesLimitsOfShape WalkingCospan sch := by
  unfold sch; infer_instance

private theorem pb {Y : Scheme.{0}} {A B C D : Y.Opens} (hC : C = A ⊓ B) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    IsPullback (Y.homOfLE hCA) (Y.homOfLE hCB) (Y.homOfLE hA) (Y.homOfLE hB) := by
  subst hC
  exact isPullback_opens_inf_le hA hB

private theorem cov (R : Type) [CommRing R] {Y : Scheme.{0}} {A B D : Y.Opens} (hD : D = A ⊔ B)
    (hA : A ≤ D) (hB : B ≤ D) :
    Cover2 R (sch.map (Y.homOfLE hA)) (sch.map (Y.homOfLE hB)) := by
  subst hD
  apply UpperTheory.isCovering_pair_of_isOpenImmersion_of_jointly_surjective
  · infer_instance
  · infer_instance
  · intro y
    have hy : (y.1 : Y) ∈ A ⊔ B := y.2
    rcases (by simpa using hy : (y.1 : Y) ∈ A ∨ (y.1 : Y) ∈ B) with h | h
    · exact Or.inl ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩
    · exact Or.inr ⟨⟨y.1, h⟩, by rw [Scheme.homOfLE_apply']; rfl⟩

end UpperTheory.SchemePresentationCover

private theorem sq_lemma' {T S : Scheme.{0}} (f : T ⟶ S) {P Q : S.Opens} (h : P ≤ Q) (h' : f ⁻¹ᵁ P ≤ f ⁻¹ᵁ Q) :
    T.homOfLE h' ≫ f ∣_ Q = f ∣_ P ≫ S.homOfLE h := by
  rw [← cancel_mono Q.ι]
  simp [morphismRestrict_ι]

open UpperTheory.SchemePresentationCover in
theorem UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish :
    ∀ (R : Type) [CommRing R] (F : Shv R) {S : Scheme.{0}} (U V : S.Opens) (n : ℤ)
        (x : H R (sch.obj (U ⊔ V).toScheme) F (n + 1)),
        pull R (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) F (n + 1) x = 0 →
        pull R (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V))) F (n + 1) x = 0 →
        ∃ y : H R (sch.obj (U ⊓ V).toScheme) F n,
          ∀ {T : Scheme.{0}} (f : T ⟶ S) (a : H R (sch.obj (f ⁻¹ᵁ U).toScheme) F n)
            (b : H R (sch.obj (f ⁻¹ᵁ V).toScheme) F n),
            pull R (sch.map (f ∣_ (U ⊓ V))) F n y =
              pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_left))) F n a -
                pull R (sch.map (T.homOfLE (f.preimage_mono inf_le_right))) F n b →
            pull R (sch.map (f ∣_ (U ⊔ V))) F (n + 1) x = 0 := by
  intro R _ F S U V n x hx1 hx2
  obtain ⟨d, hd, hnat⟩ := mayerVietoris R F
  haveI := sch_pres
  have hc := cov R (rfl : U ⊔ V = U ⊔ V) le_sup_left le_sup_right
  obtain ⟨c, hc'⟩ := ((hd _ _ hc n).2.2 x).1 ⟨hx1, hx2⟩
  have P := (pb (rfl : U ⊓ V = U ⊓ V) inf_le_left inf_le_right
    (le_sup_left : U ≤ U ⊔ V) (le_sup_right : V ≤ U ⊔ V)).map sch
  refine ⟨pull R P.isoPullback.hom F n c, ?_⟩
  intro T f a b hab
  have hD : f ⁻¹ᵁ (U ⊔ V) = f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V := by
    ext; simp
  have hC : f ⁻¹ᵁ (U ⊓ V) = f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V := by
    ext; simp
  have hcT := cov R hD (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)
  have PT := (pb hC (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)
    (f.preimage_mono le_sup_left) (f.preimage_mono le_sup_right)).map sch
  have hu : sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ U) ≫ sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have hv : sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))) ≫ sch.map (f ∣_ (U ⊔ V)) =
      sch.map (f ∣_ V) ≫ sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  have key := hnat (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V))))
    (sch.map (S.homOfLE (le_sup_left : U ≤ U ⊔ V))) (sch.map (S.homOfLE (le_sup_right : V ≤ U ⊔ V)))
    (sch.map (f ∣_ (U ⊔ V))) (sch.map (f ∣_ U)) (sch.map (f ∣_ V)) hu hv hcT hc n c
  rw [← hc', key, ((hd (sch.map (T.homOfLE (f.preimage_mono (le_sup_left : U ≤ U ⊔ V))))
    (sch.map (T.homOfLE (f.preimage_mono (le_sup_right : V ≤ U ⊔ V)))) hcT n).2.1)]
  refine ⟨a, b, ?_⟩
  have inj : Function.Injective (pull R PT.isoPullback.hom F n) := by
    intro z w h
    have h2 := congrArg (pull R PT.isoPullback.inv F n) h
    rwa [← pull_comp, ← pull_comp, Iso.inv_hom_id, pull_id, pull_id] at h2
  apply inj
  rw [map_sub, ← pull_comp, ← pull_comp, ← pull_comp, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd, ← hab, ← pull_comp]
  refine congrArg (fun φ => pull R φ F n c) ?_
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_fst, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_fst, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
  · rw [Category.assoc, Category.assoc, pullback.map, pullback.lift_snd, IsPullback.isoPullback_hom_snd_assoc,
      IsPullback.isoPullback_hom_snd, ← Functor.map_comp, ← Functor.map_comp, sq_lemma']
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionRepresentingRelativeClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

noncomputable section

private def cut (C : DC) (x : C.Tot) : C.Tot
  | 0, s => x 0 s
  | _ + 1, _ => 0

private theorem unit_map {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (u : ℤˣ) (a : A) :
    f (u • a) = u • f a := by
  simp [Units.smul_def]

private theorem split (C : DC) (rd : ∀ p s, C.A (p + 1) s →+ C.A p s)
    (h0 : ∀ p s, Even p → ∀ a, C.δ p s a = 0)
    (h1 : ∀ p s, Odd p → ∀ a, C.δ p s (rd p s a) = a)
    (h2 : ∀ p s, Odd p → ∀ a, rd p s (C.δ p s a) = a)
    (h3 : ∀ p s t a, C.d p s t (rd p s a) = rd p t (C.d (p + 1) s t a))
    (m : ℤ) (x : C.Tot) (hd : C.Deg m x) (hD : C.D m x = 0) :
    C.Deg m (cut C x) ∧ C.D m (cut C x) = 0 ∧ C.Deg m (x - cut C x) ∧
      ∃ y, C.Deg (m - 1) y ∧ C.D (m - 1) y = x - cut C x := by
  have key : ∀ (q : ℕ) (s : ℤ) (a : C.A q s), m.negOnePow • m.negOnePow • a = a := by
    intro q s a
    rw [smul_smul, Int.units_mul_self, one_smul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p s hps
    cases p with
    | zero => exact hd 0 s hps
    | succ p => rfl
  · funext p t
    cases p with
    | zero =>
      have := congrFun (congrFun hD 0) t
      simpa [DC.D, cut] using this
    | succ p =>
      cases p with
      | zero => simp [DC.D, cut, h0 0 t ⟨0, rfl⟩]
      | succ p => simp [DC.D, cut]
  · intro p s hps
    cases p with
    | zero => simp [cut]
    | succ p => simp [cut, hd (p + 1) s hps]
  · refine ⟨fun p t => if Odd p then m.negOnePow • rd p t (x (p + 1) t) else 0, ?_, ?_⟩
    · intro p t hpt
      dsimp only
      split_ifs
      · rw [hd (p + 1) t (by push_cast; omega)]
        simp
      · rfl
    · funext p t
      cases p with
      | zero => simp [DC.D, cut]
      | succ p =>
        have hx := congrFun (congrFun hD (p + 2)) t
        simp only [DC.D] at hx
        simp only [DC.D, cut, sub_add_cancel, Pi.sub_apply, sub_zero]
        rcases Nat.even_or_odd p with hp | hp
        · have hp1 : Odd (p + 1) := hp.add_one
          have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
          simp only [hp1, hp0, if_true, if_false, map_zero, smul_zero, add_zero]
          rw [unit_map, h3]
          have hx' : C.d (p + 2) (t - 1) t (x (p + 2) (t - 1)) = m.negOnePow • C.δ (p + 1) t (x (p + 1) t) := by
            rw [Int.negOnePow_succ] at hx
            rw [eq_neg_of_add_eq_zero_left hx, Units.neg_smul, neg_neg]
          rw [hx', unit_map, h2 _ _ hp1, key]
        · have hp1 : ¬ Odd (p + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr hp
          simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
          rw [unit_map, h1 _ _ hp, key]

private theorem alt {G : Type*} [AddCommGroup G] (b : G) (n : ℕ) :
    ∑ i : Fin n, (-1 : ℤ) ^ (i : ℕ) • b = if Even n then 0 else b := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih]
    by_cases h : Even n
    · have h' : ¬ Even (n + 1) := by simpa [Nat.even_add_one] using h
      simp [h, h', h.neg_one_pow]
    · have h' : Even (n + 1) := by simpa [Nat.even_add_one] using h
      have ho : Odd n := Nat.not_even_iff_odd.1 h
      simp [h, h', ho.neg_one_pow]

section Concrete
variable {R : Type} [CommRing R] {X : Scheme.{0}}

private def rdF (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (p : ℕ) (M : Shv R) : Fam Z (p + 1) M →+ Fam Z p M where
  toFun a := ⟨fun W t => a.1 W t, fun V W g t => a.2.1 V W g t, fun W t h => a.2.2 W t (hZ _ _ _ _ h)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem delta_apply (Z : Sub (sch.obj X)) (p : ℕ) (M : Shv R) (a : Fam Z p M) (W : Scheme.{0}) (t : W ⟶ X) :
    (Fam.δ Z p M (0 : ℤ).negOnePow a).1 W t = if Even (p + 2) then 0 else a.1 W t := by
  change (0 : ℤ).negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • a.1 W t = _
  rw [Int.negOnePow_zero, one_smul, alt]

private theorem fam_split (Z : Sub (sch.obj X)) (hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X), Z.mem p W t → Z.mem q W t)
    (K : Cx R) (m : ℤ) (x : (famDC Z K 0).Tot) (hd : (famDC Z K 0).Deg m x) (hD : (famDC Z K 0).D m x = 0) :
    (famDC Z K 0).Deg m (cut _ x) ∧ (famDC Z K 0).D m (cut _ x) = 0 ∧ (famDC Z K 0).Deg m (x - cut _ x) ∧
      ∃ y, (famDC Z K 0).Deg (m - 1) y ∧ (famDC Z K 0).D (m - 1) y = x - cut _ x := by
  refine split (famDC Z K 0) (fun p s => rdF Z hZ p (K.X (s + 0))) ?_ ?_ ?_ ?_ m x hd hD
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : Even (p + 2) := by rw [Nat.even_add]; simp [hp]
    rw [if_pos this] at e
    exact e
  · intro p s hp (a : Fam Z (p + 1) (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) (rdF Z hZ p (K.X (s + 0)) a) W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s hp (a : Fam Z p (K.X (s + 0)))
    apply Subtype.ext
    funext W (t : W ⟶ X)
    have e := delta_apply Z p (K.X (s + 0)) a W t
    have : ¬ Even (p + 2) := by rw [Nat.even_add]; simp [Nat.not_even_iff_odd.mpr hp]
    rw [if_neg this] at e
    exact e
  · intro p s t a
    rfl

end Concrete

theorem UpperTheory.exists_section_representing_relativeClass :
    ∀ (q : ℕ) (X : Scheme.{0}) (U : X.Opens) (m j : ℤ) (c : Hs q (opn U) m j), ∃ β : Sec ((res _ (tw q j)).X m) X, IsRep U β c.1 := by
  intro q X U m j c
  have TM := UpperTheory.relativeCohomology_isTotalModel_of_image q (opn U) j 0 m m (by simp)
  have hZ : ∀ (p q : ℕ) (W : Scheme.{0}) (t : W ⟶ X),
      (Sub.img (opn U).hom).mem p W t → (Sub.img (opn U).hom).mem q W t :=
    fun _ _ _ _ h => h
  obtain ⟨x, hxd, hxD, hxr⟩ := TM.surj c
  obtain ⟨hcd, hcD, hrd, y, hyd, hyD⟩ := fam_split (Sub.img (opn U).hom) hZ _ m x hxd hxD
  obtain ⟨c0, hc0⟩ := TM.ex _ hcd hcD
  have hsub := TM.sub _ _ _ _ hxr hc0
  have hz : c - c0 = 0 := (TM.zero _ _ hrd hsub).2 ⟨y, hyd, hyD⟩
  have hcc : c = c0 := sub_eq_zero.mp hz
  rw [← hcc] at hc0
  obtain ⟨γ, hγ, hcomp, hinr⟩ := hc0
  have cover := (UpperTheory.doubleMappingCylinder_cochain_extension (ZMod q) (opn U)).1
  have hhi : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + m = s) (W : Scheme)
      (z : Sx (dbl (opn U)) (p + 1) W), ev γ.1 (p + 1) s h W z = 0 := by
    intro p s h W z
    rcases cover (p + 1) W z with ⟨z', rfl⟩ | ⟨z', rfl⟩
    · have e : ∀ h' : -((p + 1 : ℕ) : ℤ) + m = s + 0,
          ev γ.1 (p + 1) (s + 0) h' W (Sx.map (dbl.inl (opn U)) z') = 0 := by
        intro h'
        rw [← hcomp (p + 1) s h' W z']
        rfl
      rw [add_zero] at e
      exact e h
    · exact hinr (p + 1) s h W z'
  have big : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 0),
      (∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)))) ∧
      Sec.res U.ι (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have nat : ∀ (W : Scheme) (t : W ⟶ X),
        ev γ.1 0 (m + 0) h W (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 W from t)) =
          Sec.res t (ev γ.1 0 (m + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) := by
      intro W t
      have e1 := hcomp 0 m h W t
      have e2 := hcomp 0 m h X (show Sx (opn U).right 0 X from 𝟙 X)
      have e := (cut _ x 0 m).2.1 W X t (show Sx (opn U).right 0 X from 𝟙 X)
      have r : Sx.res t (show Sx (opn U).right 0 X from 𝟙 X) = (show Sx (opn U).right 0 W from t) :=
        Category.comp_id t
      exact e1.symm.trans ((congrArg (fun z => (cut _ x 0 m).1 W z) r.symm).trans
        (e.symm.trans (congrArg (Sec.res t) e2)))
    refine ⟨nat, ?_⟩
    rw [← nat]
    have mem : (Sub.img (opn U).hom).mem 0 U U.ι := by
      refine ⟨(show Sx (sch.obj (U : Scheme.{0})) 0 U from 𝟙 (U : Scheme.{0})), ?_⟩
      dsimp [Sx.map, opn, sch, disc]
      simp
    exact (hcomp 0 m h U U.ι).symm.trans ((cut _ x 0 m).2.2 U U.ι mem)
  rw [add_zero] at big
  have dz : ∀ (h : -((0 : ℕ) : ℤ) + m = m + 1 - 1 + 0),
      Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))
        (ev γ.1 0 (m + 1 - 1 + 0) h X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X))) = 0 := by
    intro h
    have e2 := hcomp 0 (m + 1 - 1) h X (show Sx (opn U).right 0 X from 𝟙 X)
    have e := congrArg (fun a => a.1 X (show Sx (opn U).right 0 X from 𝟙 X)) (congrFun (congrFun hcD 0) (m + 1))
    refine (congrArg (Sec.map ((res (ZMod q) (tw q j)).d (m + 1 - 1 + 0) (m + 1 + 0))) e2).symm.trans ?_
    exact e
  rw [add_zero, add_zero, add_sub_cancel_right] at dz
  exact ⟨ev γ.1 0 m (by simp) X (Sx.map (dbl.inl (opn U)) (show Sx (opn U).right 0 X from 𝟙 X)),
    dz _, (big _).2, γ, hγ, fun W t => (big _).1 W t, fun W t => hinr 0 m _ W t, hhi⟩

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsUniqueSectionOfEtaleFaithfullyFlatDescent
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma sec_res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (a : Sec F U) : Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

private lemma cover_loc (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    [Module.FaithfullyFlat A C] [Algebra.Etale A C] :
    Loc (Spec (CommRingCat.of A)) (fun V g => ∃ h : V ⟶ Spec (CommRingCat.of C),
      h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = g) := by
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro x
    have hff : (CommRingCat.ofHom (algebraMap A C)).hom.FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
    have hs := ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A C))).mpr hff).2
    have het : Etale (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    obtain ⟨y, hy⟩ := hs.surj x
    exact ⟨_, Spec.map (CommRingCat.ofHom (algebraMap A C)), inferInstance, het, ⟨y, hy⟩, 𝟙 _,
      Category.id_comp _⟩
  · rintro V W g k ⟨h, rfl⟩
    exact ⟨k ≫ h, Category.assoc _ _ _⟩

private lemma lift_wd {R : Type} [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
    (w : Sec F (Spec (CommRingCat.of C)))
    (hw : Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w)
    {V : Scheme.{0}} (h h' : V ⟶ Spec (CommRingCat.of C))
    (e : h ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)) = h' ≫ Spec.map (CommRingCat.ofHom (algebraMap A C))) :
    Sec.res h w = Sec.res h' w := by
  set ψ := pullback.lift h h' e ≫ (pullbackSpecIso A C C).hom with hψ
  have hL : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom) = h := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_fst]
    exact pullback.lift_fst _ _ _
  have hR : ψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom) = h' := by
    rw [hψ, Category.assoc]
    erw [pullbackSpecIso_hom_snd]
    exact pullback.lift_snd _ _ _
  rw [← hL, ← hR, ← sec_res_res, hw, sec_res_res]

theorem UpperTheory.existsUnique_section_of_etale_faithfullyFlat_descent :
    ∀ (R : Type) [CommRing R] (F : Shv R) (A C : Type) [CommRing A] [CommRing C] [Algebra A C]
        [Module.FaithfullyFlat A C] [Algebra.Etale A C] (w : Sec F (Spec (CommRingCat.of C))),
        Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C).toRingHom)) w =
          Sec.res (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : C →ₐ[A] C ⊗[A] C).toRingHom)) w →
        ∃! y : Sec F (Spec (CommRingCat.of A)), Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) y = w := by
  intro R _ F A C _ _ _ _ _ w hw
  obtain ⟨S, hS, hSP⟩ := cover_loc A C
  choose lf hlf using hSP
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.EtC.sec_ext_glue R F _).2 S hS (fun V g hg => Sec.res (lf V g hg) w) (by
    intro V W g k hg
    rw [sec_res_res]
    apply lift_wd F A C w hw
    rw [Category.assoc, hlf, hlf])
  have hex : Sec.res (Spec.map (CommRingCat.ofHom (algebraMap A C))) a = w := by
    apply (_root_.GlobalTheory.EtC.sec_ext_glue R F _).1
    have hloc : Loc (Spec (CommRingCat.of C))
        (fun V g => S.arrows (g ≫ Spec.map (CommRingCat.ofHom (algebraMap A C)))) :=
      GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.1 _ _ _ (fun V g => S.arrows g) ⟨S, hS, fun _ _ h => h⟩
    refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ hloc ?_
    intro V g hg
    rw [sec_res_res, ha V _ hg]
    exact lift_wd F A C w hw _ _ (hlf _ _ _)
  refine ⟨a, hex, ?_⟩
  intro y hy
  apply (_root_.GlobalTheory.EtC.sec_ext_glue R F _).1
  refine GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 _ _ _ (cover_loc A C) ?_
  rintro V g ⟨h, rfl⟩
  rw [← sec_res_res, ← sec_res_res, hy, hex]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.HomAcyclicFreePullbackYonedaOfInjectiveRestricti
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafGhostCut UpperTheory.Et.Loc

private lemma res_val {R : Type} [CommRing R] {X : Scheme.{0}} {J : Shv R} (φ : (free R).obj (yoneda.obj X) ⟶ J)
    {V : Scheme.{0}} (x : V ⟶ X) :
    Sec.map φ (freeGen R (yoneda.obj X) V x) = Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h3 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.2.1 V X x (𝟙 X)
  have nat : Sec.res x (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) =
      Sec.map φ (Sec.res x (freeGen R (yoneda.obj X) X (𝟙 X))) := by
    simp only [Sec.res, Sec.map]
    exact (congrArg (fun f => ModuleCat.Hom.hom f (freeGen R (yoneda.obj X) X (𝟙 X)))
      (φ.hom.naturality x.op)).symm
  rw [nat, h3]
  simp

private noncomputable def evE (R : Type) [CommRing R] (X : Scheme.{0}) (J : Shv R) :
    ((free R).obj (yoneda.obj X) ⟶ J) ≃ₗ[ULift.{1} R] Sec J X :=
  LinearEquiv.ofBijective
    { toFun := fun φ => Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro φ ψ h
      refine (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).2.1 φ ψ fun U x => ?_
      rw [res_val φ x, res_val ψ x]
      exact congrArg (Sec.res x) h,
     by
      intro s
      obtain ⟨φ, hφ⟩ := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X) J).1 (fun U x => Sec.res x s) (by
        intro V U g x
        simp [Sec.res])
      refine ⟨φ, ?_⟩
      refine (hφ X (𝟙 X)).trans ?_
      simp [Sec.res]⟩

private lemma pullbackSymmetry_lift_map_comm {A A' Y B : Scheme.{0}} (p : Y ⟶ B) (u : A ⟶ B) (u' : A' ⟶ B) (l : A' ⟶ A) (hl : l ≫ u = u') :
    pullback.lift (pullback.fst u' p ≫ l) (pullback.snd u' p)
        (by rw [Category.assoc, hl, pullback.condition]) ≫ (pullbackSymmetry p u).inv =
      (pullbackSymmetry p u').inv ≫ pullback.map p u' p u (𝟙 Y) l (𝟙 B) (by simp) (by simp [hl]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullbackSymmetry_inv_comp_fst, pullback.lift_snd, Category.assoc, pullback.lift_fst]
    simp
  · rw [Category.assoc, pullbackSymmetry_inv_comp_snd, pullback.lift_fst, Category.assoc, pullback.lift_snd]
    simp

private lemma sym_nat {B Y : Scheme.{0}} (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) :
    (LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a) ≫ (pullbackSymmetry p U.hom).inv =
      (pullbackSymmetry p U'.hom).inv ≫ resY p a := by
  have w : a.left ≫ U.hom = U'.hom := Over.w ((LateralTheory.EWeil.AcycPf.incl B).map a)
  exact pullbackSymmetry_lift_map_comm p U.hom U'.hom a.left w

private lemma res_res {R : Type} [CommRing R] {F : Shv R} {U V W : Scheme.{0}} (f : V ⟶ U) (g : W ⟶ V) (s : Sec F U) :
    Sec.res g (Sec.res f s) = Sec.res (g ≫ f) s := by
  simp [Sec.res]

private lemma ev_pre {R : Type} [CommRing R] {X X' : Scheme.{0}} {J : Shv R} (f : X' ⟶ X)
    (φ : (free R).obj (yoneda.obj X) ⟶ J) :
    Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.res f (Sec.map φ (freeGen R (yoneda.obj X) X (𝟙 X))) := by
  have h4 := (GlobalTheory.T.free_sections_ext_res_map R (yoneda.obj X') J).2.2.2 (yoneda.obj X) (yoneda.map f) X' (𝟙 X')
  have hc : Sec.map ((free R).map (yoneda.map f) ≫ φ) (freeGen R (yoneda.obj X') X' (𝟙 X')) =
      Sec.map φ (Sec.map ((free R).map (yoneda.map f)) (freeGen R (yoneda.obj X') X' (𝟙 X'))) := rfl
  rw [hc, h4, ← res_val φ f]
  congr 2

private noncomputable def isoHP (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B) (J : Shv (ZMod q)) :
    HP (gY p ⋙ yoneda ⋙ free (ZMod q)) J ≅ (LateralTheory.EWeil.AcycPf.incl B).op ⋙ (LateralTheory.KummerTheory.tot p).op ⋙ J.obj :=
  NatIso.ofComponents (fun U => LinearEquiv.toModuleIso
      ((evE (ZMod q) (YU p U.unop) J).trans
        (J.obj.mapIso (pullbackSymmetry p U.unop.hom).symm.op).toLinearEquiv)) (by
    rintro ⟨U⟩ ⟨U'⟩ ⟨a⟩
    refine ModuleCat.hom_ext (LinearMap.ext fun φ => ?_)
    have h := ev_pre (R := ZMod q) (J := J) (resY p a) φ
    change Sec.res (pullbackSymmetry p U'.hom).inv (Sec.map ((free (ZMod q)).map (yoneda.map (resY p a)) ≫ φ)
        (freeGen (ZMod q) (yoneda.obj (YU p U')) (YU p U') (𝟙 _))) =
      Sec.res ((LateralTheory.KummerTheory.tot p).map ((LateralTheory.EWeil.AcycPf.incl B).map a))
        (Sec.res (pullbackSymmetry p U.hom).inv (Sec.map φ (freeGen (ZMod q) (yoneda.obj (YU p U)) (YU p U) (𝟙 _))))
    rw [h]
    refine (res_res _ _ _).trans (Eq.trans ?_ (res_res _ _ _).symm)
    exact congrArg (fun t => Sec.res (F := J) t _) (sym_nat p a).symm)

theorem UpperTheory.homAcyclic_free_pullback_yoneda_of_injective_restriction :
    LateralTheory.KummerTheory.InjSlice → LateralTheory.EWeil.AcycPf.RestrInj → ∀ (q : ℕ) {B Y : Scheme.{0}} (p : Y ⟶ B), Good (gY p ⋙ yoneda ⋙ free (ZMod q)) := by
  intro hI hR q B Y p J hJ
  obtain ⟨h1, i1⟩ := (hI (ZMod q) J p).1
  obtain ⟨h2, i2⟩ := hR (ZMod q) B ⟨(LateralTheory.KummerTheory.tot p).op ⋙ J.obj, h1⟩
  have e := isoHP q p J
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).2 h2, ?_⟩
  exact Injective.of_iso ((sheafToPresheaf _ _).preimageIso (X := ⟨_, h2⟩) e.symm) i2
end

