module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0004
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafImgHomPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (a : F ⟶ G) (b : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a ≫ b) x = Sec.map b (Sec.map a x) := rfl

theorem sec_map_add {R : Type} [CommRing R] {F G : Shv R} (a b : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (a + b) x = Sec.map a x + Sec.map b x := rfl

theorem sec_map_res {R : Type} [CommRing R] {F G : Shv R} (a : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map a x) = Sec.map a (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← a.hom.naturality]

theorem LeafImgHom_of (hG : LeafGen) : LeafImgHom := by
  intro S R _ _ I J ρ
  have ex : ∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s), ∃ ψ : (free R).obj P ⟶ J.X s,
      ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x)) := by
    intro P s φ
    refine (hG R P).2.2.2 (J.X s) (fun U x => ρ.app U s (Sec.map φ (freeGen S P U x))) ?_
    intro V U g x
    rw [ρ.nat, sec_map_res, (hG S P).1]
  choose T hT using ex
  have ext : ∀ (P : PSh) (s : ℤ) (ψ ψ' : (free R).obj P ⟶ J.X s),
      (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map ψ (freeGen R P U x) = Sec.map ψ' (freeGen R P U x)) → ψ = ψ' :=
    fun P s ψ ψ' h => (hG R P).2.2.1 _ ψ ψ' h
  refine ⟨fun P s => { toFun := T P s, map_zero' := ?_, map_add' := ?_ }, ?_, ?_, ?_⟩
  · apply ext; intro U x
    rw [hT]; show ρ.app U s 0 = 0; exact map_zero _
  · intro φ ψ; apply ext; intro U x
    rw [sec_map_add, hT, hT, hT, sec_map_add, map_add (f := _)]
  · intro P s φ U x; exact hT P s φ U x
  · intro P s t φ; apply ext; intro U x
    show Sec.map (T P t (φ ≫ I.d s t)) _ = Sec.map (T P s φ ≫ J.d s t) _
    rw [hT, sec_map_comp, sec_map_comp, hT, ρ.comm]
  · intro P P' f s φ; apply ext; intro U x
    show Sec.map (T P s ((free S).map f ≫ φ)) _ = Sec.map ((free R).map f ≫ T P' s φ) _
    rw [hT, sec_map_comp, sec_map_comp, (hG S P).2.1, (hG R P).2.1, hT]

end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafImgPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd
namespace ImgPf

variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}
  (T0 : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s))

def T' (E : Spc) (p s : ℤ) : (((chains S).obj E).X p ⟶ I.X s) →+ (((chains R).obj E).X p ⟶ J.X s) :=
  if h : -(((-p).toNat : ℕ) : ℤ) = p then
    { toFun := fun φ => (((chains R).obj E).XIsoOfEq h).inv ≫ (chainsXIso R E _).hom ≫
        T0 _ s ((chainsXIso S E _).inv ≫ (((chains S).obj E).XIsoOfEq h).hom ≫ φ)
      map_zero' := by simp
      map_add' := by intros; simp [Preadditive.comp_add] }
  else 0

theorem T'_eq (E : Spc) (k : ℕ) (s : ℤ) (φ : ((chains S).obj E).X (-(k : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s φ = (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
  have key : ∀ (k' : ℕ) (h' : -(k' : ℤ) = -(k : ℤ)), (((chains R).obj E).XIsoOfEq h').inv ≫ (chainsXIso R E k').hom ≫
      T0 _ s ((chainsXIso S E k').inv ≫ (((chains S).obj E).XIsoOfEq h').hom ≫ φ) =
      (chainsXIso R E k).hom ≫ T0 _ s ((chainsXIso S E k).inv ≫ φ) := by
    intro k' h'
    obtain rfl : k' = k := by omega
    simp [HomologicalComplex.XIsoOfEq_rfl]
  unfold T'
  rw [dite_eq_left (by simp)]
  exact key _ _

theorem T'_pos (E : Spc) (p s : ℤ) (hp : 0 < p) : T' T0 E p s = 0 := by
  unfold T'
  rw [dite_eq_right (by omega)]

theorem T'_comp_d (E : Spc) (p s t : ℤ) (φ : ((chains S).obj E).X p ⟶ I.X s)
    (hd : ∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T0 P t (φ ≫ I.d s t) = T0 P s φ ≫ J.d s t) :
    T' T0 E p t (φ ≫ I.d s t) = T' T0 E p s φ ≫ J.d s t := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    rw [T'_eq, T'_eq, ← Category.assoc, hd, Category.assoc]
  · rw [T'_pos T0 E p t hp, T'_pos T0 E p s hp]
    simp

theorem T'_free (E E' : Spc) (k k' : ℕ) (s : ℤ) {ι : Type} [Fintype ι] (c : ι → ℤ)
    (u : ι → (E.obj (op (SimplexCategory.mk k)) ⟶ E'.obj (op (SimplexCategory.mk k'))))
    (gS : ((chains S).obj E).X (-(k : ℤ)) ⟶ ((chains S).obj E').X (-(k' : ℤ)))
    (gR : ((chains R).obj E).X (-(k : ℤ)) ⟶ ((chains R).obj E').X (-(k' : ℤ)))
    (hS : gS = (chainsXIso S E k).hom ≫ (∑ i, c i • (free S).map (u i)) ≫ (chainsXIso S E' k').inv)
    (hR : gR = (chainsXIso R E k).hom ≫ (∑ i, c i • (free R).map (u i)) ≫ (chainsXIso R E' k').inv)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ)
    (φ : ((chains S).obj E').X (-(k' : ℤ)) ⟶ I.X s) :
    T' T0 E (-(k : ℤ)) s (gS ≫ φ) = gR ≫ T' T0 E' (-(k' : ℤ)) s φ := by
  rw [T'_eq, T'_eq, hS, hR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul, hn]

theorem T'_d (E : Spc) (p p' s : ℤ) (h : p + 1 = p') (φ : ((chains S).obj E).X p' ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).obj E).d p p' ≫ φ) = ((chains R).obj E).d p p' ≫ T' T0 E p' s φ := by
  rcases lt_or_ge p 0 with hp | hp
  · obtain ⟨k, rfl, rfl⟩ : ∃ k : ℕ, p = -((k + 1 : ℕ) : ℤ) ∧ p' = -(k : ℤ) := ⟨(-p - 1).toNat, by omega, by omega⟩
    refine T'_free T0 E E k.succ k s (fun i : Fin (k + 2) => ((-1 : ℤ) ^ (i : ℕ))) (fun i => E.δ i) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extend_d_eq ((chainsN S).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
    · refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat
        (i' := -((k + 1 : ℕ) : ℤ)) (j' := -(k : ℤ)) (i := k + 1) (j := k) rfl rfl).trans ?_
      unfold chainsXIso
      congr 2
      exact AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ k
  · have hz : ((chains S).obj E).d p p' = 0 := by
      apply (HomologicalComplex.isZero_extend_X _ _ p' ?_).eq_of_tgt
      intro i hi
      change -(i : ℤ) = p' at hi
      omega
    rw [hz, T'_pos T0 E p' s (by omega)]
    simp

theorem T'_map (E E' : Spc) (f : E ⟶ E') (p s : ℤ) (φ : ((chains S).obj E').X p ⟶ I.X s)
    (hn : ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T0 P s ((free S).map f ≫ φ) = (free R).map f ≫ T0 P' s φ) :
    T' T0 E p s (((chains S).map f).f p ≫ φ) = ((chains R).map f).f p ≫ T' T0 E' p s φ := by
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
    refine T'_free T0 E E' k k s (fun _ : Unit => 1) (fun _ => f.app _) _ _ ?_ ?_ hn φ
    · refine (HomologicalComplex.extendMap_f ((chainsN S).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
    · refine (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat
        (i := k) (i' := -(k : ℤ)) rfl).trans ?_
      unfold chainsXIso
      congr 2
      simp only [Finset.univ_unique, Finset.sum_singleton, one_smul]
      rfl
  · rw [T'_pos T0 E p s hp, T'_pos T0 E' p s hp]
    simp

def TC (E : Spc) (n : ℤ) : Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n where
  toFun α := Cochain.mk fun p q h => T' T0 E p q (α.v p q h)
  map_zero' := Cochain.ext _ _ fun p q h => by simp
  map_add' α β := Cochain.ext _ _ fun p q h => by simp [Cochain.add_v]

theorem TC_v (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p q : ℤ) (h : p + n = q) :
    (TC T0 E n α).v p q h = T' T0 E p q (α.v p q h) :=
  Cochain.mk_v (fun p q h => T' T0 E p q (α.v p q h)) p q h

end ImgPf

open ImgPf in
theorem LeafImg_of (hI : LeafImgHom) : LeafImg := by
  intro S R _ _ I J ρ
  obtain ⟨T0, hgen, hd, hn⟩ := hI S R I J ρ
  refine ⟨fun E n => TC T0 E n, ?_, ?_, ?_⟩
  · intro E n α p s h U x
    unfold ev
    rw [TC_v, T'_eq, Iso.inv_hom_id_assoc]
    exact hgen _ _ _ U x
  · intro E n m α
    by_cases hnm : n + 1 = m
    · refine Cochain.ext _ _ fun p q hpq => ?_
      rw [TC_v, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl, δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
        map_add, Units.smul_def, Units.smul_def, map_zsmul, T'_comp_d T0 E _ _ _ _ hd, TC_v, TC_v,
        T'_d T0 E p (p + 1) q rfl _ hn]
    · rw [δ_shape n m hnm, δ_shape n m hnm, map_zero]
  · intro E E' f n α
    refine Cochain.ext _ _ fun p q hpq => ?_
    simp only [pb, TC_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    exact T'_map T0 E E' f p q _ hn

end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafInvPf
section
noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

variable {A : Type} [CommRing A]

theorem inv_retr (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) :
    ∃ r : Localization.Away x →+* A ⧸ I, r.comp (algebraMap A (Localization.Away x)) = Ideal.Quotient.mk I := by
  have hu0 : IsUnit (Ideal.Quotient.mk I x) := by rw [hx]; exact isUnit_one
  exact ⟨IsLocalization.Away.lift (S := Localization.Away x) (g := Ideal.Quotient.mk I) x hu0,
    IsLocalization.Away.lift_comp (S := Localization.Away x) x hu0⟩

theorem inv_surj (I : Ideal A) (x : A) (hx : Ideal.Quotient.mk I x = 1) (s : Localization.Away x) :
    ∃ a : A, s - algebraMap A (Localization.Away x) a ∈ I.map (algebraMap A (Localization.Away x)) := by
  obtain ⟨⟨a, ⟨u, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) s
  refine ⟨a, ?_⟩
  have h1 := IsLocalization.mk'_spec (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)
  have h2 : 1 - x ^ n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hx, one_pow, map_one, sub_self]
  rw [← h1]
  have h3 : IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) -
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (x ^ n) =
      IsLocalization.mk' (Localization.Away x) a (⟨x ^ n, n, rfl⟩ : Submonoid.powers x) *
        algebraMap A (Localization.Away x) (1 - x ^ n) := by
    rw [map_sub, map_one, mul_sub, mul_one]
  rw [h3]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ h2)

theorem inv_univ (I : Ideal A) (i : A) (hi : i ∈ I) : Univ (algebraMap A (Localization.Away (1 + i))) I := by
  intro B _ J hJ ψ hψ
  have hu : IsUnit (ψ (1 + i)) := by
    have hj : ψ i ∈ Ideal.jacobson ⊥ := by
      rw [Ideal.jacobson_bot]
      exact hJ.jac (hψ hi)
    have := (Ideal.mem_jacobson_bot.1 hj) 1
    rw [mul_one, add_comm] at this
    rwa [map_add, map_one]
  refine ⟨IsLocalization.Away.lift (1 + i) hu, RingHom.ext fun a => IsLocalization.Away.lift_eq (1 + i) hu a, ?_⟩
  intro χ hχ
  apply IsLocalization.ringHom_ext (Submonoid.powers (1 + i))
  rw [hχ]
  exact RingHom.ext fun a => (IsLocalization.Away.lift_eq (1 + i) hu a).symm

theorem LeafInv_of : LeafInv := by
  intro A _ I i hi
  have hx : Ideal.Quotient.mk I (1 + i) = 1 := by
    rw [map_add (f := _), map_one, Ideal.Quotient.eq_zero_iff_mem.2 hi, add_zero]
  refine ⟨Localization.Away (1 + i), inferInstance, algebraMap A (Localization.Away (1 + i)),
    ⟨?_, inv_retr I _ hx, inv_surj I _ hx, inv_univ I i hi⟩, IsLocalization.Away.algebraMap_isUnit (1 + i)⟩
  rw [RingHom.etale_algebraMap]
  exact Algebra.Etale.of_isLocalizationAway (1 + i)

end LateralTheory.CohomologicalPurity.Hz
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

def EtaleLocBase : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (Y : Scheme.{0}) (g : Y ⟶ X),
  ∃ (D' : J ⥤ Scheme.{0}) (c' : ∀ j, D'.obj j ⟶ Y), (∀ j, IsOpenImmersion (c' j)) ∧
    (∀ y : Y, ∃ j, y ∈ Set.range (c' j)) ∧
    (∀ (y : Y) j k, y ∈ Set.range (c' j) → y ∈ Set.range (c' k) → ∃ l, l ≤ j ∧ l ≤ k ∧ y ∈ Set.range (c' l)) ∧
    ∃ hc' : Coc (D' ⋙ yoneda) (fun j => yoneda.map (c' j)),
      Nonempty (Arrow.mk (pullback.snd (aug _ hc) (sch.map g)) ≅ Arrow.mk (aug _ hc'))

def EtaleLocAug : Prop := ∀ (J : Type) [Preorder J] (D : J ⥤ Scheme.{0}) (X : Scheme.{0}) (c : ∀ j, D.obj j ⟶ X),
  (∀ j, IsOpenImmersion (c j)) → (∀ x : X, ∃ j, x ∈ Set.range (c j)) →
  (∀ (x : X) j k, x ∈ Set.range (c j) → x ∈ Set.range (c k) → ∃ l, l ≤ j ∧ l ≤ k ∧ x ∈ Set.range (c l)) →
  ∀ (hc : Coc (D ⋙ yoneda) fun j => yoneda.map (c j)) (R : Type) [CommRing R], QuasiIso ((chains R).map (aug _ hc))

theorem LeafLocCut.goal_of (hb : EtaleLocBase) (ha : EtaleLocAug) : LeafLoc := by
  intro J _ D X c ho hcov hdir hc R _ Y g
  obtain ⟨D', c', ho', hcov', hdir', hc', ⟨e⟩⟩ := hb J D X c ho hcov hdir hc Y g
  have h := ha J D' Y c' ho' hcov' hdir' hc' R
  exact (quasiIso_iff_of_arrow_mk_iso _ _ ((chains R).mapArrow.mapIso e.symm)).1 h

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.ChartCut

theorem LeafLoc_of : LeafLoc := by
  intro d P x W hxW
  have := P.cl; have := P.smX; have := P.smZ
  obtain ⟨T, hT, hxT, -⟩ := exists_isAffineOpen_mem_and_subset (x := P.p.base x) (U := ⊤) trivial
  obtain ⟨V, hV, hxV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ P.p ⁻¹ᵁ T) ⟨hxW, hxT⟩
  have e : V ≤ P.p ⁻¹ᵁ T := fun y hy => (hVW hy).2
  refine ⟨⟨V, hV⟩, hxV, fun y hy => (hVW hy).1, Γ(P.S, T), inferInstance, (P.p.appLE T V e).hom, ?_, ?_⟩
  · exact HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension (P.e + d)) P.p P.smX ⟨T, hT⟩ ⟨V, hV⟩ e
  · have hV' : IsAffineOpen (P.ι ⁻¹ᵁ V) := hV.preimage P.ι
    have e2 : P.ι ⁻¹ᵁ V ≤ (P.ι ≫ P.p) ⁻¹ᵁ T := fun y hy => e hy
    have h2 := HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension P.e) (P.ι ≫ P.p) P.smZ
      ⟨T, hT⟩ ⟨P.ι ⁻¹ᵁ V, hV'⟩ e2
    have hc : (P.ι ≫ P.p).appLE T (P.ι ⁻¹ᵁ V) e2 = P.p.appLE T V e ≫ P.ι.app V := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [hc] at h2
    have hs : Function.Surjective (P.ι.app V).hom := P.ι.app_surjective V hV
    have hk : P.ι.ker.ideal ⟨V, hV⟩ = RingHom.ker (P.ι.app V).hom := P.ι.ker_apply ⟨V, hV⟩
    rw [hk]
    let eqv := RingHom.quotientKerEquivOfSurjective hs
    have heq : (Ideal.Quotient.mk (RingHom.ker (P.ι.app V).hom)).comp (P.p.appLE T V e).hom =
        eqv.symm.toRingHom.comp ((P.p.appLE T V e ≫ P.ι.app V).hom) := by
      ext a
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      apply eqv.injective
      simp [eqv]
    rw [heq]
    exact (RingHom.locally_respectsIso
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left _ _ h2

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafMatPf
section
noncomputable section
open Matrix

namespace LateralTheory.CohomologicalPurity.MatPf

theorem gens {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A)
    (h : Ideal.span (Set.range x) ≤ Ideal.span (Set.range y)) :
    ∃ N : Matrix (Fin d) (Fin d) A, x = N *ᵥ y := by
  have : ∀ i, ∃ c : Fin d → A, ∑ j, c j * y j = x i := fun i =>
    (Ideal.mem_span_range_iff_exists_fun).1 (h (Ideal.subset_span ⟨i, rfl⟩))
  choose c hc using this
  exact ⟨Matrix.of c, funext fun i => by simp [mulVec, dotProduct, hc]⟩

theorem red {d : ℕ} {A : Type} [CommRing A] (x y : Fin d → A) (N N' T : Matrix (Fin d) (Fin d) A)
    (hy : y = N *ᵥ x) (hx : x = N' *ᵥ y) : y = (N + T * (1 - N' * N)) *ᵥ x := by
  have : (1 - N' * N) *ᵥ x = 0 := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← hy, ← hx, sub_self]
  rw [add_mulVec, ← mulVec_mulVec, this, mulVec_zero, add_zero, hy]

theorem glue_dom (hD : ∀ (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D),
    N' * N + E = 1 → ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0) : LateralTheory.CohomologicalPurity.Cl.LeafMat := by
  intro d A _ x y hxy p
  obtain ⟨N, hN⟩ := gens y x hxy.ge
  obtain ⟨N', hN'⟩ := gens x y hxy.le
  let f := Ideal.Quotient.mk p.asIdeal
  obtain ⟨T₀, hT₀⟩ := hD d (A ⧸ p.asIdeal) (f.mapMatrix N) (f.mapMatrix (1 - N' * N)) (f.mapMatrix N')
    (by rw [← map_mul, ← map_add (f := _), add_sub_cancel, map_one])
  choose T hT using fun i j => Ideal.Quotient.mk_surjective (I := p.asIdeal) (T₀ i j)
  refine ⟨N + Matrix.of T * (1 - N' * N), ?_, red x y N N' _ hN hN'⟩
  intro hm
  apply hT₀
  have h1 : f.mapMatrix (Matrix.of T) = T₀ := by ext i j; simp [f, hT]
  have := RingHom.map_det f (N + Matrix.of T * (1 - N' * N))
  rw [map_add (f := _), map_mul, h1, (Ideal.Quotient.eq_zero_iff_mem).2 hm] at this
  exact this.symm

theorem fld {d : ℕ} {k : Type} [Field k] (N E N' : Matrix (Fin d) (Fin d) k) (h : N' * N + E = 1) :
    ∃ T : Matrix (Fin d) (Fin d) k, ∀ s : k, s ≠ 0 → (N + (s • T) * E).det ≠ 0 := by
  classical
  let n := Matrix.toLin' N
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range n)
  obtain ⟨K', hK⟩ := Submodule.exists_isCompl (LinearMap.ker n)
  have hr : Module.finrank k (LinearMap.ker n) = Module.finrank k C := by
    have h1 := LinearMap.finrank_range_add_finrank_ker n
    have h2 := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hr
  let t : (Fin d → k) →ₗ[k] (Fin d → k) :=
    C.subtype ∘ₗ e.toLinearMap ∘ₗ Submodule.linearProjOfIsCompl _ _ hK
  refine ⟨LinearMap.toMatrix' t, fun s hs hdet => ?_⟩
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  apply hv0
  have hE : E = 1 - N' * N := by rw [← h]; abel
  rw [add_mulVec, ← mulVec_mulVec, smul_mulVec, LinearMap.toMatrix'_mulVec] at hv
  have htC : ∀ w, t w ∈ C := fun w => (e _).2
  have hnv : n v = 0 := by
    have hm : n v ∈ C := by
      have : n v = -(s • t (E *ᵥ v)) := eq_neg_of_add_eq_zero_left (by simpa [n] using hv)
      rw [this]; exact C.neg_mem (C.smul_mem s (htC _))
    exact (Submodule.disjoint_def.1 hC.disjoint) _ (LinearMap.mem_range_self n v) hm
  have hNv : N *ᵥ v = 0 := by simpa [n] using hnv
  have hw : E *ᵥ v = v := by
    rw [hE, sub_mulVec, one_mulVec, ← mulVec_mulVec, hNv, mulVec_zero, sub_zero]
  rw [hw, hNv, zero_add, smul_eq_zero] at hv
  have htv : t v = 0 := hv.resolve_left hs
  have hker : v ∈ LinearMap.ker n := hnv
  have hp : Submodule.linearProjOfIsCompl _ _ hK v = ⟨v, hker⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hK ⟨v, hker⟩
  have : e ⟨v, hker⟩ = 0 := by
    apply Subtype.ext
    have := htv
    simp only [t, LinearMap.comp_apply, hp] at this
    exact this
  have he : e ⟨v, hker⟩ = e 0 := this.trans (e.toLinearMap.map_zero).symm
  have := congrArg Subtype.val (e.injective he)
  simpa using this

theorem dom (d : ℕ) (D : Type) [CommRing D] [IsDomain D] (N E N' : Matrix (Fin d) (Fin d) D)
    (h : N' * N + E = 1) : ∃ T : Matrix (Fin d) (Fin d) D, (N + T * E).det ≠ 0 := by
  classical
  let g := algebraMap D (FractionRing D)
  obtain ⟨T, hT⟩ := fld (g.mapMatrix N) (g.mapMatrix E) (g.mapMatrix N')
    (by rw [← map_mul, ← map_add (f := _), h, map_one])
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors D)
    (fun ij : Fin d × Fin d => T ij.1 ij.2)
  choose T' hT' using fun i j => hb (i, j)
  have h1 : g.mapMatrix (Matrix.of T') = g b • T := by
    ext i j; simp [g, hT', Algebra.smul_def]
  have hne : g b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  refine ⟨Matrix.of T', fun h0 => hT (g b) hne ?_⟩
  have := RingHom.map_det g (N + Matrix.of T' * E)
  rw [h0, map_zero, map_add (f := _), map_mul, h1] at this
  exact this.symm

end LateralTheory.CohomologicalPurity.MatPf

theorem LateralTheory.CohomologicalPurity.Cl.LeafMat_of : LateralTheory.CohomologicalPurity.Cl.LeafMat := LateralTheory.CohomologicalPurity.MatPf.glue_dom LateralTheory.CohomologicalPurity.MatPf.dom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafOffPf
section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafOff_of : LeafOff := by
  intro d P F
  apply le_antisymm F.h
  intro y hy
  change y ∉ PrimeSpectrum.zeroLocus (F.I : Set F.B)
  intro hz
  have hk : RingHom.ker (Ideal.Quotient.mk F.I) = F.I := Ideal.mk_ker
  have hr : y ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk F.I)) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, hk]; exact hz
  obtain ⟨y0, rfl⟩ := hr
  have hw := congrArg (fun g => g.base y0) F.cart.w
  simp only [Scheme.Hom.comp_base] at hw
  have hU : F.w.base ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I))).base y0) ∈ (P.U : Set P.X) := hy
  rw [P.hU] at hU
  exact hU ⟨F.z.base y0, hw.symm⟩

end LateralTheory.CohomologicalPurity.Cl
end

