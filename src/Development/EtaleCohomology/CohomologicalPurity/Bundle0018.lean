module

public import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0010
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafRefinePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex
namespace LateralTheory.CohomologicalPurity.TubeCut

variable {d : ℕ}

theorem hmap_congr (H : Hens) {A B : Type} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B} {φ ψ : A →+* B}
    (e : φ = ψ) (h : I ≤ J.comap φ) (h' : I ≤ J.comap ψ) : H.map φ h = H.map ψ h' := by subst e; rfl

theorem hmap_sq (H : Hens) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    {I : Ideal A} {J : Ideal B} {K : Ideal C} {L : Ideal D} (a : A →+* B) (b : B →+* D) (c : A →+* C) (e : C →+* D)
    (ha : I ≤ J.comap a) (hb : J ≤ L.comap b) (hc : I ≤ K.comap c) (he : K ≤ L.comap e) (e0 : b.comp a = e.comp c) :
    (H.map b hb).comp (H.map a ha) = (H.map e he).comp (H.map c hc) := by
  rw [← H.map_comp a b ha hb (fun x hx => hb (ha hx)), ← H.map_comp c e hc he (fun x hx => he (hc hx))]
  exact hmap_congr H e0 _ _

theorem appLE_congr {X Y : Scheme.{0}} {u v : X ⟶ Y} (e : u = v) (U : Y.Opens) (W : X.Opens) (h : W ≤ u ⁻¹ᵁ U) :
    u.appLE U W h = v.appLE U W (e ▸ h) := by subst e; rfl

theorem idl {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens) (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    P.ι.ker.ideal V ≤ (P'.ι.ker.ideal V').comap (φ.f.appLE V.1 V'.1 h).hom := by
  have := P.cl; have := P'.cl
  intro a ha
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at ha
  rw [Ideal.mem_comap, Scheme.Hom.ker_apply, RingHom.mem_ker]
  rw [← CommRingCat.comp_apply, P'.ι.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr φ.cart.w,
    Scheme.Hom.comp_appLE, CommRingCat.comp_apply, ha, map_zero]

theorem cotangentAtUnit_tangentBijection_naturality (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V1 V2 : P.X.affineOpens) (V1' V2' : P'.X.affineOpens)
    (h1 : V1'.1 ≤ φ.f ⁻¹ᵁ V1.1) (h2 : V2'.1 ≤ φ.f ⁻¹ᵁ V2.1) (hV : V1 ≤ V2) (hV' : V1' ≤ V2') :
    Spec.map (CommRingCat.ofHom (H.map _ (P'.ι.ker.ideal_le_comap_ideal hV'))) ≫
      Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V2.1 V2'.1 h2).hom (idl φ V2 V2' h2))) =
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V1.1 V1'.1 h1).hom (idl φ V1 V1' h1))) ≫
      Spec.map (CommRingCat.ofHom (H.map _ (P.ι.ker.ideal_le_comap_ideal hV))) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact hmap_sq H _ _ _ _ _ _ _ _ (by rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE])

theorem henselization_spec_map_commutes_with_smooth_pair_hom (H : Hens) {P' P : SP d} (φ : P'.Hom P) (V : P.X.affineOpens) (V' : P'.X.affineOpens)
    (h : V'.1 ≤ φ.f ⁻¹ᵁ V.1) :
    Spec.map (CommRingCat.ofHom (H.map (φ.f.appLE V.1 V'.1 h).hom (idl φ V V' h))) ≫ hensTo H P V =
      hensTo H P' V' ≫ φ.f := by
  dsimp only [hensTo, eta]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H.map_η, CommRingCat.ofHom_comp, Spec.map_comp_assoc]
  exact (congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec φ.f V.2 V'.2 h)).trans (Category.assoc _ _ _).symm

abbrev RJ {P' P : SP d} (φ : P'.Hom P) : Type :=
  {p : P'.X.affineOpens × P.X.affineOpens // Good P' p.1 ∧ Good P p.2 ∧ p.1.1 ≤ φ.f ⁻¹ᵁ p.2.1}

def Sys.ref (hC : LateralTheory.CohomologicalPurity.LeafChart) {P' P : SP d} (φ : P'.Hom P) : Sys P' where
  J := RJ φ
  V j := j.1.1
  mono h := (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1
  good j := j.2.1
  cov x := by
    obtain ⟨V, hV, -, g⟩ := hC d P (φ.f x) ⊤ trivial
    obtain ⟨V', hV', l, g'⟩ := hC d P' x (φ.f ⁻¹ᵁ V.1) hV
    exact ⟨⟨(V', V), g', g, l⟩, hV'⟩
  dir x j k hj hk := by
    have hj2 : φ.f x ∈ j.1.2.1 := j.2.2.2 hj
    have hk2 : φ.f x ∈ k.1.2.1 := k.2.2.2 hk
    obtain ⟨V, hV, l, g⟩ := hC d P (φ.f x) (j.1.2.1 ⊓ k.1.2.1) ⟨hj2, hk2⟩
    obtain ⟨V', hV', l', g'⟩ := hC d P' x (j.1.1.1 ⊓ k.1.1.1 ⊓ φ.f ⁻¹ᵁ V.1) ⟨⟨hj, hk⟩, hV⟩
    exact ⟨⟨(V', V), g', g, l'.trans inf_le_right⟩, ⟨l'.trans (inf_le_left.trans inf_le_left), l.trans inf_le_left⟩,
      ⟨l'.trans (inf_le_left.trans inf_le_right), l.trans inf_le_right⟩, hV'⟩

theorem EtaleRefine_of_push (hP : LeafPush) : LeafRefine := by
  intro hC H d P' P φ
  let S' := Sys.ref hC φ
  let G1 : S'.J ⥤ (Sys.all hC P').J := Monotone.functor (f := fun j => (⟨j.1.1, j.2.1⟩ : {V : P'.X.affineOpens // Good P' V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).1)
  let G2 : S'.J ⥤ (Sys.all hC P).J := Monotone.functor (f := fun j => (⟨j.1.2, j.2.2.1⟩ : {V : P.X.affineOpens // Good P V}))
    (fun _ _ h => (Prod.le_def.1 (Subtype.coe_le_coe.2 h)).2)
  let α1 : S'.hen H ⋙ yoneda ⟶ G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda :=
    { app := fun j => (𝟙 ((S'.hen H ⋙ yoneda).obj j) : _ ⟶ (G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).obj j)
      naturality := fun j k f => (Category.comp_id _).trans (Category.id_comp ((G1 ⋙ (Sys.all hC P').hen H ⋙ yoneda).map f)).symm }
  obtain ⟨a, ha⟩ := hP _ _ _ _ G1 α1 _ _ (𝟙 (yoneda.obj P'.X)) _ _ (S'.cocHen H) ((Sys.all hC P').cocHen H)
    (fun j => (Category.id_comp _).trans (Category.comp_id _).symm)
  have ea : a ≫ (Sys.all hC P').π H = S'.π H := by
    have := ha; rw [disc.map_id, Category.comp_id] at this; exact this
  let α2 : S'.hen H ⋙ yoneda ⟶ G2 ⋙ (Sys.all hC P).hen H ⋙ yoneda :=
    { app := fun j => yoneda.map (Spec.map (CommRingCat.ofHom
        (H.map (φ.f.appLE (j.1.2).1 (j.1.1).1 j.2.2.2).hom (idl φ j.1.2 j.1.1 j.2.2.2))))
      naturality := fun j k f => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map
        (cotangentAtUnit_tangentBijection_naturality H φ j.1.2 k.1.2 j.1.1 k.1.1 j.2.2.2 k.2.2.2 (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).2
          (Prod.le_def.1 (Subtype.coe_le_coe.2 f.le)).1)).trans (yoneda.map_comp _ _)) }
  obtain ⟨b, hb⟩ := hP _ _ _ _ G2 α2 _ _ (yoneda.map φ.f) _ _ (S'.cocHen H) ((Sys.all hC P).cocHen H)
    (fun j => (yoneda.map_comp _ _).symm.trans ((congrArg yoneda.map (henselization_spec_map_commutes_with_smooth_pair_hom H φ j.1.2 j.1.1 j.2.2.2)).trans
      (yoneda.map_comp _ _)))
  exact ⟨S', a, b, ea, hb⟩

end LateralTheory.CohomologicalPurity.TubeCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafSurjGeoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity

theorem LeafSurjGeo_of : LeafSurjGeo := by
  intro X' X Z f _ ι' ι _ hp U hU T t
  let F : Bool → Scheme.{0} := fun b => Bool.rec (pullback t f) (t ⁻¹ᵁ U).toScheme b
  let m : ∀ b, F b ⟶ T := fun b => Bool.rec (pullback.fst t f) (t ⁻¹ᵁ U).ι b
  have hR : Presieve.ofArrows F m ∈ Scheme.precoverage @Etale T := by
    refine (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr ⟨fun x => ?_, fun b => ?_⟩
    · by_cases hx : t.base x ∈ (U : Set X)
      · refine ⟨true, ?_⟩
        show x ∈ Set.range (t ⁻¹ᵁ U).ι.base
        rw [Scheme.Opens.range_ι]; exact hx
      · rw [hU, Set.notMem_compl_iff] at hx
        obtain ⟨z, hz⟩ := hx
        have hw : f.base (ι'.base z) = ι.base z := by
          rw [← Scheme.Hom.comp_apply, hp.w]; simp
        obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := f) x (ι'.base z)
          (by rw [hw, hz])
        exact ⟨false, p, hp1⟩
    · cases b <;> dsimp [m] <;> infer_instance
  refine ⟨Sieve.generate (Presieve.ofArrows F m),
    Precoverage.generate_mem_toGrothendieck hR, ?_⟩
  intro V g hg
  obtain ⟨W, h, k, hk, rfl⟩ := hg
  obtain ⟨b⟩ := hk
  cases b
  · right
    refine ⟨h ≫ pullback.snd t f, ?_⟩
    simp only [m, Category.assoc, ← pullback.condition]
  · left
    refine ⟨h ≫ (t ∣_ U), ?_⟩
    simp only [m, Category.assoc, morphismRestrict_ι]

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTailPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem pull_bij_of_iso (R : Type) [CommRing R] {E E' : Spc} (e : E ≅ E') (F : Shv R) (n : ℤ) :
    Function.Bijective (pull R e.hom F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull R e.inv F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, e.inv_hom_id, pull_id]
  · rw [← pull_comp, e.hom_inv_id, pull_id]

theorem eqv_of_iso (R : Type) [CommRing R] {E₁ E₂ E₁' E₂' : Spc} (f : E₁ ⟶ E₂) (g : E₁' ⟶ E₂')
    (e₁ : E₁ ≅ E₁') (e₂ : E₂ ≅ E₂') (w : f ≫ e₂.hom = e₁.hom ≫ g) (F : Shv R) (h : Eqv R g F) : Eqv R f F := by
  have hf : f = e₁.hom ≫ g ≫ e₂.inv := by rw [← Category.assoc, ← w, Category.assoc, e₂.hom_inv_id, Category.comp_id]
  have hE : ∀ {E E' : Spc} (u : E ⟶ E'), Eqv R u F ↔ ∀ n, Function.Bijective (pull R u F n) := fun _ => Iff.rfl
  rw [hE] at h ⊢
  intro n
  have key : pull R f F n = (pull R e₁.hom F n).comp ((pull R g F n).comp (pull R e₂.inv F n)) := by
    ext x; simp only [hf, pull_comp, AddMonoidHom.comp_apply]
  rw [key]
  exact (pull_bij_of_iso R e₁ F n).comp ((h n).comp (pull_bij_of_iso R e₂.symm F n))

def LeafTailRep : Prop := ∀ (d : ℕ) (R : Type) [CommRing R] (n : SimplexCategoryᵒᵖ),
  ∃ (A : Type) (_ : CommRing A) (I : Ideal A) (φ : R →+* A),
    I.FG ∧ ∃ (h : off (Polynomial A) (I.map Polynomial.C) ≤
        Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) ⁻¹ᵁ off A I)
      (e₁ : disc.obj ((PR (d + 1) 1 R).obj n) ≅ sch.obj (off (Polynomial A) (I.map Polynomial.C)))
      (e₂ : disc.obj ((PR d 0 R).obj n) ≅ sch.obj (off A I)),
      disc.map ((prod.map (Pj.tail d) (𝟙 _) : PR (d + 1) 1 R ⟶ PR d 0 R).app n) ≫ e₂.hom =
        e₁.hom ≫ sch.map ((Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A))).resLE _ _ h)

theorem LeafTail_of (hRep : LeafTailRep) (hH : LeafHtpy) : LeafTail := by
  intro hyp q _ d R _ hq i
  obtain ⟨hA1, -, hA3, hA4, -, -, -, -, -, hC4, -, -⟩ := hyp
  apply hA3
  intro n
  obtain ⟨A, _, I, φ, hI, h, e₁, e₂, w⟩ := hRep d R n
  have hqA : IsUnit (q : A) := by simpa using hq.map φ
  exact eqv_of_iso _ _ _ e₁ e₂ w _ (hH hA1 hA4 hC4 q A I hI hqA h i)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTauNatPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem tn_pull_cast {q : ℕ} {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E' n i) : pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_red_cast {q r : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i')
    (x : Ht q E n i) : red q r E _ _ (x.cast hn hi) = Ht.cast hn hi (red q r E _ _ x) := by
  subst hn; subst hi; rfl

theorem tn_pull_cpow (h : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hI : Inv q E')
    (x : Ht q E' 2 1) (k : ℕ) : pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_pull_cast, (h q).2.1 f hI]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_pull_cast, (h q).1, ih]

theorem tn_red_cpow (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) {E : Spc} (hI : Inv q E)
    (L : E ⟶ ofCat (glCat 1)) (k : ℕ) : red q r E _ _ (cpow q (c1 q L) k) = cpow r (c1 r L) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, tn_red_cast, ((h q r hr E).2.1 hI).1]
  | succ k ih => rw [cpow_succ, cpow_succ, tn_red_cast, (h q r hr E).1, ih, ((h q r hr E).2.1 hI).2]

theorem tn_pull_hyp (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0) :
    pull _ f _ _ (hyp q N 0 A) = hyp q N 0 B := by
  unfold hyp
  rw [(h q).2.2.1 f _ hI, hl]

theorem tn_pull_poly (h : DivisorNaturality) (q : ℕ) [NeZero q] (N : ℕ) {A B : Type} [CommRing A] [CommRing B]
    (φ : A →+* B) (f : PR N 0 B ⟶ PR N 0 A) (hI : Inv q (PR N 0 A))
    (hl : f ≫ prod.fst ≫ Pj.line N 0 = prod.fst ≫ Pj.line N 0)
    (hs : f ≫ prod.snd = prod.snd ≫ spMap φ) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    pull _ f _ _ (poly q N 0 A m n i a) = poly q N 0 B m n i (fun j => pull _ (spMap φ) _ _ (a j)) := by
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_pull_cast, (h q).1, ← pull_comp, hs, pull_comp, tn_pull_cpow h q f hI, tn_pull_hyp h q N f hI hl]

theorem tn_red_poly (h : A11) (q r : ℕ) [NeZero q] (hr : r ∣ q) (N : ℕ) {A : Type} [CommRing A]
    (hI : Inv q (PR N 0 A)) (m : ℕ) (n i : ℤ)
    (a : ∀ j : Fin m, Ht q (sp A) (n - 2 * (j : ℕ)) (i - (j : ℕ))) :
    red q r _ _ _ (poly q N 0 A m n i a) = poly r N 0 A m n i (fun j => red q r _ _ _ (a j)) := by
  unfold poly
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tn_red_cast, (h q r hr _).1, ← pull_red]
  unfold hyp
  rw [tn_red_cpow h q r hr hI]

theorem LeafTauNat_of (hG : LeafGeo) : LeafTauNat := by
  intro h6 h11 q _ d A _ hq τ hτ
  obtain ⟨a, ha⟩ := hτ
  have hI : Inv q (PR (d + 1) 0 A) := hG.2.1 q (d + 1) 0 A hq
  refine ⟨fun B _ φ g hl hs => ⟨fun j => pull _ (spMap φ) _ _ (a j), ?_⟩,
    fun r hr τ' hτ' => ⟨fun j => red q r _ _ _ (a j), ?_⟩⟩
  · have e : Hs.fgt q (pr d B) _ _ (Hs.pull q g _ _ τ) =
        pull (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) _ g.right _ _
          (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ (pull _ (dbl.map g) _ _ τ.1) =
        pull _ g.right _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [← pull_comp, ← pull_comp, inl_map]
    rw [e, ha, map_add (f := _), tn_pull_cpow h6 q (E := PR (d + 1) 0 B) (E' := PR (d + 1) 0 A) g.right hI,
      tn_pull_hyp h6 q (d + 1) g.right hI hl, tn_pull_poly h6 q (d + 1) φ g.right hI hl hs]
  · have e : Hs.fgt r (pr d A) _ _ τ' = red q r (PR (d + 1) 0 A) _ _
        (show Ht q (PR (d + 1) 0 A) _ _ from Hs.fgt q (pr d A) _ _ τ) := by
      change pull _ (dbl.inl _) _ _ τ'.1 = red q r _ _ _ (pull _ (dbl.inl _) _ _ τ.1)
      rw [hτ', pull_red]
    rw [e, ha, map_add (f := _), tn_red_poly h11 q r hr (d + 1) hI]
    unfold hyp
    rw [tn_red_cpow h11 q r hr hI]

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTauPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom

theorem cast_inj {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Function.Injective (Ht.cast (q := q) (E := E) h1 h2) := by
  subst h1; subst h2; intro a b h; exact h

theorem cast_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Ht.cast (q := q) (E := E) h1 h2 0 = 0 := by
  subst h1; subst h2; rfl

theorem cast_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n) (h4 : i' = i)
    (a : Ht q E n i) : Ht.cast h3 h4 (Ht.cast h1 h2 a) = a := by
  subst h1; subst h2; rfl

def LeafTauRes : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a,
  pull _ (pr d R).hom (tw q i) n (poly q (d + 1) 0 R m n i a) = poly q (d + 1) 1 R m n i a

def LeafTauU : Prop := LeafPB → LeafTail → Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R],
  IsUnit (q : R) → ∀ n i : ℤ, Function.Bijective (poly q (d + 1) 1 R d n i)

def LeafTauLin : Prop := ∀ (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) a b,
  poly q N k R m n i (a - b) = poly q N k R m n i a - poly q N k R m n i b

def LeafTauFgt : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] (P : Arrow Spc) (n m i j : ℤ) (a : Ht q P.right n i)
  (b : Hs q P m j), Hs.fgt q P _ _ (Hs.act q a b) = cup q a (Hs.fgt q P _ _ b)

def LeafTauTop : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (d : ℕ) (R : Type) [CommRing R] (n i : ℤ) (x : Ht q (sp R) n i)
  (a : ∀ j : Fin d, Ht q (sp R) (2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) ((d : ℤ) - ((j : ℕ) : ℤ))),
  ∃ e : ∀ j : Fin (d + 1), Ht q (sp R) (n + 2 * (d : ℤ) - 2 * ((j : ℕ) : ℤ)) (i + (d : ℤ) - ((j : ℕ) : ℤ)),
    e (Fin.last d) = x.cast (by simp) (by simp) ∧
    cup q (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _ x)
      (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d a) =
      poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) e

theorem cast_sub {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a b : Ht q E n i) :
    Ht.cast h1 h2 (a - b) = Ht.cast h1 h2 a - Ht.cast h1 h2 b := by
  subst h1; subst h2; rfl

theorem tauLin : LeafTauLin := by
  intro q N k R _ m n i a b
  unfold poly
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.sub_apply, map_sub, map_sub, AddMonoidHom.sub_apply, cast_sub]

theorem tauFgt : LeafTauFgt := by
  intro h q _ P n m i j a b
  have hb : pull _ (dbl.inr P) (tw q j) m b.1 = 0 := b.2
  change pull _ (dbl.inl P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1 - pull _ (dbl.fold P) _ _
    (pull _ (dbl.inr P) _ _ (cup q (pull _ (dbl.fold P) _ n a) b.1))) = cup q a (pull _ (dbl.inl P) _ _ b.1)
  rw [map_sub, (h q).1, (h q).1, hb, map_zero, map_zero, map_zero, sub_zero, ← pull_comp, inl_fold, pull_id]

theorem poly_zero (hL : LeafTauLin) (q N k : ℕ) (R : Type) [CommRing R] (m : ℕ) (n i : ℤ) :
    poly q N k R m n i 0 = 0 := by
  have h := hL q N k R m n i 0 0
  rw [sub_zero, sub_self] at h
  exact h

theorem LeafTau_of (hBd : LeafBd) (hG : LeafGeo) (hPB : LeafPB) (hTl : LeafTail) (hR : LeafTauRes)
    (hU : LeafTauU) (hL : LeafTauLin) (hF : LeafTauFgt) (hT : LeafTauTop) : LeafTau := by
  intro H q _ d R _ hq
  obtain ⟨δ, hδ, -, -⟩ := hBd
  have hm : Mono (pr d R).hom := hG.1 d R
  have h6 : DivisorNaturality := H.2.2.2.2.1
  have hUb := hU hPB hTl H q d R hq
  have hPB' := hPB H.1 h6 H.2.2.2.2.2.2.2.2.2.2.1 q (d + 1) R hq
  have hpoly0 := poly_zero hL
  have hres0 : ∀ n i (σ : Hs q (pr d R) n i), pull _ (pr d R).hom (tw q i) n (Hs.fgt q _ n i σ) = 0 :=
    fun n i σ => ((hδ q _ hm n i).1 _).2 ⟨σ, rfl⟩
  have hinj : ∀ n i, Function.Injective (Hs.fgt q (pr d R) n i) := by
    intro N i
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by ring⟩
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro σ hσ
    obtain ⟨u, rfl⟩ := ((hδ q _ hm n i).2.2 σ).1 hσ
    obtain ⟨a, ha⟩ := (hUb n i).2 u
    exact ((hδ q _ hm n i).2.1 u).2 ⟨poly q (d + 1) 0 R d n i a, (hR H q d R d n i a).trans ha⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := (hUb (2 * d) d).2 (pull _ (pr d R).hom (tw q d) _ (cpow q (hyp q (d + 1) 0 R) d))
    have hy : pull _ (pr d R).hom (tw q d) _
        (cpow q (hyp q (d + 1) 0 R) d + poly q (d + 1) 0 R d (2 * d) d (0 - b)) = 0 := by
      refine (map_add _ _ _).trans ?_
      rw [hR H q d R d (2 * d) d (0 - b), hL, hpoly0, zero_sub, ← hb]
      exact add_neg_cancel _
    obtain ⟨τ, hτ⟩ := ((hδ q _ hm _ _).1 _).1 hy
    refine ⟨τ, ⟨0 - b, hτ⟩, ?_⟩
    rintro τ' ⟨a', ha'⟩
    have e1 := hres0 _ _ τ'
    rw [ha'] at e1
    have e2 := (map_add (pull _ (pr d R).hom (tw q d) (2 * d)) _ _).symm.trans e1
    rw [hR H q d R d (2 * d) d a'] at e2
    have hab : a' = 0 - b := (hUb _ _).1 (by
      rw [hL, hpoly0, zero_sub, hb]
      exact eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans e2))
    apply hinj
    rw [ha', hτ, hab]
  · rintro τ ⟨a, ha⟩ n i
    constructor
    · intro x y hxy
      obtain ⟨ex, hex, hex'⟩ := hT H q d R n i x a
      obtain ⟨ey, hey, hey'⟩ := hT H q d R n i y a
      have h1 := congrArg (Hs.fgt q (pr d R) (n + 2 * d) (i + d)) hxy
      dsimp only at h1
      have fx := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n x) τ
      have fy := hF h6 q (pr d R) n (2 * d) i d (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n y) τ
      rw [ha] at fx fy
      replace h1 := hex'.symm.trans (fx.symm.trans (h1.trans (fy.trans hey')))
      have h2 := congrFun ((hPB' _ _).1 h1) (Fin.last d)
      rw [hex, hey] at h2
      exact cast_inj _ _ h2
    · intro σ
      obtain ⟨c, hc⟩ := (hPB' (n + 2 * d) (i + d)).2 (Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
      have k1 : n + 2 * (d : ℤ) - 2 * (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = n := by
        simp only [Fin.val_last]; ring
      have k2 : i + (d : ℤ) - (((Fin.last d : Fin (d + 1)) : ℕ) : ℤ) = i := by
        simp only [Fin.val_last]; ring
      refine ⟨Ht.cast k1 k2 (c (Fin.last d)), ?_⟩
      obtain ⟨e, he, he'⟩ := hT H q d R n i (Ht.cast k1 k2 (c (Fin.last d))) a
      have hlast : (e - c) (Fin.last d) = 0 := by
        rw [Pi.sub_apply, he, cast_cast, sub_self]
      have hsnoc : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          poly q (d + 1) 0 R d (n + 2 * d) (i + d) (fun j : Fin d => (e - c) j.castSucc) := by
        unfold poly
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [map_zero, AddMonoidHom.zero_apply, cast_zero, add_zero]
        rfl
      have hd : poly q (d + 1) 0 R (d + 1) (n + 2 * d) (i + d) (e - c) =
          Hs.fgt q (pr d R) (n + 2 * d) (i + d) (Hs.act q (P := pr d R) (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) _ _
            (Ht.cast k1 k2 (c (Fin.last d)))) τ - σ) := by
        have hfx := hF h6 q (pr d R) n (2 * d) i d
          (pull _ (prod.snd : PR (d + 1) 0 R ⟶ sp R) (tw q i) n (Ht.cast k1 k2 (c (Fin.last d)))) τ
        rw [ha] at hfx
        rw [hL, map_sub, hc]
        exact congrArg (fun t : Ht q (pr d R).right (n + 2 * d) (i + d) => t - Hs.fgt q (pr d R) (n + 2 * d) (i + d) σ)
          (he'.symm.trans hfx.symm)
      have hg : (fun j : Fin d => (e - c) j.castSucc) = 0 := (hUb _ _).1 (by
        rw [hpoly0, ← hR H, ← hsnoc, hd]
        exact hres0 _ _ _)
      rw [hg, hpoly0] at hsnoc
      rw [hsnoc] at hd
      replace hd := hd.symm
      rw [map_sub] at hd
      exact hinj _ _ (sub_eq_zero.mp hd)

end LateralTheory.CohomologicalPurity.Thom
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafTopPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_sheaf_sections_restrict_restrict_eq_restrict_comp {R : Type} [CommRing R] {F : Shv R} {Y Z W : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ W) (a : Sec F W) :
    Sec.res f (Sec.res g a) = Sec.res (f ≫ g) a := by
  show (F.obj.map f.op).hom ((F.obj.map g.op).hom a) = (F.obj.map (f ≫ g).op).hom a
  rw [op_comp, Functor.map_comp]; rfl

theorem etale_sheaf_sections_restriction_of_zero_eq_zero {R : Type} [CommRing R] {F : Shv R} {Y Z : Scheme.{0}} (f : Y ⟶ Z) :
    Sec.res f (0 : Sec F Z) = 0 := by
  show (F.obj.map f.op).hom 0 = 0
  exact map_zero _

theorem etale_sheaf_sections_map_restrict_comm {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {Y Z : Scheme.{0}} (f : Y ⟶ Z) (a : Sec F Z) :
    Sec.map φ (Sec.res f a) = Sec.res f (Sec.map φ a) := by
  show (φ.hom.app (op Y)).hom ((F.obj.map f.op).hom a) = (G.obj.map f.op).hom ((φ.hom.app (op Z)).hom a)
  have h := φ.hom.naturality f.op
  exact congrArg (fun ψ => ψ.hom a) h

theorem LeafTop_of : LeafTop := by
  intro R _ K X U n c' hc'
  obtain ⟨h1, h2⟩ := (mem_Zc c').1 hc'
  refine ⟨Sec.res X.topIso.inv c', (mem_Zc _).2 ⟨?_, ?_⟩, ?_⟩
  · have : IsIso (⊤ : X.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
    have e : U.ι ≫ X.topIso.inv = inv ((⊤ : X.Opens).ι ∣_ U) ≫ ((⊤ : X.Opens).ι ⁻¹ᵁ U).ι := by
      rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
        Scheme.topIso_hom, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp, e, ← etale_sheaf_sections_restrict_restrict_eq_restrict_comp, h1, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · rw [etale_sheaf_sections_map_restrict_comm, h2, etale_sheaf_sections_restriction_of_zero_eq_zero]
  · intro V
    rw [etale_sheaf_sections_restrict_restrict_eq_restrict_comp]
    congr 1
    rw [← cancel_mono X.topIso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Scheme.topIso_hom,
      Scheme.homOfLE_ι]

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

