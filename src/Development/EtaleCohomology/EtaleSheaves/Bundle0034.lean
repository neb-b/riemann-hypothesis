module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0010

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.longPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.longPf
open LateralTheory.E.CxDescPf

def LES : Prop := ∀ (R : Type) [CommRing R] (I : Cx R), (∀ n, Injective (I.X n)) → ∃ d : ∀ (S : ShortComplex (Cx R)), S.ShortExact → ∀ n : ℤ, CohomologyClass S.X₁ I n →+ CohomologyClass S.X₃ I (n + 1), (∀ (S : ShortComplex (Cx R)) (hS : S.ShortExact) n, Function.Exact (cpull S.g I n) (cpull S.f I n) ∧ Function.Exact (cpull S.f I n) (d S hS n) ∧ Function.Exact (d S hS n) (cpull S.g I (n + 1))) ∧ ∀ (S S' : ShortComplex (Cx R)) (hS : S.ShortExact) (hS' : S'.ShortExact) (φ : S ⟶ S') n x, cpull φ.τ₃ I (n + 1) (d S' hS' n x) = d S hS n (cpull φ.τ₁ I n x)

theorem four_inj {A B C D A' B' C' D' : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D']
    (α : A →+ B) (β : B →+ C) (γ : C →+ D) (α' : A' →+ B') (β' : B' →+ C') (γ' : C' →+ D')
    (a : A →+ A') (b : B →+ B') (c : C →+ C') (d : D →+ D')
    (h2 : Function.Exact α β) (h2' : Function.Exact α' β') (h3 : Function.Exact β γ)
    (s1 : ∀ x, b (α x) = α' (a x)) (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x))
    (ha : Function.Surjective a) (hb : Function.Injective b) (hd : Function.Injective d) : Function.Injective c := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have : γ x = 0 := hd (by rw [s3, hx, map_zero, map_zero])
  obtain ⟨y, rfl⟩ := (h3 x).1 this
  have : β' (b y) = 0 := by rw [← s2]; exact hx
  obtain ⟨z', hz'⟩ := (h2' (b y)).1 this
  obtain ⟨z, rfl⟩ := ha z'
  have : α z = y := hb (by rw [s1, hz'])
  rw [← this]; exact h2.apply_apply_eq_zero z

theorem four_surj {B C D E B' C' D' E' : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
    [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D'] [AddCommGroup E']
    (β : B →+ C) (γ : C →+ D) (δ : D →+ E) (β' : B' →+ C') (γ' : C' →+ D') (δ' : D' →+ E')
    (b : B →+ B') (c : C →+ C') (d : D →+ D') (e : E →+ E')
    (h2' : Function.Exact β' γ') (h3 : Function.Exact γ δ) (h3' : Function.Exact γ' δ')
    (s2 : ∀ x, c (β x) = β' (b x)) (s3 : ∀ x, d (γ x) = γ' (c x)) (s4 : ∀ x, e (δ x) = δ' (d x))
    (hb : Function.Surjective b) (hd : Function.Surjective d) (he : Function.Injective e) : Function.Surjective c := by
  intro x'
  obtain ⟨y, hy⟩ := hd (γ' x')
  have : δ y = 0 := he (by rw [s4, hy, map_zero, h3'.apply_apply_eq_zero])
  obtain ⟨w, rfl⟩ := (h3 y).1 this
  have : γ' (x' - c w) = 0 := by rw [map_sub, ← s3, hy, sub_self]
  obtain ⟨u', hu'⟩ := (h2' _).1 this
  obtain ⟨u, rfl⟩ := hb u'
  exact ⟨w + β u, by rw [map_add (f := _), s2, hu', add_sub_cancel]⟩

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) (x) :
    cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_sq {R : Type} [CommRing R] {A B C D : Cx R} (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C) (g' : C ⟶ D)
    (w : f ≫ g = f' ≫ g') (I : Cx R) (n : ℤ) (x) :
    cpull f I n (cpull g I n x) = cpull f' I n (cpull g' I n x) := by
  rw [← cpull_comp, ← cpull_comp, w]

def Ses : Prop := ∀ (R : Type) [CommRing R] (N : ℕ), ∃ (i : ∀ K : Cx R, tr K N ⟶ tr K (N + 1))
  (p : ∀ K : Cx R, tr K (N + 1) ⟶ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).obj (K.X (-((N + 1 : ℕ) : ℤ))))
  (w : ∀ K, i K ≫ p K = 0), (∀ K, (ShortComplex.mk (i K) (p K) (w K)).ShortExact) ∧
  ∀ {K L : Cx R} (g : K ⟶ L), i K ≫ trm g (N + 1) = trm g N ≫ i L ∧
    p K ≫ (CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ))) = trm g (N + 1) ≫ p L

theorem long_of (hLES : LES) (hSes : Ses) : LateralTheory.E.CxDescPf.long := by
  intro R _ I _ hI K L _ _ g m N h3 h1
  obtain ⟨d, hex, hnat⟩ := hLES R I hI
  obtain ⟨i, p, w, hse, hn⟩ := hSes R N
  let MainNotions := ShortComplex.mk (i K) (p K) (w K)
  let SL := ShortComplex.mk (i L) (p L) (w L)
  let φ : MainNotions ⟶ SL := ShortComplex.Hom.mk (trm g N) (trm g (N + 1))
    ((CochainComplex.singleFunctor (Shv R) (-((N + 1 : ℕ) : ℤ))).map (g.f (-((N + 1 : ℕ) : ℤ)))) (hn g).1.symm (hn g).2.symm
  have sf : ∀ j x, cpull φ.τ₁ I j (cpull SL.f I j x) = cpull MainNotions.f I j (cpull φ.τ₂ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₁₂ I j x
  have sg : ∀ j x, cpull φ.τ₂ I j (cpull SL.g I j x) = cpull MainNotions.g I j (cpull φ.τ₃ I j x) :=
    fun j x => cpull_sq _ _ _ _ φ.comm₂₃ I j x
  have inj : ∀ n : ℤ, n + 1 ≤ m → Function.Injective (cpull φ.τ₂ I (n + 1)) := by
    intro n hn
    refine four_inj (d SL (hse L) n) (cpull SL.g I (n + 1)) (cpull SL.f I (n + 1))
      (d MainNotions (hse K) n) (cpull MainNotions.g I (n + 1)) (cpull MainNotions.f I (n + 1))
      (cpull φ.τ₁ I n) (cpull φ.τ₃ I (n + 1)) (cpull φ.τ₂ I (n + 1)) (cpull φ.τ₁ I (n + 1))
      (hex SL (hse L) n).2.2 (hex MainNotions (hse K) n).2.2 (hex SL (hse L) (n + 1)).1
      (fun x => hnat MainNotions SL (hse K) (hse L) φ n x) (sg (n + 1)) (sf (n + 1))
      (h1.1 n (by omega)).2 ?_ ?_
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h3.1 _ h).1
      · rw [h]; exact h3.2
    · rcases lt_or_eq_of_le hn with h | h
      · exact (h1.1 _ h).1
      · rw [h]; exact h1.2
  have surj : ∀ j : ℤ, j < m → Function.Surjective (cpull φ.τ₂ I j) := by
    intro j hj
    refine four_surj (cpull SL.g I j) (cpull SL.f I j) (d SL (hse L) j)
      (cpull MainNotions.g I j) (cpull MainNotions.f I j) (d MainNotions (hse K) j)
      (cpull φ.τ₃ I j) (cpull φ.τ₂ I j) (cpull φ.τ₁ I j) (cpull φ.τ₃ I (j + 1))
      (hex MainNotions (hse K) j).1 (hex SL (hse L) j).2.1 (hex MainNotions (hse K) j).2.1
      (sg j) (sf j) (fun x => hnat MainNotions SL (hse K) (hse L) φ j x)
      (h3.1 j hj).2 (h1.1 j hj).2 ?_
    rcases lt_or_eq_of_le (show j + 1 ≤ m by omega) with h | h
    · exact (h3.1 _ h).1
    · rw [h]; exact h3.2
  have inj' : ∀ j : ℤ, j ≤ m → Function.Injective (cpull φ.τ₂ I j) := by
    intro j hj
    have := inj (j - 1) (by omega)
    rwa [sub_add_cancel] at this
  exact ⟨fun j hj => ⟨inj' j hj.le, surj j hj⟩, inj' m le_rfl⟩

end LateralTheory.E.longPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.shiftPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.shiftPf

theorem conj_iff {α β γ δ : Type*} (F : α → β) (G : γ → δ) (e1 : α ≃ γ) (e2 : β ≃ δ)
    (h : ∀ x, G (e1 x) = e2 (F x)) :
    (Function.Bijective F ↔ Function.Bijective G) ∧ (Function.Injective F ↔ Function.Injective G) := by
  have hG : G = e2 ∘ F ∘ e1.symm := funext fun y => by simpa using h (e1.symm y)
  have hF : F = e2.symm ∘ G ∘ e1 := funext fun x => by simp [h]
  refine ⟨⟨fun hb => ?_, fun hb => ?_⟩, ⟨fun hb => ?_, fun hb => ?_⟩⟩
  · rw [hG]; exact e2.bijective.comp (hb.comp e1.symm.bijective)
  · rw [hF]; exact e2.symm.bijective.comp (hb.comp e1.bijective)
  · rw [hG]; exact e2.injective.comp (hb.comp e1.symm.injective)
  · rw [hF]; exact e2.symm.injective.comp (hb.comp e1.injective)

section Cat
variable {C : Type*} [Category C]

abbrev pre {X X' : C} (u : X ⟶ X') (Y : C) : (X' ⟶ Y) → (X ⟶ Y) := fun h => u ≫ h

theorem pre_conj {W W' X X' : C} (u' : W ⟶ W') (u : X ⟶ X') (a : W ≅ X) (b : W' ≅ X')
    (h : u' ≫ b.hom = a.hom ≫ u) (Y : C) :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u' Y)) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u' Y)) :=
  conj_iff _ _ ((Iso.homCongr b.symm (Iso.refl Y))) ((Iso.homCongr a.symm (Iso.refl Y))) (fun x => by
    simp only [pre, Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id]
    rw [← Category.assoc, h, Category.assoc])

theorem pre_target {X X' Y Y' : C} (u : X ⟶ X') (e : Y ≅ Y') :
    (Function.Bijective (pre u Y) ↔ Function.Bijective (pre u Y')) ∧
      (Function.Injective (pre u Y) ↔ Function.Injective (pre u Y')) :=
  conj_iff _ _ (Iso.homCongr (Iso.refl X') e) (Iso.homCongr (Iso.refl X) e) (fun x => by
    simp [pre, Iso.homCongr_apply])

theorem pre_shift [HasShift C ℤ] {X X' : C} (u : X ⟶ X') (p : ℤ) (Y : C) :
    (Function.Bijective (pre (u⟦p⟧') Y) ↔ Function.Bijective (pre u (Y⟦-p⟧))) ∧
      (Function.Injective (pre (u⟦p⟧') Y) ↔ Function.Injective (pre u (Y⟦-p⟧))) :=
  conj_iff _ _ ((shiftEquiv C p).toAdjunction.homEquiv X' Y) ((shiftEquiv C p).toAdjunction.homEquiv X Y) (fun x => by
    simp only [pre]
    exact ((shiftEquiv C p).toAdjunction.homEquiv_naturality_left u x).symm)

end Cat

variable {R : Type} [CommRing R]

abbrev Qt (R : Type) [CommRing R] := HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)

theorem toHom_cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) (x : CohomologyClass L I n) :
    CohomologyClass.toHom (cpull f I n x) = (Qt R).map f ≫ CohomologyClass.toHom x := by
  obtain ⟨b, rfl⟩ := x.mk_surjective
  rw [cpull, cpre_mk, CohomologyClass.toHom_mk, CohomologyClass.toHom_mk, ← Functor.map_comp,
    ← Cocycle.equivHomShift_symm_precomp]
  congr 2

theorem cpull_iff {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) :
    (Function.Bijective (cpull f I n) ↔ Function.Bijective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) ∧
      (Function.Injective (cpull f I n) ↔ Function.Injective (pre ((Qt R).map f) ((Qt R).obj (I⟦n⟧)))) :=
  conj_iff _ _ (CohomologyClass.homAddEquiv (K := L) (L := I) (n := n)).toEquiv
    (CohomologyClass.homAddEquiv (K := K) (L := I) (n := n)).toEquiv (fun x => by
      simp [toHom_cpull])

theorem main_iff (I : Cx R) {A B : Shv R} (φ : A ⟶ B) (P j : ℤ) :
    (Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) ∧
    (Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map φ) I (j - P)) ↔
      Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) (-P)).map φ) I j)) := by
  let s0 := (CochainComplex.singleFunctor (Shv R) 0).map φ
  let sp := (CochainComplex.singleFunctor (Shv R) (-P)).map φ
  let E := (CochainComplex.singleFunctors (Shv R)).shiftIso P (-P) 0 (by omega)
  obtain ⟨b1, i1⟩ := cpull_iff sp I j
  obtain ⟨b2, i2⟩ := pre_conj ((Qt R).map sp) ((Qt R).map (s0⟦P⟧'))
    ((Qt R).mapIso (E.symm.app A)) ((Qt R).mapIso (E.symm.app B)) (by
      simp only [Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, ← Functor.map_comp]
      congr 1
      exact E.inv.naturality φ) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b3, i3⟩ := pre_conj ((Qt R).map (s0⟦P⟧')) (((Qt R).map s0)⟦P⟧')
    (((Qt R).commShiftIso P).app _) (((Qt R).commShiftIso P).app _)
    (((Qt R).commShiftIso P).hom.naturality s0) ((Qt R).obj (I⟦j⟧))
  obtain ⟨b4, i4⟩ := pre_shift ((Qt R).map s0) P ((Qt R).obj (I⟦j⟧))
  obtain ⟨b5, i5⟩ := pre_target ((Qt R).map s0)
    ((((Qt R).commShiftIso (-P)).symm.app (I⟦j⟧)) ≪≫
      (Qt R).mapIso ((shiftFunctorAdd' (Cx R) j (-P) (j - P) (by omega)).symm.app I))
  obtain ⟨b6, i6⟩ := cpull_iff s0 I (j - P)
  exact ⟨b6.trans (b5.symm.trans (b4.symm.trans (b3.trans (b2.trans b1.symm)))),
    i6.trans (i5.symm.trans (i4.symm.trans (i3.trans (i2.trans i1.symm))))⟩

theorem shift_of : LateralTheory.E.CxDescPf.shift := by
  intro R _ I A B φ p j
  obtain ⟨hb, hi⟩ := main_iff I φ (p : ℤ) j
  exact ⟨hb.1, hi.1⟩

end LateralTheory.E.shiftPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.stupidPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex LateralTheory.E.CxDescPf

namespace LateralTheory.E.stupidPf

theorem cpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ)
    (x : CohomologyClass M I n) : cpull (f ≫ g) I n x = cpull f I n (cpull g I n x) := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe, Cochain.ofHom_comp]
  rw [Cochain.comp_assoc_of_first_is_zero_cochain]

theorem cpull_id {R : Type} [CommRing R] (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) :
    cpull (𝟙 K) I n x = x := by
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  apply Cocycle.ext
  simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
  exact Cochain.id_comp _

theorem cpull_iso {R : Type} [CommRing R] {K L : Cx R} (e : K ≅ L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨cpull e.inv I n, fun x => ?_, fun x => ?_⟩
  · rw [← cpull_comp, e.inv_hom_id, cpull_id]
  · rw [← cpull_comp, e.hom_inv_id, cpull_id]

def trunc0 : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L),
  ∃ (eK : tr K 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (K.X (-((0 : ℕ) : ℤ))))
    (eL : tr L 0 ≅ (CochainComplex.singleFunctor (Shv R) 0).obj (L.X (-((0 : ℕ) : ℤ)))),
    trm g 0 ≫ eL.hom = eK.hom ≫ (CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))

def incl : Prop := ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0] {K L : Cx R} (g : K ⟶ L) (N : ℕ),
  ∃ (ιK : tr K N ⟶ K) (ιL : tr L N ⟶ L), trm g N ≫ ιL = ιK ≫ g ∧
    ∀ n : ℤ, n + 1 ≤ (N : ℤ) → Function.Bijective (cpull ιK I n) ∧ Function.Bijective (cpull ιL I n)

theorem stupid_of (h0 : trunc0) (hI : incl) : LateralTheory.E.CxDescPf.stupid := by
  intro R _ I _ _ K L _ _ g
  refine ⟨fun hb j => ?_, fun m N hN hG => ?_⟩
  · obtain ⟨eK, eL, hsq⟩ := h0 R g
    have hc : (cpull (trm g 0) I j) ∘ (cpull eL.hom I j) =
        (cpull eK.hom I j) ∘ (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f (-((0 : ℕ) : ℤ)))) I j) := by
      funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    have hb' : Function.Bijective ((cpull (trm g 0) I j) ∘ (cpull eL.hom I j)) := by
      rw [hc]; exact (cpull_iso eK I j).comp (hb j)
    exact (Function.Bijective.of_comp_iff _ (cpull_iso eL I j)).1 hb'
  · obtain ⟨ιK, ιL, hsq, hbij⟩ := hI R I g N
    have hc : ∀ j, (cpull ιK I j) ∘ (cpull g I j) = (cpull (trm g N) I j) ∘ (cpull ιL I j) := by
      intro j; funext x; simp only [Function.comp_apply, ← cpull_comp, hsq]
    refine ⟨fun j hj => ?_, ?_⟩
    · have hb' : Function.Bijective ((cpull ιK I j) ∘ (cpull g I j)) := by
        rw [hc]; exact (hG.1 j hj).comp (hbij j (by omega)).2
      exact (Function.Bijective.of_comp_iff' (hbij j (by omega)).1 _).1 hb'
    · have hi : Function.Injective ((cpull ιK I m) ∘ (cpull g I m)) := by
        rw [hc]; exact hG.2.comp (hbij m hN).2.1
      exact Function.Injective.of_comp hi

end LateralTheory.E.stupidPf
end
end

