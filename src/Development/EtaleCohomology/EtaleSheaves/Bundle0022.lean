module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0017
public import Development.EtaleCohomology.EtaleSheaves.Bundle0009
public import Development.EtaleCohomology.TateTwists.Bundle0015
public import Development.EtaleCohomology.EtaleSheaves.Bundle0019
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014
public import Development.EtaleCohomology.EtaleSheaves.Bundle0020

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartSurjCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartSurjCut

def Root : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  AICSch Z → IsUnit (q : A) → Nonempty (Prim q Γ(Z, ⊤))

def LCIso : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (S : Scheme.{0}) (ζ : Prim q Γ(S, ⊤)),
  ∃ e : ∀ (X : Scheme.{0}) (s : X ⟶ S), LocallyConstant X (ZMod q) ≃+ Ht q (sch.obj X) 0 i,
    ∀ {X Y : Scheme.{0}} (s : X ⟶ S) (t : Y ⟶ S) (f : Y ⟶ X), f ≫ s = t → ∀ g : LocallyConstant X (ZMod q),
      pull _ (sch.map f) (tw q i) 0 (e X s g) = e Y t (g.comap f.base.hom)

end LateralTheory.E.ChartSurjCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassExistence

def LeafEvMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LeafEvDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleKummerChernEdgeValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 1 U → Sec ((res _ (tw q 1)).X 1) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 1 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      a U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def EtaleKummerChernTriangleValuesExistNatural : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ a : ∀ U : Scheme.{0}, Sx E 2 U → Sec ((res _ (tw q 1)).X 0) U,
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U), Sec.res g (a U x) = a V (x.res g)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      a U x = kumT q U v + kumT q U w - kumT q U (v * w)

def EtaleKummerChernCochainCoboundaryVanishesOnEdges : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (δ 2 3 α) 1 2 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTriangles : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev (δ 2 3 α) 2 1 (by simp) U x = 0

def EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α →
  ∀ (U : Scheme.{0}) (x : Sx E 3 U), ev (δ 2 3 α) 3 0 (by simp) U x = 0

theorem cx_ext_pf : LateralTheory.EtaleFoundations.cx_ext := by
  intro R _ E I n α h
  apply LateralTheory.E.ChernCocycleExistenceAndUniqueness.cochain_ext_ev α 0
  intro p s hs U x
  rw [h]
  simp [ev]

theorem res_neg_pf : LateralTheory.EtaleFoundations.res_neg := by
  intro q s hs U a
  exact LateralTheory.EtaleFoundations.FirstChernUniqueness.sec_sub (LateralTheory.EtaleFoundations.FirstChernUniqueness.res_zero_neg q s hs) U a 0

theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : LeafEvMk) (hd : LeafEvDelta) (h1 : EtaleKummerChernEdgeValuesExistNatural) (h2 : EtaleKummerChernTriangleValuesExistNatural)
    (c1 : EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) : LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists := by
  intro q _ E L hi
  exact LateralTheory.EtaleFoundations.exists_closed_etale_kummer_chern_class_cochain_of_values hmk h1 h2 (LateralTheory.EtaleFoundations.etale_first_chern_cochain_closed_of_components hd cx_ext_pf res_neg_pf c1 c2 c3) q L hi

end LateralTheory.E.ChernClassExistence
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChowLCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowLCut

inductive IterLine {S : Scheme.{0}} : ∀ {Y : Scheme.{0}}, (Y ⟶ S) → Prop
  | iso {Y : Scheme.{0}} (e : Y ⟶ S) : IsIso e → IterLine e
  | comp {Y T : Scheme.{0}} (l : Y ⟶ T) (k : T ⟶ S) : IsLine l → IterLine k → IterLine (l ≫ k)

theorem IT_of_iterLine {S Y : Scheme.{0}} {k : Y ⟶ S} (hk : IterLine k) :
    ∀ {X : Scheme.{0}} (u : X ⟶ Y), IsIntegralHom u → IT (u ≫ k) := by
  induction hk with
  | iso e he => intro X u hu; exact IT.int _ (by infer_instance)
  | comp l k hl _ ih =>
    intro X u hu
    refine IT.step (u ≫ l) k _ ?_ ⟨_, u, l, hu, hl, rfl⟩ (Category.assoc _ _ _)
    simpa using ih (𝟙 _) inferInstance

def LineEx : Prop := ∀ S : Scheme.{0}, ∃ (L : Scheme.{0}) (l : L ⟶ S), IsLine l

def IterBC : Prop := ∀ {P S X : Scheme.{0}} (q : P ⟶ S) (g : X ⟶ S), IterLine q → IterLine (pullback.fst g q)

def ChowGraph : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q)
    (U : X₁.Opens) (s : U.toScheme ⟶ X'), IterLine q ∧ IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧
    (U : Set X₁).Nonempty ∧ s ≫ i ≫ pullback.fst p₁ q = U.ι

theorem goal_of (hB : IterBC) (hG : ChowGraph) : LateralTheory.E.ChowCut.ChowL := by
  intro A _ X₁ p₁ _ hX₁
  obtain ⟨P, q, X', i, U, s, hq, hi, his, hU, hs⟩ := hG A p₁ hX₁
  refine ⟨X', i ≫ pullback.fst p₁ q, U, s, hU, hs, IT_of_iterLine (hB q p₁ hq) i inferInstance, ?_⟩
  have e : (i ≫ pullback.fst p₁ q) ≫ p₁ = (i ≫ pullback.snd p₁ q) ≫ q := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  rw [e]
  exact IT_of_iterLine hq _ inferInstance

end LateralTheory.E.ChowLCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CompPf
section
noncomputable section
open CategoryTheory Limits Polynomial

namespace LateralTheory.E.CompPf
open LateralTheory.E.t_E3Cut

section
variable {R D : Type} [CommRing R] [CommRing D] (h : R →+* D)

theorem eval_map_rr (p : R[X]) (x : D) :
    (p.map h.rangeRestrict).eval₂ h.range.subtype x = p.eval₂ h x := by
  rw [eval₂_map]; rfl

theorem alg_of (x : D) (p : R[X]) (n : ℕ) (hn : h (p.coeff n) ≠ 0) (hp : p.eval₂ h x = 0) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  refine ⟨p.map h.rangeRestrict, ?_, ?_⟩
  · intro h0
    apply hn
    have h1 := congrArg (fun q => ((q.coeff n : h.range) : D)) h0
    simpa using h1
  · rw [aeval_def]; exact (eval_map_rr h p x).trans hp

theorem of_alg (x : D) :
    letI : Algebra h.range D := h.range.subtype.toAlgebra;
    IsAlgebraic h.range x → ∃ p : R[X], (∃ n, h (p.coeff n) ≠ 0) ∧ p.eval₂ h x = 0 := by
  letI : Algebra h.range D := h.range.subtype.toAlgebra
  rintro ⟨q, hq0, hq⟩
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective h.rangeRestrict h.rangeRestrict_surjective q
  refine ⟨p, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    apply hq0
    ext n
    simp only [coeff_map, coeff_zero]
    simpa using hc n
  · rw [aeval_def] at hq; exact (eval_map_rr h p x).symm.trans hq
end

theorem Comp_of : LateralTheory.E.AlgResPropsPf.Comp := by
  intro A B C f g hf hg Q hQ c
  haveI := hQ
  let gB : B →+* C ⧸ Q := (Ideal.Quotient.mk Q).comp g.hom
  let fA : A →+* C ⧸ Q := gB.comp f.hom
  have hle : fA.range ≤ gB.range := by rintro _ ⟨a, rfl⟩; exact ⟨f.hom a, rfl⟩
  letI : Algebra fA.range (C ⧸ Q) := fA.range.subtype.toAlgebra
  letI : Algebra gB.range (C ⧸ Q) := gB.range.subtype.toAlgebra
  letI : Algebra fA.range gB.range := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower fA.range gB.range (C ⧸ Q) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI h1 : Algebra.IsAlgebraic fA.range gB.range := ⟨by
    rintro ⟨_, b, rfl⟩
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hf (Q.comap g.hom) (hQ.comap _) b
    have hb := alg_of fA (gB b) p n (by
        intro h0; apply hn; rw [Ideal.mem_comap]; exact Ideal.Quotient.eq_zero_iff_mem.mp h0)
      (by
        have h5 : (Ideal.Quotient.mk Q) (g.hom (p.eval₂ f.hom b)) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂, hom_eval₂] at h5; exact h5)
    exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom fA.range gB.range (C ⧸ Q)) Subtype.val_injective).mp hb⟩
  haveI h2 : Algebra.IsAlgebraic gB.range (C ⧸ Q) := ⟨by
    intro x
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, ⟨n, hn⟩, hp⟩ := hg Q hQ c'
    exact alg_of gB _ p n (fun h0 => hn (Ideal.Quotient.eq_zero_iff_mem.mp h0))
      (by
        have h5 : (Ideal.Quotient.mk Q) (p.eval₂ g.hom c') = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
        rw [hom_eval₂] at h5; exact h5)⟩
  have h3 := (Algebra.IsAlgebraic.trans fA.range gB.range (C ⧸ Q)).1 (Ideal.Quotient.mk Q c)
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := of_alg fA _ h3
  refine ⟨p, ⟨n, fun hm => hn (Ideal.Quotient.eq_zero_iff_mem.mpr hm)⟩, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [hom_eval₂]; exact hp

end LateralTheory.E.CompPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContAffPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContAffPf

lemma isoSpec_inv_nat {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

lemma pp {R : Type} [CommRing R] {A B C E : Spc} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E) (h : a ≫ b = c ≫ d)
    (F : Shv R) (n : ℤ) (x : H R E F n) : pull R a F n (pull R b F n x) = pull R c F n (pull R d F n x) := by
  rw [← pull_comp, h, pull_comp]

theorem aff_case (hB1 : B1) (q : ℕ) {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) (ha : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)) (hcs : ∀ j, CompactSpace (D.obj j))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (hu : ∀ j, IsUnit (q : Γ(D.obj j, ⊤)))
    (hA : ∀ j, IsAffine (D.obj j)) (hP : IsAffine c.pt) (n i : ℤ) :
    (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
    ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0 := by
  obtain ⟨hE⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j) := fun _ => hP
  have B := hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := I)
  have huP : IsUnit (q : Γ(c.pt, ⊤)) := by
    have := (hu j0).map (c.π.app j0).appTop.hom
    simpa using this
  constructor
  · intro x
    obtain ⟨j, y, hy⟩ := B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP
    refine ⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩
    have key := pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom)
      (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n y
    refine key.trans ?_
    have hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y =
      pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x := hy
    rw [hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, pull_id]
  · intro j y hy
    obtain ⟨k, f, hk⟩ := B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by
      have key2 := pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv)
        (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y
      exact key2.trans (by rw [hy]; exact map_zero _))
    refine ⟨k.unop, f.unop, ?_⟩
    have e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
    rw [e1]
    have key3 := pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom)
      (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)
    refine key3.trans ?_
    have hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0 := hk
    rw [hk', map_zero]

theorem ContAff_of : ContAff := by
  intro h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : IsAffine (D.obj j0) := IsAffine.of_isIso e.hom
  have hc' : IsLimit (c.whisker (Over.forget j0)) := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc
  have hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k) := fun k => by
    have i1 := ha k.hom
    have i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right)) := ‹IsAffine (D.obj j0)›
    exact @isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2
  have hP : IsAffine c.pt := by
    have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f) := ha
    have := hcs; have := hqs
    have := isAffineHom_π_app D c hc j0
    exact isAffine_of_isAffineHom (c.π.app j0)
  have R := aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _)
    (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨k, y, hy⟩ := R.1 x
    exact ⟨k.left, y, hy⟩
  · obtain ⟨k, g, h0, -⟩ := IsCofilteredOrEmpty.cone_objs j j0
    obtain ⟨l, f, hf⟩ := R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by
      show pull _ (sch.map (c.π.app k)) _ _ _ = 0
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]
      exact hy)
    refine ⟨l.left, f.left ≫ g, ?_⟩
    rw [D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]
    exact hf

end LateralTheory.E.ContAffPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContStepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContStepPf

def PCS (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

def PCK (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

theorem PC_of {X0 : Scheme.{0}} (h1 : PCS X0) (h2 : PCK X0) : PC X0 := by
  intro q J _ _ D c hc ha hcs hqs hu j0 e n i
  exact ⟨h1 q D c hc ha hcs hqs hu j0 e n i, h2 q D c hc ha hcs hqs hu j0 e n i⟩

def StepS : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCS X

def StepK : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCK X

theorem ContStep_of (hS : StepS) (hK : StepK) : ContStep := by
  intro h hmv X U V hU hV hUV pU pV pW
  exact PC_of (hS h hmv X U V hU hV hUV pU pV pW) (hK h hmv X U V hU hV hUV pU pV pW)

end LateralTheory.E.ContStepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescIntPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut

namespace LateralTheory.E.DescIntPf

def RelZS (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {U E : Spc} (u : U ⟶ E) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull R u F m)) ∧ Function.Injective (pull R u F n)

theorem relZ_iff (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) :
    RelZ q i n f ↔ RelZS (ZMod q) (tw q i) n (sch.map (Spec.map f)) := Iff.rfl

theorem transfer (R : Type) [CommRing R] (F : Shv R) {U E X' X : Spc} (u : U ⟶ E) (f : X' ⟶ X) (a' : U ⟶ X')
    (a : E ⟶ X) (hsq : u ≫ a = a' ≫ f) (ha : Eqv R a F) (ha' : Eqv R a' F) (n : ℤ) (hu : RelZS R F n u) :
    RelZS R F n f := by
  have key : ∀ m (x : H R X F m), pull R a' F m (pull R f F m x) = pull R u F m (pull R a F m x) := by
    intro m x
    rw [← pull_comp, ← pull_comp, hsq]
  refine ⟨fun m hm y => ?_, fun x x' hxx => ?_⟩
  · obtain ⟨z, hz⟩ := hu.1 m hm (pull R a' F m y)
    obtain ⟨x, rfl⟩ := (ha m).2 z
    refine ⟨x, (ha' m).1 ?_⟩
    rw [key, hz]
  · have h1 := congrArg (pull R a' F n) hxx
    rw [key, key] at h1
    exact (ha n).1 (hu.2 h1)

theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F := fun n => by
  have h1 : ∀ x, pull R e.inv F n (pull R e.hom F n x) = x := fun x => by
    rw [← pull_comp, e.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R e.hom F n (pull R e.inv F n x) = x := fun x => by
    rw [← pull_comp, e.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem RelZS.of_iso (R : Type) [CommRing R] (F : Shv R) {U E U' E' : Spc} (u : U ⟶ E) (u' : U' ⟶ E') (e₁ : U ≅ U')
    (e₂ : E ≅ E') (hsq : u ≫ e₂.hom = e₁.hom ≫ u') (n : ℤ) (hu : RelZS R F n u) : RelZS R F n u' :=
  transfer R F u u' e₁.hom e₂.hom hsq (eqv_of_iso R F e₂) (eqv_of_iso R F e₁) n hu

def EtaleRelativeIsoTruncationFromLevels : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (u : U ⟶ E) (n : ℤ),
  (∀ (p : ℕ) (m : ℤ), m < n → RelZS R F m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) →
  RelZS R F n (disc.map (u.app (Opposite.op (SimplexCategory.mk 0)))) → RelZS R F n u

def CechSq : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' →
  ∃ (U E : Spc) (u : U ⟶ E) (a' : U ⟶ sch.obj (Spec Y')) (a : E ⟶ sch.obj (Spec C)),
    u ≫ a = a' ≫ sch.map (Spec.map φ') ∧ Eqv _ a (tw q i) ∧ Eqv _ a' (tw q i) ∧
    (∀ p : ℕ, ∃ (L : CommRingCat.{0}) (l : A ⟶ L) (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : L ⟶ Z),
      P L l ∧ IsPushout φ l wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk p))))) ∧
    ∃ (Z : CommRingCat.{0}) (wz : Y ⟶ Z) (ψ : D ⟶ Z), IsPushout φ (c ≫ g) wz ψ ∧
      ∀ m, RelZ q i m ψ → RelZS (ZMod q) (tw q i) m (disc.map (u.app (Opposite.op (SimplexCategory.mk 0))))

theorem DescInt_of (hT : EtaleRelativeIsoTruncationFromLevels) (hC : CechSq) : LateralTheory.E.StalkCut.DescInt := by
  intro hH q _ i n A Y φ hq P hpush hbelow C D c g hCc hDc hgi hgs hDn Y' w φ' hpo
  obtain ⟨U, E, u, a', a, hsq, ha, ha', hlev, Z, wz, ψ, hpo0, h0⟩ :=
    hC hH q i φ hq P @hpush c g hCc hDc hgi hgs Y' w φ' hpo
  rw [relZ_iff]
  refine transfer _ _ u _ a' a hsq ha ha' n (hT _ _ u n (fun p m hm => ?_) (h0 n (hDn Z wz ψ hpo0)))
  obtain ⟨L, l, Z', wz', ψ', hL, hpo', hrel⟩ := hlev p
  exact hrel m (hbelow m hm L l hL Z' wz' ψ' hpo')

end LateralTheory.E.DescIntPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtAffNbhdPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleCohomologyThirdStatementHolds
section
namespace LateralTheory.Fin.EtaleChapterDThree
theorem etale_cohomology_third_statement_holds_alt : LateralTheory.E.EtaleChapterDThree := by
  apply LateralTheory.E.t_D3Cut.goal
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDThree := etale_cohomology_third_statement_holds_alt
end LateralTheory.Fin.EtaleChapterDThree
end

