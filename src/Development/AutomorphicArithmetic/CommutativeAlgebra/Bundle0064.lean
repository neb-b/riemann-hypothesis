module

public import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0014
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0015
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0031
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0018
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0017
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0019
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0023
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0042
public import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0033
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0035
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
public import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupFirstLocusEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section
namespace UpperTheory.Rel1

private abbrev Ac (N : ℕ) : Act := (BC N).sub ((Q1 N).comap (βC N))

private theorem isUnit_cyclotomicPeriod_deRham {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) :
    IsUnit ((show Um N A × Um 2 A from p.pt.1).2.1 1) := by
  have h := p.pt.2
  change IsUnit ((Um.join (show Um N A × Um 2 A from p.pt.1)).1 (Fin.last N)) at h
  simpa [Um.join] using h

private def tU {N : ℕ} {A : CommRingCat.{0}} (p : Ob (Ac N) A) : Aˣ := (isUnit_cyclotomicPeriod_deRham p).unit

private def vert {E : Spc} {N : ℕ} {T : Scheme.{0}} (x : Sx (Sp E (Ac N)) 0 T) : Ob (Ac N) Γ(T, ⊤) :=
  (show ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 0 from x.2).obj 0

private def ww (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 0 T) : (Γ(T, ⊤))ˣ := tU (vert x)

private theorem triv1 (E : Spc) (N : ℕ) {T' T : Scheme.{0}} (g : T' ⟶ T) (x : Sx (Sp E (Ac N)) 0 T) :
    ww E N T' (x.res g) = Units.map g.appTop.hom.toMonoidHom (ww E N T x) := by
  ext
  rfl

private theorem triv2 (E : Spc) (N : ℕ) (T : Scheme.{0}) (x : Sx (Sp E (Ac N)) 1 T) :
    lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x * ww E N T (x.face 0) = ww E N T (x.face 1) := by
  let c : ComposableArrows (Ob (Ac N) Γ(T, ⊤)) 1 := x.2
  let f := c.map' 0 1
  have hl : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x = (show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 := by
    have e : lineUnit (Sp.map E (incl ((Q1 N).comap (βC N))) ≫ Sp.line E (chiB N)) x =
        Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1)
          (show (Γ(T, ⊤))ˣ from (chiB N).app Γ(T, ⊤) f.1)) := rfl
    rw [e]
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
    rfl
  rw [hl]
  change _ * tU (c.obj 1) = tU (c.obj 0)
  ext
  have e := congrArg (fun p => (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from p.1).2.1 1) f.2
  change ((show (Γ(T, ⊤))ˣ × (Γ(T, ⊤))ˣ from f.1).2 : Γ(T, ⊤)) * (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 1).pt.1).2.1 1 =
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from (c.obj 0).pt.1).2.1 1
  refine Eq.trans ?_ e.symm
  rfl

end UpperTheory.Rel1
end

theorem UpperTheory.chernClass_pullback_blowupFirstLocus_eq_zero :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q1 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) = 0 := by
  intro q _ N E hE
  have hX : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hY : Inv q (Sp E (UpperTheory.Rel1.Ac N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  rw [(GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q).2.1 _ _ hX]
  exact UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ (UpperTheory.Rel1.ww E N) hY ⟨fun g x => UpperTheory.Rel1.triv1 E N g x, UpperTheory.Rel1.triv2 E N⟩
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.ChernClassPullbackBlowupSecondLocusEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

noncomputable section

namespace UpperTheory.LineUnitTrivialization

private def arr {a : Act} {E : Spc} {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) : a.G.obj Γ(U, ⊤) :=
  (show ComposableArrows (Ob a Γ(U, ⊤)) 1 from x.2).hom.1

private theorem det_scalar {A : Type} [CommRing A] (u : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp

private theorem lineUnit_line {a : Act} {E : Spc} (χ : a.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (arr x)) :=
  det_scalar _

private theorem lineUnit_map {a b : Act} {E : Spc} (φ : Act.Hom a b) (χ : b.G ⟶ gmF) {U : Scheme.{0}} (x : Sx (Sp E a) 1 U) :
    lineUnit (Sp.map E φ ≫ Sp.line E χ) x = (show (Γ(U, ⊤))ˣ from χ.app Γ(U, ⊤) (φ.g.app Γ(U, ⊤) (arr x))) :=
  det_scalar _

private def chiM (N : ℕ) (Q : Pred (BC N)) : ((BC N).sub Q).G ⟶ gmF where
  app A := GrpCat.ofHom (MonoidHom.snd Aˣ Aˣ / MonoidHom.fst Aˣ Aˣ)
  naturality A B f := by
    ext x
    exact (map_div (Units.map (f.hom : A →* B)) x.2 x.1).symm

private theorem isUnit_um_join_of_span_castSucc_eq_whole {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have h' : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) ≤ Ideal.span {x.2.1 0} := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp only [Um.join, Fin.snoc_castSucc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  rw [h, top_le_iff, Ideal.span_singleton_eq_top] at h'
  exact h'

private def sU {N : ℕ} {A : CommRingCat.{0}} (y : ((BC N).sub ((Q2 N).comap (βC N))).D.obj A) : Aˣ :=
  (isUnit_um_join_of_span_castSucc_eq_whole (A := A) y.1 y.2).unit

private def wS (N : ℕ) (E : Spc) (T : Scheme.{0}) (y : Sx (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) 0 T) : (Γ(T, ⊤))ˣ :=
  sU (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 0 from y.2).left.pt

private theorem triv (N : ℕ) (E : Spc) :
    IsTrivBy (Sp.line E (chiM N ((Q2 N).comap (βC N)))) (wS N E) := by
  refine ⟨?_, ?_⟩
  · intro T' T g x
    apply Units.ext
    simp only [wS, sU, IsUnit.unit_spec, Units.coe_map]
    rfl
  · intro T x
    rw [lineUnit_line]
    apply Units.ext
    have key := (show ComposableArrows (Ob ((BC N).sub ((Q2 N).comap (βC N))) Γ(T, ⊤)) 1 from x.2).hom.2
    have k2 := congrArg (fun y => (y.1.2.1 0 : Γ(T, ⊤))) key
    simp only [wS, sU, IsUnit.unit_spec]
    exact k2.symm

end UpperTheory.LineUnitTrivialization

end

open UpperTheory.LineUnitTrivialization in
theorem UpperTheory.chernClass_pullback_blowupSecondLocus_eq :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc), Inv q E →
        pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiB N))) =
          pull _ (Sp.map E (incl ((Q2 N).comap (βC N)))) _ _ (c1 q (Sp.line E (chiH N))) := by
  intro q _ N E hE
  have hI : Inv q (Sp E ((BC N).sub ((Q2 N).comap (βC N)))) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  have hI' : Inv q (Sp E (BC N)) := fun U ⟨x⟩ => hE U ⟨x.1⟩
  obtain ⟨-, hpull, hadd⟩ := GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive q
  rw [hpull _ _ hI', hpull _ _ hI']
  have h0 : c1 q (Sp.line E (chiM N ((Q2 N).comap (βC N)))) = 0 := UpperTheory.firstChernClass_eq_zero_of_isTrivialized q _ _ hI (triv N E)
  have hsum := hadd (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiH N))
    (Sp.line E (chiM N ((Q2 N).comap (βC N))))
    (Sp.map E (incl ((Q2 N).comap (βC N))) ≫ Sp.line E (chiB N)) hI (by
      intro U x
      rw [lineUnit_map, lineUnit_map, lineUnit_line]
      first
        | exact (mul_div_cancel _ _).symm
        | exact (mul_div_cancel_left _ _).symm
        | exact (mul_div_cancel'_right _ _).symm)
  rw [hsum, h0, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.EqvTwistBlowupRestriction
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.BlowEqv

private theorem s_unit {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A)
    (h : Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤) : IsUnit (x.2.1 0) := by
  have key : ∀ i : Fin N, (Um.join x).1 (Fin.castSucc i) = x.2.1 0 * x.1.1 i := by
    intro i
    simp [Um.join, Fin.snoc_castSucc]
  rw [← Ideal.span_singleton_eq_top]
  refine eq_top_iff.2 (le_trans (le_of_eq h.symm) ?_)
  rw [Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

private def vec1 {A : Type} [CommRing A] (s : A) (h : IsUnit s) : Um 1 A :=
  ⟨fun _ => s, by
    rw [Set.range_const]
    exact Ideal.span_singleton_eq_top.2 h⟩

private theorem unimodularRow_one_isUnit {A : Type} [CommRing A] (c : Um 1 A) : IsUnit (c.1 0) := by
  have h := c.2
  rw [Set.range_unique] at h
  exact Ideal.span_singleton_eq_top.1 h

private theorem join_inj {N : ℕ} {A : Type} [CommRing A] {x y : Um N A × Um 2 A} (hs : x.2.1 0 = y.2.1 0)
    (hu : IsUnit (x.2.1 0)) (h : Um.join x = Um.join y) : x = y := by
  have h1 := congrArg Subtype.val h
  have hl : x.2.1 1 = y.2.1 1 := by
    have := congrFun h1 (Fin.last N)
    simpa [Um.join] using this
  have hi : ∀ i, x.1.1 i = y.1.1 i := by
    intro i
    have := congrFun h1 (Fin.castSucc i)
    simp only [Um.join, Fin.snoc_castSucc] at this
    rw [← hs] at this
    exact hu.mul_left_cancel this
  refine Prod.ext (Subtype.ext (funext hi)) (Subtype.ext (funext fun j => ?_))
  refine Fin.cases hs (fun k => ?_) j
  rw [Fin.fin_one_eq_zero k]
  exact hl

private theorem join_surj {N : ℕ} {A : Type} [CommRing A] (w : Um (N + 1) A)
    (hw : Ideal.span (w.1 '' Set.range Fin.castSucc) = ⊤) (u : Aˣ) :
    ∃ x : Um N A × Um 2 A, x.2.1 0 = u ∧ Um.join x = w := by
  refine ⟨(⟨fun i => (↑u⁻¹ : A) * w.1 (Fin.castSucc i), ?_⟩, ⟨![(u : A), w.1 (Fin.last N)], ?_⟩), rfl, ?_⟩
  · refine eq_top_iff.2 (le_trans (le_of_eq hw.symm) ?_)
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have e : w.1 (Fin.castSucc i) = (u : A) * ((↑u⁻¹ : A) * w.1 (Fin.castSucc i)) := by
      simp
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) u.isUnit
  · apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [Um.join]
    · simp [Um.join, Fin.snoc_castSucc]

private def ratioG : gm2F ⟶ gmF where
  app A := GrpCat.ofHom
    { toFun := fun g => (show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹
      map_one' := by
        change (1 : Aˣ) * (1 : Aˣ)⁻¹ = 1
        simp
      map_mul' := fun g h => by
        change ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from h).2) * ((show Aˣ × Aˣ from g).1 * (show Aˣ × Aˣ from h).1)⁻¹ =
          ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹) * ((show Aˣ × Aˣ from h).2 * (show Aˣ × Aˣ from h).1⁻¹)
        rw [mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  naturality A B f := by
    refine GrpCat.hom_ext (MonoidHom.ext fun g => ?_)
    change (Units.map f.hom.toMonoidHom (show Aˣ × Aˣ from g).2) * (Units.map f.hom.toMonoidHom (show Aˣ × Aˣ from g).1)⁻¹ =
      Units.map f.hom.toMonoidHom ((show Aˣ × Aˣ from g).2 * (show Aˣ × Aˣ from g).1⁻¹)
    rw [map_mul, map_inv]

private def sig (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) :
    Act.Hom ((BC N).sub (Q.comap (βC N))) (XC 1) where
  d :=
    { app := fun A => TypeCat.ofHom fun x =>
        vec1 ((show Um N A × Um 2 A from x.1).2.1 0) (s_unit _ (hQ A _ x.2))
      naturality := fun A B f => by
        ext x
        exact Subtype.ext rfl }
  g := ratioG
  eq A u x := Subtype.ext (funext fun _ => rfl)

private theorem pts_bij (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) (A : CommRingCat.{0}) :
    Function.Bijective (fun x : ((BC N).sub (Q.comap (βC N))).D.obj A =>
      ((((βC N).sub Q).d.app A x, (sig N Q hQ).d.app A x) :
        ((XC (N + 1)).sub Q).D.obj A × (XC 1).D.obj A)) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : Um.join x = Um.join y := congrArg Subtype.val h1
    have e2 : x.2.1 0 = y.2.1 0 := congrArg (fun c : Um 1 A => c.1 0) h2
    exact Subtype.ext (join_inj e2 (s_unit x (hQ A _ hx)) e1)
  · rintro ⟨⟨w, hw⟩, c⟩
    obtain ⟨x, hx0, hxw⟩ := join_surj w (hQ A w hw) (unimodularRow_one_isUnit c).unit
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show Q.P A (Um.join x)
      rw [hxw]
      exact hw
    · refine Prod.ext (Subtype.ext hxw) (Subtype.ext (funext fun i => ?_))
      obtain rfl : i = 0 := Subsingleton.elim _ _
      exact hx0.trans (unimodularRow_one_isUnit c).unit_spec

private theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (m c : G) : m * (m * c⁻¹)⁻¹ = c := by
  rw [mul_inv_rev, inv_inv, mul_comm c, mul_inv_cancel_left]

private theorem grp_bij (N : ℕ) (Q : Pred (XC (N + 1))) (hQ : Q.Le (Q2 N)) (A : CommRingCat.{0}) :
    Function.Bijective (fun g : ((BC N).sub (Q.comap (βC N))).G.obj A =>
      ((((βC N).sub Q).g.app A g, (sig N Q hQ).g.app A g) :
        ((XC (N + 1)).sub Q).G.obj A × (XC 1).G.obj A)) := by
  constructor
  · rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    change b = b' at h1
    change b * a⁻¹ = b' * a'⁻¹ at h2
    subst h1
    have e : a⁻¹ = a'⁻¹ := mul_left_cancel h2
    exact Prod.ext (inv_injective e) rfl
  · rintro ⟨m, c⟩
    let m' : (↑A : Type)ˣ := m
    let c' : (↑A : Type)ˣ := c
    refine ⟨(show (↑A : Type)ˣ × (↑A : Type)ˣ from (m' * c'⁻¹, m')), ?_⟩
    refine Prod.ext rfl ?_
    exact mul_ringHom_units_ratio m' c'

private theorem lh_norm {q : ℕ} {X E : Spc} (π : X ⟶ E) {d e : Fin 1 → ℤ} (c : ∀ j, Ht q X (d j) (e j))
    (hd : ∀ j, d j = 0) (he : ∀ j, e j = 0) (hc : ∀ j, c j = (one q X).cast (hd j).symm (he j).symm)
    (h : LH q π d e c) : LH q π (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q X) := by
  obtain rfl : d = fun _ => 0 := funext hd
  obtain rfl : e = fun _ => 0 := funext he
  have hc' : c = fun _ => one q X := funext fun j => by
    rw [hc j]
    rfl
  subst hc'
  exact h

end UpperTheory.BlowEqv

open UpperTheory.BlowEqv in
theorem UpperTheory.eqv_twist_blowupRestriction :
    ∀ (q : ℕ) [NeZero q] (N : ℕ) (E : Spc) (Q : Pred (XC (N + 1))) (i : ℤ), Q.Le (Q2 N) → Inv q E →
        Eqv _ (Sp.map E ((βC N).sub Q)) (tw q i) := by
  intro q _ N E Q i hQ hE
  have invS : ∀ {X : Spc} (Z : Spc), Inv q X → Inv q (mulS X Z) := fun Z hX U ⟨x⟩ => hX U ⟨x.1⟩
  have hF : Inv q (Sp E ((XC (N + 1)).sub Q)) := invS _ hE
  have hX : Inv q (Sp (Sp E ((XC (N + 1)).sub Q)) (XC 1)) := invS _ hF
  have hP : Pbf q (Sp E ((XC (N + 1)).sub Q)) 1 := (UpperTheory.projBundleFormula_iff_pglForm q _ 1 hF).1 (UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant q _ hF)
  unfold Pbf at hP
  have hL := lh_norm _ _ (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; simp)
    (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; simp)
    (fun j => by obtain rfl : j = 0 := Subsingleton.elim _ _; exact cpow_zero q _) hP
  have hfst : ∀ i, Eqv (ZMod q) (Sp.fst (Sp E ((XC (N + 1)).sub Q)) (XC 1)) (tw q i) :=
    (UpperTheory.lerayHirsch_one_iff_twist_equiv q _ hX).1 hL
  have hiso := UpperTheory.isIso_stackProductPair_of_bijective E ((βC N).sub Q) (sig N Q hQ) (pts_bij N Q hQ) (grp_bij N Q hQ)
  have hcomp : Sp.pair E ((βC N).sub Q) (sig N Q hQ) ≫ Sp.fst _ (XC 1) = Sp.map E ((βC N).sub Q) := by
    rfl
  rw [← hcomp]
  obtain ⟨hiso', hcmp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  exact (hcmp _ _ _ _ _).1 (hiso' _ _ _ hiso) (hfst i)
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.TwoOpenCoverOfMapIncl
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private theorem q_of_unit {N : ℕ} {A : Type} [CommRing A] (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤)
    (h : ∃ i, IsUnit (v i)) :
    IsUnit (v (Fin.last N)) ∨ Ideal.span (v '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨i, hi⟩ := h
  by_cases hl : i = Fin.last N
  · left
    rw [← hl]
    exact hi
  · right
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hl
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨_, ⟨j, rfl⟩, rfl⟩) hi

theorem UpperTheory.two_open_cover_of_map_incl :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc), Cover2 R (Sp.map E (incl (Q1 N))) (Sp.map E (incl (Q2 N))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E (incl (Q1 N)) (incl (Q2 N)) (fun A x y h => Subtype.ext h) (fun A x y h => Subtype.ext h)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um (N + 1) Γ(T, ⊤) from x).1 (show Um (N + 1) Γ(T, ⊤) from x).2
  refine ⟨S, hS, fun V g hg => ?_⟩
  let w : (XC (N + 1)).D.obj Γ(V, ⊤) := (XC (N + 1)).D.map g.appTop x
  rcases q_of_unit (fun i => g.appTop.hom ((show Um (N + 1) Γ(T, ⊤) from x).1 i))
      (show Um (N + 1) Γ(V, ⊤) from (XC (N + 1)).D.map g.appTop x).2 (hP V g hg) with h | h
  · have h' : (Q1 N).P Γ(V, ⊤) w := h
    exact Or.inl ⟨⟨w, h'⟩, rfl⟩
  · have h' : (Q2 N).P Γ(V, ⊤) w := h
    exact Or.inr ⟨⟨w, h'⟩, rfl⟩
end

