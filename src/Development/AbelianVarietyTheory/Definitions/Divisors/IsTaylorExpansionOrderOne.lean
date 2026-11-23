module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

section Tay

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : Type} [CommRing R] [Algebra ℂ R]

abbrev evT {W : Opens E} (R : Type) [CommRing R] [Algebra ℂ R] (p : E) (hp : p ∈ W) : R ⊗[ℂ] Hol W →ₐ[ℂ] R :=
  Algebra.TensorProduct.lift (AlgHom.id ℂ R) ((Algebra.ofId ℂ R).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)

def IsTay {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} (N : ℕ) (t : I → R) {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀) : Prop :=
  ∀ (h : Hol W) (p : Tot Empty g) (hp : p ∈ W₀), evT R p hp (ρ h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)

end Tay

namespace Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R]

def shA {l : Λ} {k k' : K.K} (h : K.le l k' k) : Hol (K.W k) →ₐ[ℂ] Hol (K.W k') :=
  Hol.comap (F.shift l) (F.shift_analytic l (K.base k')) (K.maps h)

theorem shA_apply {l : Λ} {k k' : K.K} (h : K.le l k' k) (x : Hol (K.W k)) : shA h x = sh h x := rfl


variable (K) in
structure DObj (η : Hol F.V →+* R) (M : Ideal R) : Type 1 where

  T : K.Obj
  [alg : Algebra R T.C]
  compat : ∀ f, algebraMap (Hol F.V) T.C f = algebraMap R T.C (η f)
  mem : ∀ d ∈ M, algebraMap R T.C d ∈ T.J

attribute [instance] DObj.alg

variable {η : Hol F.V →+* R} {M : Ideal R}

instance : Category (K.DObj η M) where
  Hom S S' := {f : S.T ⟶ S'.T // ∀ d, f.φ (algebraMap R S.T.C d) = algebraMap R S'.T.C d}
  id S := ⟨𝟙 _, fun _ ↦ rfl⟩
  comp f f' := ⟨f.1 ≫ f'.1, fun d ↦ by rw [comp_φ, f.2, f'.2]⟩
  id_comp f := Subtype.ext (Category.id_comp _)
  comp_id f := Subtype.ext (Category.comp_id _)
  assoc f f' f'' := Subtype.ext (Category.assoc _ _ _)


variable (K η M) in
@[reducible] def OD : K.DObj η M ⥤ CommAlgCat.{0} R where
  obj S := CommAlgCat.of _ S.T.C
  map f := CommAlgCat.ofHom { (f.1.φ : _ →+* _) with commutes' := f.2 }


variable (K η M) in
def perZD (q : Λ →+ R) : Z1 (K.OD η M) :=
  ⟨fun _ S' f ↦ algebraMap R S'.T.C (q f.1.deg), fun S S' S'' f f' ↦ by
    change algebraMap _ S''.T.C (q (f.1.deg + f'.1.deg)) = f'.1.φ (algebraMap _ _ _) + algebraMap _ S''.T.C _
    rw [f'.2, map_add (f := _), map_add (f := _)]⟩


variable (K η M) in
def perClD (q : Λ →+ R) : CatCoh.H1 (K.OD η M) := H1.mk _ (K.perZD η M q)


end Charts

section Theta

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {R : Type} [CommRing R] {η : Hol F.V →+* R} {M : Ideal R}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}
  {D : Type} [CommRing D] {J : Ideal D}

structure IsOver (η : Hol F.V →+* R) (M : Ideal R) (s : X ⟶ Sp B) (σ : B →+* Hol F.V) (J : Ideal D) (s' : X ⟶ Sp D)
    (π : D →+* B) (ι : D →+* R) : Prop where
  w : s' = s ≫ spMap π
  mem : ∀ d ∈ J, ι d ∈ M
  red : ∀ d, ι d - η (σ (π d)) ∈ M

variable (r : Real K s σ) (κ : DividedPowers J) {s' : X ⟶ Sp D} {π : D →+* B} {ι : D →+* R} (H : IsOver η M s σ J s' π ι)

def Real.objD (S : K.DObj η M) : Thick κ s' where
  B := S.T.C
  alg := ((algebraMap R S.T.C).comp ι).toAlgebra
  J := S.T.J
  δ := S.T.δ
  nil := letI := S.T.ratAlg; isPDNilpotent_of_rat _ S.T.nil
  dp := letI := S.T.ratAlg; isDPMorphism_of_rat κ S.T.δ _ fun d hd ↦ S.mem _ (H.mem d hd)
  B₀ := S.T.C ⧸ S.T.J
  π := Ideal.Quotient.mk S.T.J
  surj := Ideal.Quotient.mk_surjective
  ker _ := Ideal.Quotient.eq_zero_iff_mem
  x := spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r.x S.T.k
  w := by
    rw [H.w, Category.assoc, ← Category.assoc (r.x _), r.w, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 1
    refine RingHom.ext fun d ↦ (Ideal.Quotient.eq.2 ?_).symm
    have := S.mem _ (H.red d)
    rw [map_sub, ← S.compat, ← S.T.ρ_cst] at this
    exact this

def Real.coefD : CoefMap ι (O κ s') (K.OD η M) where
  G :=
    { obj := r.objD κ H
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun d ↦ f.2 (ι d) }
          φ₀ := Ideal.quotientMap S'.T.J (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          comm := fun _ ↦ rfl
          dp := letI := S'.T.ratAlg; isDPMorphism_of_rat S.T.δ S'.T.δ (f.1.φ : S.T.C →+* S'.T.C) f.1.mem
          pt := r.analyticChartsRealization_comp_point_eq f.1 }
      map_id _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)
      map_comp _ _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (ι d) c).symm

end Theta

section Inhabitants

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}

def jetAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} (v p : E) (hp : p ∈ W) :
    Hol W →+* DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (Hol.ev p hp h) + TrivSqZeroExt.inr (Hol.ev p hp (Hol.der v h))
  map_one' := by simp
  map_mul' x y := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [Derivation.leibniz, mul_comm]
  map_zero' := by simp
  map_add' x y := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp

def Charts.dualD (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    K.DObj (jetAt v p.1 (K.base k p hp)) (Ideal.span {DualNumber.eps}) where
  T :=
    { k := k
      C := DualNumber ℂ
      alg := (jetAt v p.1 (K.base k p hp)).toAlgebra
      J := Ideal.span {DualNumber.eps}
      nil := ⟨2, by rw [Ideal.span_singleton_pow, sq, DualNumber.eps_mul_eps]; simp⟩
      ρ := jetAt ((v, 0) : Tot I g) p hp
      ρ_cst := fun f ↦ by
        have e1 : Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f := by
          rw [Hol.ev_apply, Hol.ev_apply, K.fn_cst k f hp]
        have e2 : Hol.ev p hp (Hol.der ((v, 0) : Tot I g) (K.cst k f)) =
            Hol.ev p.1 (K.base k p hp) (Hol.der v f) := by
          rw [Hol.ev_apply, Hol.ev_apply, Hol.fn_der _ _ (K.base k p hp)]
          refine (Hol.fn_der_comap _ _ _ _ f hp).trans ?_
          rw [fderiv_fst]; rfl
        change (TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _ : DualNumber ℂ) = TrivSqZeroExt.inl _ + TrivSqZeroExt.inr _
        rw [e1, e2] }
  alg := Algebra.id (DualNumber ℂ)
  compat _ := rfl
  mem _ h := h

theorem Charts.dualD_J_ne_bot (K : Charts F) (k : K.K) (v : I → ℂ) (p : Tot I g) (hp : p ∈ K.W k) :
    (K.dualD k v p hp).T.J ≠ ⊥ := by
  intro h
  have h' : (DualNumber.eps : DualNumber ℂ) = 0 := Ideal.span_singleton_eq_bot.1 h
  simpa using congrArg TrivSqZeroExt.snd h'

def Charts.Obj.toD {K : Charts F} (T : K.Obj) : K.DObj (RingHom.id _) ⊥ where
  T := T
  alg := T.alg
  compat _ := rfl
  mem d h := by rw [Ideal.mem_bot.1 h, map_zero]; exact T.J.zero_mem

end Inhabitants

end GlobalTheory.AnPer
