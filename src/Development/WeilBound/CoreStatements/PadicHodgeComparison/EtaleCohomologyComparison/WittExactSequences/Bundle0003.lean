module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.FlagDomainConjHostXiEqNeg
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.D

open PAlg

variable {l : ℕ} [Fact l.Prime]

theorem flagDomainConj_hostXi_eq_neg : WittVector.constantCoeff (xi0 l) = -pFlat l := by
  rw [xi0, map_sub, map_natCast, CharP.cast_eq_zero, zero_sub]
  exact congrArg Neg.neg (WittVector.teichmuller_coeff_zero l _)

theorem un_rep {A : PAlg l} {n : ℕ} (x : A.Un n) : ∃ w : A.W, x = Ideal.Quotient.mk _ (A.th w) := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {A.xi}) u
  exact ⟨w, rfl⟩

variable (A : PAlg l)

def rho0 : A.U →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp WittVector.constantCoeff) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    have e : WittVector.constantCoeff A.xi = -A.pi := by
      change (WittVector.map A.s (xi0 l)).coeff 0 = -A.s (pFlat l)
      rw [WittVector.map_coeff, ← map_neg, ← flagDomainConj_hostXi_eq_neg]; rfl
    rw [RingHom.comp_apply, map_mul, e]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ _ (neg_mem (Ideal.mem_span_singleton_self _)))

def rho : A.Un 1 →+* A.A ⧸ Ideal.span {A.pi} :=
  Ideal.Quotient.lift _ (rho0 A) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, ← map_natCast (Ideal.Quotient.mk (Ideal.span {A.pi})), A.natCast_l, map_zero,
      zero_pow one_ne_zero, mul_zero]

theorem rho_mk (w : A.W) : rho A (Ideal.Quotient.mk _ (A.th w)) = Ideal.Quotient.mk _ (w.coeff 0) := rfl

theorem rho_bij (hU : RU l) : Function.Bijective (rho A) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨w, rfl⟩ := un_rep x
    rw [rho_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have := ((hU A).2 w).2 hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [pow_one])
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ (A.th (WittVector.teichmuller l a)), by rw [rho_mk, WittVector.teichmuller_coeff_zero]⟩

theorem span_pi_eq : (Ideal.span {A.pi}).restrictScalars (Ob l) = (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, trivial, by rw [Algebra.smul_def, mul_comm]; rfl⟩
  · rintro ⟨b, _, rfl⟩
    exact ⟨b, by rw [Algebra.smul_def, mul_comm]; rfl⟩

def kappa : (A.A ⧸ Ideal.span {A.pi}) ≃ₗ[Ob l] A.A ⧸ (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A) :=
  (Submodule.Quotient.restrictScalarsEquiv (Ob l) (Ideal.span {A.pi})).symm.trans (Submodule.quotEquivOfEq _ _ (span_pi_eq A))

def tau1 : A.Un 1 →+ (Ob l ⧸ Ideal.span {pFlat l}) ⊗[Ob l] A.A :=
  ((TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.toAddMonoidHom.comp
    (kappa A).toAddMonoidHom).comp (rho A).toAddMonoidHom

theorem kappa_mk (x : A.A) :
    kappa A (Ideal.Quotient.mk _ x) = Submodule.Quotient.mk (p := (Ideal.span {pFlat l} • ⊤ : Submodule (Ob l) A.A)) x := by
  rfl

theorem tau1_mk (w : A.W) : tau1 A (Ideal.Quotient.mk _ (A.th w)) = (1 : Ob l ⧸ Ideal.span {pFlat l}) ⊗ₜ[Ob l] w.coeff 0 := by
  change (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm (kappa A (rho A (Ideal.Quotient.mk _ (A.th w)))) = _
  rw [rho_mk, kappa_mk]
  exact TensorProduct.quotTensorEquivQuotSMul_symm_mk _ _

theorem tau1_bijective (hU : RU l) : Function.Bijective (tau1 A) :=
  (TensorProduct.quotTensorEquivQuotSMul A.A (Ideal.span {pFlat l})).symm.bijective.comp
    ((kappa A).bijective.comp (rho_bij A hU))

theorem tau1_smul (a : Ainf l) (x : A.Un 1) :
    tau1 A (a • x) = WittVector.constantCoeff a • tau1 A x := by
  obtain ⟨w, rfl⟩ := un_rep x
  have e : a • (Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th w)) =
      Ideal.Quotient.mk (Ideal.span {(l : A.U) ^ 1}) (A.th (A.sW a * w)) := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (Ainf l) A.U, Ideal.Quotient.algebraMap_eq, ← map_mul, map_mul A.th]; rfl
  rw [e, tau1_mk, tau1_mk, ← TensorProduct.tmul_smul, WittVector.mul_coeff_zero, Algebra.smul_def]
  change _ ⊗ₜ[Ob l] ((WittVector.map A.s a).coeff 0 * _) = _
  rw [WittVector.map_coeff]; rfl

end CrystallineSemistableComparison.D
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ResKill
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

section Span
universe w₁
variable {R : Type} [CommRing R]

theorem res_add {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} {a b : R}
    (ha : K.ResUpTo a ε) (hb : K.ResUpTo b ε) : K.ResUpTo (a + b) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [add_smul, ha.2.1 x hx, hb.2.1 x hx, add_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    obtain ⟨x', hx'⟩ := hb.2.2.1 y hy
    exact ⟨x + x', by rw [map_add (f := _), hx, hx', add_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    obtain ⟨x', hx'⟩ := hb.2.2.2 n y hy
    exact ⟨x + x', by rw [map_add (f := _), hx, hx', add_smul]⟩

theorem res_mul {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (r : R) {a : R}
    (ha : K.ResUpTo a ε) : K.ResUpTo (r * a) ε := by
  refine ⟨ha.1, fun x hx => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · rw [mul_smul, ha.2.1 x hx, smul_zero]
  · obtain ⟨x, hx⟩ := ha.2.2.1 y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩
  · obtain ⟨x, hx⟩ := ha.2.2.2 n y hy
    exact ⟨r • x, by rw [map_smul, hx, mul_smul]⟩

theorem res_kill {K : Cx.{w} R} {M : Type w₁} [AddCommGroup M] [Module R M] {ε : M →ₗ[R] K.X 0} (a : R)
    (h0 : ∀ x, K.d 0 (ε x) = 0) (hM : ∀ x : M, a • x = 0) (hK : ∀ n (y : K.X n), a • y = 0) : K.ResUpTo a ε :=
  ⟨h0, fun x _ => hM x, fun y _ => ⟨0, by rw [map_zero, hK]⟩, fun n y _ => ⟨0, by rw [map_zero, hK]⟩⟩

theorem d_ptsAug {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) : d (elF (pts j A) (j ⋙ F)) 0 (ptsAug j F A x) = 0 := by
  funext s
  have key : ∀ i : Fin 2, ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom (ptsAug j F A x (GlobalTheory.CatH.face i s)) =
      (F.map (s.obj (Fin.last 1)).2).hom x := by
    intro i
    change (F.map ((GlobalTheory.CatH.face i s).obj (Fin.last 0)).2 ≫ F.map (j.map (GlobalTheory.CatH.toLast i s).1)).hom x = _
    rw [← F.map_comp]
    congr 3
    exact (GlobalTheory.CatH.toLast i s).2
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((elF (pts j A) (j ⋙ F)).map (GlobalTheory.CatH.toLast i s)).hom
    (ptsAug j F A x (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two, key, key]
  simp

end Span

def ptsG {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') (A : C) : pts j A ⟶ pts (j ⋙ G) (G.obj A) where
  app t := TypeCat.ofHom fun y => G.map y
  naturality t t' φ := by
    ext y
    exact G.map_comp y (j.map φ)

theorem des_ff {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {C' : Type u''} [Category.{v} C'] (G : C ⥤ C') [G.Full] [G.Faithful] (F : C' ⥤ ModuleCat.{w} R) (s : R) :
    DesJ (j ⋙ G) F s → DesJ j (G ⋙ F) s := by
  intro h A
  have hb : ∀ t, Function.Bijective ((ptsG j G A).app t) := fun t =>
    ⟨fun y y' (e : G.map y = G.map y') => G.map_injective e, fun y => ⟨G.preimage y, G.map_preimage y⟩⟩
  have := (CrystallineSemistableComparison.P.res_semilinear (elMor (ptsG j G A) ((j ⋙ G) ⋙ F)).hom (ptsAug (j ⋙ G) F (G.obj A))
    (ptsAug j (G ⋙ F) A) LinearMap.id s Function.bijective_id (CrystallineSemistableComparison.P.el_iso _ _ hb) (fun x => rfl)).1 (h (G.obj A))
  exact this

theorem des_span {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R) (S : Set R)
    (h : ∀ a ∈ S, DesJ j F a ∨ ∀ (A : C) (x : F.obj A), a • x = 0) : ∀ s ∈ Ideal.span S, DesJ j F s := by
  have kill : ∀ a : R, (∀ (A : C) (x : F.obj A), a • x = 0) → DesJ j F a := fun a ha A =>
    res_kill a (d_ptsAug j F A) (ha A) fun n y => by funext s; exact ha _ (y s)
  intro s hs
  induction hs using Submodule.span_induction with
  | mem a ha => exact (h a ha).elim id (kill a)
  | zero => exact kill 0 fun _ x => zero_smul R x
  | add a b _ _ ha hb => exact fun A => res_add (ha A) (hb A)
  | smul r a _ ha => exact fun A => res_mul r (ha A)

end CrystallineSemistableComparison.D
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SemilinearOfAdditive
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

universe w₁

def semilinearOfAdditive {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {M : Type w} {M' : Type w₁}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (τ : M →+ M')
    (h : ∀ (a : R) x, τ (a • x) = σ a • τ x) : M →ₛₗ[σ] M' where
  toFun := τ
  map_add' := map_add τ
  map_smul' := h

def semiMor {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C]
    (E : C ⥤ Type v') (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x)
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) :
    CH.Mor (CH.elF E F) (CH.elF E F') σ where
  G := 𝟭 _
  τ X := semilinearOfAdditive σ (τ X.1) (hσ X.1)
  nat φ x := hn φ.1 x

theorem d_aug_zero {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)
    {M : Type w₁} [AddCommGroup M] [Module R M] (e : ∀ T : C, M →ₗ[R] F.obj T)
    (he : ∀ {T T' : C} (φ : T ⟶ T') x, (F.map φ).hom (e T x) = e T' x) (x : M) :
    CH.d F 0 (CH.aug F e x) = 0 := by
  funext s
  simp only [CH.d, LinearMap.coe_mk, AddHom.coe_mk, CH.aug, LinearMap.pi_apply, he]
  simp

theorem ptsAug_d {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (A : C) (x : F.obj A) :
    CH.d (CH.elF (CH.pts j A) (j ⋙ F)) 0 (CH.ptsAug j F A x) = 0 :=
  d_aug_zero _ _ (fun {X Y} φ y => by
    change (F.map (j.map φ.1)).hom ((F.map X.2).hom y) = (F.map Y.2).hom y
    rw [← ModuleCat.comp_apply, ← F.map_comp]
    exact congrArg (fun g => (F.map g).hom y) φ.2) x

theorem des_semi {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F : C ⥤ ModuleCat.{w} R) (F' : C ⥤ ModuleCat.{w} R') (τ : ∀ A : C, F.obj A →+ F'.obj A)
    (hσ : ∀ A (a : R) x, τ A (a • x) = σ a • τ A x) (hb : ∀ A, Function.Bijective (τ A))
    (hn : ∀ {A B : C} (f : A ⟶ B) x, τ B ((F.map f).hom x) = (F'.map f).hom (τ A x)) (s : R) :
    DesJ j F s ↔ DesJ j F' (σ s) := by
  refine forall_congr' fun A => ?_
  let m : CH.Mor (CH.elF (CH.pts j A) (j ⋙ F)) (CH.elF (CH.pts j A) (j ⋙ F')) σ :=
    semiMor σ (CH.pts j A) (j ⋙ F) (j ⋙ F') (fun X => τ (j.obj X)) (fun X => hσ _) (fun f x => hn (j.map f) x)
  refine CrystallineSemistableComparison.P.res_semilinear m.hom (CH.ptsAug j F A) (CH.ptsAug j F' A) (semilinearOfAdditive σ (τ A) (hσ A)) s (hb A)
    (fun n => ⟨?_, ?_⟩) (fun x => ?_)
  · intro f g h
    funext t
    have h' : τ (j.obj (t.obj (Fin.last n)).1) (f t) = τ (j.obj (t.obj (Fin.last n)).1) (g t) := congrFun h t
    exact (hb _).1 h'
  · intro g
    exact ⟨fun t => Function.surjInv (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t),
      funext fun t => Function.surjInv_eq (hb (j.obj (t.obj (Fin.last n)).1)).2 (g t)⟩
  · funext t
    exact hn _ x

theorem des_res {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {C : Type u} [Category.{v} C] {T : Type u'}
    [Category.{v'} T] (j : T ⥤ C) (F : C ⥤ ModuleCat.{w} R') (s : R) :
    DesJ j (F ⋙ ModuleCat.restrictScalars σ) s ↔ DesJ j F (σ s) :=
  des_semi σ j (F ⋙ ModuleCat.restrictScalars σ) F (fun A => AddMonoidHom.id (F.obj A)) (fun _ _ _ => rfl)
    (fun _ => Function.bijective_id) (fun _ _ => rfl) s

def natRes {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂)
    {C : Type u} [Category.{v} C] (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x)) :
    F₁ ⋙ ModuleCat.restrictScalars σ₁ ⟶ F₂ ⋙ ModuleCat.restrictScalars σ₂ where
  app A :=
    letI : Module R (F₁.obj A) := Module.compHom _ σ₁
    letI : Module R (F₂.obj A) := Module.compHom _ σ₂
    ModuleCat.ofHom {
      toFun := α A
      map_add' := map_add (α A)
      map_smul' := hα A }
  naturality A B f := by
    ext x
    exact nα f x

theorem des_ses_nat {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    {G₁ G₂ G₃ : C ⥤ ModuleCat.{w} R} (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃)
    (hi : ∀ A, Function.Injective (α.app A).hom) (he : ∀ A, Function.Exact (α.app A).hom (β.app A).hom)
    (hs : ∀ A, Function.Surjective (β.app A).hom) (s : R) :
    (DesJ j G₁ s → DesJ j G₃ s → DesJ j G₂ (s ^ 3)) ∧ (DesJ j G₂ s → DesJ j G₃ s → DesJ j G₁ (s ^ 3)) := by
  have key : ∀ A : C,
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo s (CH.ptsAug j G₁ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo (s ^ 3) (CH.ptsAug j G₂ A)) ∧
      ((CH.cx (CH.elF (CH.pts j A) (j ⋙ G₂))).ResUpTo s (CH.ptsAug j G₂ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₃))).ResUpTo s (CH.ptsAug j G₃ A) →
        (CH.cx (CH.elF (CH.pts j A) (j ⋙ G₁))).ResUpTo (s ^ 3) (CH.ptsAug j G₁ A)) := by
    intro A
    let a := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j α)
    let b := Functor.whiskerLeft (CategoryOfElements.π (CH.pts j A)) (Functor.whiskerLeft j β)
    obtain ⟨h1, h2, h3⟩ := CrystallineSemistableComparison.P.ses_cochains a b (fun X => hi _) (fun X => he _) (fun X => hs _)
    obtain ⟨k1, k2, -⟩ := CrystallineSemistableComparison.P.res_2of3 _ _ h1 h2 h3 (α.app A).hom (β.app A).hom (hi A) (he A) (hs A)
      (CH.ptsAug j G₁ A) (CH.ptsAug j G₂ A) (CH.ptsAug j G₃ A)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (α.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => funext fun t => (congrArg (fun φ => ModuleCat.Hom.hom φ x) (β.naturality (t.obj (Fin.last 0)).2)).symm)
      (fun x => ptsAug_d j G₂ A x) s
    exact ⟨k1, k2⟩
  exact ⟨fun h1 h3 A => (key A).1 (h1 A) (h3 A), fun h2 h3 A => (key A).2 (h2 A) (h3 A)⟩

theorem des_ses {R R₁ R₂ R₃ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing R₃] (σ₁ : R →+* R₁) (σ₂ : R →+* R₂) (σ₃ : R →+* R₃)
    {C : Type u} [Category.{v} C] {T : Type u'} [Category.{v'} T] (j : T ⥤ C)
    (F₁ : C ⥤ ModuleCat.{w} R₁) (F₂ : C ⥤ ModuleCat.{w} R₂) (F₃ : C ⥤ ModuleCat.{w} R₃)
    (α : ∀ A : C, F₁.obj A →+ F₂.obj A) (β : ∀ A : C, F₂.obj A →+ F₃.obj A)
    (hα : ∀ A (a : R) x, α A (σ₁ a • x) = σ₂ a • α A x) (hβ : ∀ A (a : R) x, β A (σ₂ a • x) = σ₃ a • β A x)
    (nα : ∀ {A B : C} (f : A ⟶ B) x, α B ((F₁.map f).hom x) = (F₂.map f).hom (α A x))
    (nβ : ∀ {A B : C} (f : A ⟶ B) x, β B ((F₂.map f).hom x) = (F₃.map f).hom (β A x))
    (hi : ∀ A, Function.Injective (α A)) (he : ∀ A, Function.Exact (α A) (β A)) (hs : ∀ A, Function.Surjective (β A)) (s : R) :
    (DesJ j F₁ (σ₁ s) → DesJ j F₃ (σ₃ s) → DesJ j F₂ (σ₂ (s ^ 3))) ∧
    (DesJ j F₂ (σ₂ s) → DesJ j F₃ (σ₃ s) → DesJ j F₁ (σ₁ (s ^ 3))) := by
  have key := des_ses_nat j (natRes σ₁ σ₂ F₁ F₂ α hα nα) (natRes σ₂ σ₃ F₂ F₃ β hβ nβ)
    (fun A x y h => hi A h) (fun A y => he A y) (fun A y => hs A y) s
  refine ⟨fun h1 h3 => ?_, fun h2 h3 => ?_⟩
  · exact (des_res σ₂ j F₂ (s ^ 3)).1 (key.1 ((des_res σ₁ j F₁ s).2 h1) ((des_res σ₃ j F₃ s).2 h3))
  · exact (des_res σ₁ j F₁ (s ^ 3)).1 (key.2 ((des_res σ₂ j F₂ s).2 h2) ((des_res σ₃ j F₃ s).2 h3))

end CrystallineSemistableComparison.D
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ToPfFull
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TensorProduct GroundTheory.PAdicHodge CrystallineSemistableComparison.CH

universe w v u v' u' v'' u''

namespace CrystallineSemistableComparison.D

variable (l : ℕ) [Fact l.Prime]

theorem isRt_rt : IsRt l (rt l) ∧ rt l 0 = pFlat l := by
  refine ⟨fun k => ?_, ?_⟩
  · apply (iterateFrobeniusEquiv (Ob l) l k).injective
    have h1 : iterateFrobeniusEquiv (Ob l) l (k + 1) (rt l (k + 1)) = pFlat l := RingEquiv.apply_symm_apply _ _
    have h2 : iterateFrobeniusEquiv (Ob l) l k (rt l k) = pFlat l := RingEquiv.apply_symm_apply _ _
    rw [h2, ← h1, iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def, ← pow_mul, pow_succ']
  · change (iterateFrobeniusEquiv (Ob l) l 0).symm (pFlat l) = pFlat l
    rw [iterateFrobeniusEquiv_zero]; rfl

theorem toPf_full : (toPf l).Full ∧ (toPf l).Faithful := by
  refine ⟨⟨fun {A B} φ => ⟨⟨φ.hom.hom.toRingHom, RingHom.ext fun c => φ.hom.hom.commutes c⟩, ?_⟩⟩,
    ⟨fun {A B} f g h => ?_⟩⟩
  · exact InducedCategory.hom_ext (CommAlgCat.hom_ext (AlgHom.ext fun x => rfl))
  · have h' := congrArg (fun φ => φ.hom.hom.toRingHom) h
    exact PAlg.Hom.ext h'

end CrystallineSemistableComparison.D
end
end

