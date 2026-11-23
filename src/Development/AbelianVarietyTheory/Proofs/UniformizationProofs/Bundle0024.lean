module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.TorusPointForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsZeroOfIsAddSelf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtPointsCompare

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

section Cast

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}

def castGen (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) := h ▸ t

theorem castGen_isGen (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (castGen h t).IsGen := by
  subst h; exact ht

theorem castGen_castGen (h : φ = φ') (h' : φ' = φ) (t : LB.Gen (LB.LinComb L φ ε)) :
    castGen h' (castGen h t) = t := by
  subst h; rfl

theorem corr_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) (u : LB.Gen (LB.LinComb L ψ δ)) :
    LB.Gen.Corr L _ _ _ _ (castGen h t) u ↔ LB.Gen.Corr L _ _ _ _ t u := by
  subst h; rfl

theorem corr_mul_castGen {K' : Type} [Fintype K'] {ψ : K' → (Y ⟶ X)} {δ : K' → ℤ}
    {φ₁ φ₁' φ₂ φ₂' : K → (Y ⟶ X)} (h : φ = φ') (h₁ : φ₁ = φ₁') (h₂ : φ₂ = φ₂')
    (t : LB.Gen (LB.LinComb L φ ε)) (c : LB.Gen (LB.LinComb L ψ δ))
    (t₁ : LB.Gen (LB.LinComb L φ₁ ε)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε)) :
    LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (castGen h t) c)
        (LB.mulGen L _ _ _ _ (castGen h₁ t₁) (castGen h₂ t₂)) ↔
      LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t c) (LB.mulGen L _ _ _ _ t₁ t₂) := by
  subst h h₁ h₂; rfl

end Cast

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem oφ_eq (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : oφ D b χ = DegPre.gtφ D F b χ := by
  have : padd D.P.A b (cPt D _ χ) = padd D.P.A (DegPre.cF D F χ) b := mul_comm b (cPt D _ χ)
  unfold oφ DegPre.gtφ
  rw [this]; rfl

theorem corr_one_of_mult (b : TF (R := R) F ⟶ D.P.A)
    (s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b 0) DegPre.gtε))
    (s' : LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b (0 + 0)) DegPre.gtε)) (hs : HEq s' s)
    (m : LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ s' (DegPre.cubAt D F (DegPre.cF D F 0) (DegPre.cF D F 0) b))
      (LB.mulGen D.P.L _ _ _ _ s s)) :
    LB.Gen.Corr D.P.L _ _ _ _ s (LB.oneGen D.P.L) := by
  revert s'
  rw [add_zero (0 : D.X)]
  intro s' hs m
  obtain rfl := eq_of_heq hs
  refine corr_of_val D.P.isLB fun y J hJ => Eq.trans ?_ (val_one _).symm
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  have e := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_cubAt hJ _ _ _))).symm.trans
      ((val_corr hJ m _).trans (val_mul hJ _ _ _))
  have z : DegPre.cF D F 0 = 1 := cPoint_zero _
  rw [z, C.face] at e
  exact (mul_left_cancel e).symm

def ptEquiv : GtPt D F ≃ GtPtF D F where
  toFun g :=
    { b := g.base
      s := fun χ => castGen (oφ_eq D F g.base χ) (g.form χ)
      isGen := fun χ => castGen_isGen _ (g.form_gen χ)
      s_zero := corr_one_of_mult D F g.base _ (castGen (oφ_eq D F g.base (0 + 0)) (g.form (0 + 0)))
        (by rw [add_zero (0 : D.X)])
        ((corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul 0 0))
      mult := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.form_mul χ χ') }
  invFun g :=
    { base := g.b
      form := fun χ => castGen (oφ_eq D F g.b χ).symm (g.s χ)
      form_gen := fun χ => castGen_isGen _ (g.isGen χ)
      form_mul := fun χ χ' => (corr_mul_castGen _ _ _ _ _ _ _).2 (g.mult χ χ') }
  left_inv g := by
    obtain ⟨b, s, h₁, h₂⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _
  right_inv g := by
    obtain ⟨b, s, h₁, h₂, h₃⟩ := g
    dsimp only
    congr 1
    exact funext fun χ => castGen_castGen _ _ _

variable {D F}

theorem isZero_iff (g : GtPt D F) : (ptEquiv D F g).IsZero ↔ g.IsZero :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)

theorem isAdd_iff (g g' h : GtPt D F) :
    (ptEquiv D F g).IsAdd (ptEquiv D F g') (ptEquiv D F h) ↔ g.IsAdd g' h :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_mul_castGen _ _ _ _ _ _ _)

theorem isIota_iff (y : D.X) (g : GtPt D F) :
    GtPtF.IsIota y (ptEquiv D F g) ↔ GtPt.IsIo y g :=
  and_congr Iff.rfl (forall_congr' fun _ => corr_castGen _ _ _)

theorem isNsmul_iff (k : ℕ) (g h : GtPt D F) :
    GtPtF.IsNsmul k (ptEquiv D F g) (ptEquiv D F h) ↔ g.IsNsmul k h := by
  constructor
  · rintro ⟨gs, h0, hs, hl⟩
    have key : ∀ (i : ℕ) (hi : i < k + 1), g.IsNsmul i ((ptEquiv D F).symm (gs ⟨i, hi⟩)) := by
      intro i
      induction i with
      | zero =>
        intro hi
        exact .zero _ ((isZero_iff _).1 (by rw [Equiv.apply_symm_apply]; exact h0))
      | succ i ih =>
        intro hi
        refine .succ i _ _ (ih (by omega)) ((isAdd_iff _ _ _).1 ?_)
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hs ⟨i, by omega⟩
    have := key k (Nat.lt_succ_self k)
    rwa [show gs ⟨k, Nat.lt_succ_self k⟩ = ptEquiv D F h from hl, Equiv.symm_apply_apply] at this
  · intro H
    induction H with
    | zero h hz => exact ⟨fun _ => ptEquiv D F h, (isZero_iff h).2 hz, fun i => i.elim0, rfl⟩
    | succ k h h' _ ha ih =>
      obtain ⟨gs, h0, hs, hl⟩ := ih
      refine ⟨Fin.snoc (α := fun _ => GtPtF D F) gs (ptEquiv D F h'), ?_, fun i => ?_, ?_⟩
      · rw [← Fin.castSucc_zero, Fin.snoc_castSucc]; exact h0
      · rw [Fin.snoc_castSucc]
        refine Fin.lastCases ?_ (fun j => ?_) i
        · rw [Fin.succ_last, Fin.snoc_last, hl]; exact (isAdd_iff _ _ _).2 ha
        · rw [Fin.succ_castSucc, Fin.snoc_castSucc]; exact hs j
      · rw [Fin.snoc_last]

variable (D F)

theorem exists_nsmul_iff (k : ℕ) (y : D.X) (g : GtPt D F) :
    (∃ h : GtPtF D F, GtPtF.IsNsmul k (ptEquiv D F g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h := by
  constructor
  · rintro ⟨h, h₁, h₂⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨w, (isNsmul_iff _ _ _).1 h₁, (isIota_iff _ _).1 h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    exact ⟨ptEquiv D F h, (isNsmul_iff _ _ _).2 h₁, (isIota_iff _ _).2 h₂⟩

theorem qkPt_ext {k : ℕ} {q q' : QkPt D F k} (h₁ : q.y = q'.y) (h₂ : q.g = q'.g) : q = q' := by
  obtain ⟨y, g, h⟩ := q
  obtain ⟨y', g', h'⟩ := q'
  obtain rfl : y = y' := h₁
  obtain rfl : g = g' := h₂
  rfl

def pairEquivOf (k : ℕ) (e : GtPt D F ≃ GtPtF D F)
    (H : ∀ y g, (∃ h : GtPtF D F, GtPtF.IsNsmul k (e g) h ∧ GtPtF.IsIota y h) ↔
      ∃ h : GtPt D F, g.IsNsmul k h ∧ GtPt.IsIo y h) : QPair D F k ≃ QkPt D F k where
  toFun p := ⟨p.1.1, e p.1.2, (H _ _).2 p.2⟩
  invFun q := ⟨(q.y, e.symm q.g), (H _ _).1 (by rw [Equiv.apply_symm_apply]; exact q.eq)⟩
  left_inv p := Subtype.ext (Prod.ext rfl (Equiv.symm_apply_apply e p.1.2))
  right_inv q := qkPt_ext D F rfl (Equiv.apply_symm_apply e q.g)

def pairEquiv (k : ℕ) : QPair D F k ≃ QkPt D F k :=
  pairEquivOf D F k (ptEquiv D F) (exists_nsmul_iff D F k)

variable {D F}

theorem rel_iff {k : ℕ} (p p' : QPair D F k) :
    QkPt.Equiv D F (pairEquiv D F k p) (pairEquiv D F k p') ↔ QRel D F k p p' := by
  constructor
  · rintro ⟨z, hz, h, hi, ha⟩
    obtain ⟨w, rfl⟩ := (ptEquiv D F).surjective h
    exact ⟨z, w, (isIota_iff _ _).1 hi, hz, (isAdd_iff _ _ _).1 ha⟩
  · rintro ⟨z, w, hi, hz, ha⟩
    exact ⟨z, hz, ptEquiv D F w, (isIota_iff _ _).2 hi, (isAdd_iff _ _ _).2 ha⟩

variable (D F)

variable {D F}

variable (D F)

end GlobalTheory.GtPointsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ScalCompSpecMap
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace ExpandsLinear

def scalOn {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) :
    R →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem scalOn_apply {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (W : Y.Opens) (r : R) : resTop W (scal p r) = scalOn p W r := rfl

theorem scal_comp_specMap {R C : Type} [CommRing R] [CommRing C] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of C)) (φ : R →+* C) (r : R) :
    scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
  unfold scal
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 1
  have := congrArg (fun g => g.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

theorem app_resTop_scal {R : Type} [CommRing R] {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) (r : R) :
    (h.app W).hom (resTop W (scal p r)) = resTop _ (scal (h ≫ p) r) := by
  simp only [resTop]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.naturality, CommRingCat.hom_comp,
    RingHom.comp_apply]
  rfl

def secComb {Y : Scheme.{0}} {L : LB Y} {n : ℕ} (a : Fin n → Γ(Y, ⊤)) (s : Fin n → LB.Sec L) : LB.Sec L where
  f := fun j => ∑ i, resTop _ (a i) * (s i).f j
  compat := fun j j' => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (SecOps.secScale (a i) (s i)).compat j j'

theorem secScal_comb {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {X Y Y' : Scheme.{0}} (L : LB X)
    {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ)
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (h : Y' ⟶ Y) (π : Y' ⟶ Spec (CommRingCat.of C))
    (π' : Y' ⟶ Spec (CommRingCat.of R)) (p : Y ⟶ Spec (CommRingCat.of R))
    (hπ : π' = π ≫ Spec.map (CommRingCat.ofHom φ)) (hp : h ≫ p = π') {n : ℕ}
    (s : Fin n → LB.Sec (LB.LinComb L φ₁ ε₁)) (t : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (r a : Fin n → R) (d : R) (c : Fin n → C) (hc : ∀ i, φ (a i) * φ (r i) = φ d * c i)
    (H : ∀ i, GeneratorPullback.SecScal L φ₁ ε₁ (s i) φ₂ ε₂ (t i) h (scal π' (r i)))
    (s₀ : LB.Sec (LB.LinComb L φ₁ ε₁)) (hs : ∀ j, s₀.f j = ∑ i, resTop _ (scal π (c i)) * (s i).f j) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₀ φ₂ ε₂ (secComb (fun i => scal p (a i)) t) h (scal π' d) := by
  intro j₁ j₂ hco
  erw [hs]
  dsimp only [secComb]
  erw [map_sum, map_sum, map_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have Hi := H i j₁ j₂ hco
  erw [map_mul, map_mul, map_mul, Hi, app_resTop_scal, SecOps.resTop_res, SecOps.resTop_res]
  rw [hp, hπ, scal_comp_specMap, scal_comp_specMap, scal_comp_specMap, ← _root_.mul_assoc, ← _root_.mul_assoc]
  simp only [scalOn_apply]
  rw [← map_mul, hc, map_mul]

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {N : Type} (S : Finset N) (s : N → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_f, ih]

end ExpandsLinear


open ExpandsLinear in
theorem expands_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (b : Fin n → U.SecK k) (F : Fin n → Fam D.toPre (FractionRing R) k) (c : Fin n → FractionRing R) (s : U.SecK k), (∀ i, U.Expands k (b i) (F i)) → (∀ j, (s).f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) → U.Expands k s (∑ i, c i • F i) := by
  intro R _ _ I _ D A G _ _ _ U k n b F c s hE hs
  choose r hr σ f hσ hf hE using hE
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun i => c i / algebraMap R (FractionRing R) (r i))
  choose a ha using hd
  have hc : ∀ i, algebraMap R (FractionRing R) (a i) * algebraMap R (FractionRing R) (r i) =
      algebraMap R (FractionRing R) d * c i := fun i => by
    have h0 : algebraMap R (FractionRing R) (r i) ≠ 0 :=
      fun h => hr i ((IsFractionRing.injective R (FractionRing R)) (h.trans (map_zero _).symm))
    rw [ha i, Algebra.smul_def, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  refine ⟨d, nonZeroDivisors.ne_zero d.2, ExpandsLinear.secComb (fun i => scal G.hom (a i)) σ,
    fun α => ExpandsLinear.secComb (fun i => scal D.toPre.P.A.hom (a i)) (fun i => f i α), ?_, fun α => ?_, fun e => ?_⟩
  · exact ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _ (pullback.snd G.hom (jK R)) _ G.hom rfl
      pullback.condition b σ r a d c hc hσ s hs
  · refine ExpandsLinear.secScal_comb (algebraMap R (FractionRing R)) _ _ _ _ _ _
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left _ D.toPre.P.A.hom ?_
      (Over.w (DegPre.prB D.toPre (FractionRing R))) (fun i => (F i).s α) (fun i => f i α) r a d c hc
      (fun i => hf i α) _ fun j => ?_
    · rw [← Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)]
      congr 1
      change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    · rw [ExpandsLinear.fam_sum_f]
      rfl
  · exact expandsAt_linear R I D A G U k e n a σ f _ _ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_relation_descends : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (z : (T' ⊗ B).left) (J), Good L z J → gs (ψ ▷ B).left z ⊤ c' * sval s' (ψ ▷ B).left z J = gs (ψ ▷ B).left z ⊤ c * (sval s ((ψ ▷ B).left ≫ τ) z J * (val u (ψ ▷ B).left z J).val)) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro S B T T' _ _ _ ψ hψ X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := _root_.GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero S B T T' ψ hψ X L hL K' φ' ε' d
    (fun z J hJ => (hd _ _ z J hJ).trans (sub_eq_zero.2 (h z J hJ)))
  refine sub_eq_zero.1 ((hd Z r z J hJ).symm.trans ?_)
  refine (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

end GlobalTheory
end

