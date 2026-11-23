module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionPowerCalculusGeometricFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.Calc
open GlobalTheory.FrameGen GlobalTheory.ConstFam

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L' : LB G'.left}
  {L : LB G.left} {w : LB.Iso L' (L.pull φ)} {k : ℕ} {T' : Over S'} {T T₁ : Over S}

theorem prod_ext' {Z : Scheme.{0}} {a b : Z ⟶ (T ⊗ G).left} (h₁ : a ≫ (fst T G).left = b ≫ (fst T G).left)
    (h₂ : a ≫ (snd T G).left = b ≫ (snd T G).left) : a = b := pullback.hom_ext h₁ h₂

theorem exists_lift {Z : Scheme.{0}} (a : Z ⟶ T.left) (b : Z ⟶ G.left) (e : a ≫ T.hom = b ≫ G.hom) :
    ∃ H : Z ⟶ (T ⊗ G).left, H ≫ (fst T G).left = a ∧ H ≫ (snd T G).left = b :=
  ⟨pullback.lift a b e, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem prod_w : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := (Over.w _).trans (Over.w _).symm

theorem exists_prod (hφ : φ ≫ G.hom = G'.hom ≫ f) {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) :
    ∃ H : (T' ⊗ G').left ⟶ (T ⊗ G).left, H ≫ (fst T G).left = (fst T' G').left ≫ h ∧
      H ≫ (snd T G).left = (snd T' G').left ≫ φ :=
  exists_lift _ _ (by rw [Category.assoc, Category.assoc, hh, hφ, ← Category.assoc, ← Category.assoc, prod_w])

theorem thru_sv {h : T'.left ⟶ T.left} {s : LB.Sec (LPow G L (k : ℤ) T)} {s' : LB.Sec (LPow G' L' (k : ℤ) T')}
    (H : Thru w k h s s') {Z : Scheme.{0}} (r' : Z ⟶ (T' ⊗ G').left) (r : Z ⟶ (T ⊗ G).left)
    (h₁ : r ≫ (fst T G).left = r' ≫ (fst T' G').left ≫ h) (h₂ : r ≫ (snd T G).left = r' ≫ (snd T' G').left ≫ φ)
    (z : Z) {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sv G L k s r z J = (wVal w z J J' (r' ≫ (snd T' G').left) ^ k).val * sv G' L' k s' r' z J' := by
  rw [Units.val_pow_eq_pow_val]
  exact H Z r' r h₁ h₂ z J J' hJ hJ'

theorem existsUnique_thru (hφ : φ ≫ G.hom = G'.hom ≫ f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {h : T'.left ⟶ T.left} (hh : h ≫ T.hom = T'.hom ≫ f) (s : LB.Sec (LPow G L (k : ℤ) T)) :
    ∃! t : LB.Sec (LPow G' L' (k : ℤ) T'), Thru w k h s t := by
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hh
  obtain ⟨t, ht⟩ := exists_secThrough (φ' := fun _ : Fin 1 => (snd T' G').left)
    (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (h := H) hw hL hL' (fun _ => h₂.symm) s
  have key : Thru w k h s t := fun Z r' r e₁ e₂ z J J' hJ hJ' => by
    obtain rfl : r = r' ≫ H := prod_ext' (by rw [Category.assoc, h₁, e₁]) (by rw [Category.assoc, h₂, e₂])
    have a := ht.sval (fun _ => h₂.symm) r' hJ hJ'
    rwa [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val] at a
  refine ⟨t, key, fun t' ht' => SecOps.sec_ext (sec_ext_val hL' fun y J' hJ' => ?_)⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e₁ : H ≫ (fst T G).left = 𝟙 _ ≫ (fst T' G').left ≫ h := by rw [Category.id_comp, h₁]
  have e₂ : H ≫ (snd T G).left = 𝟙 _ ≫ (snd T' G').left ≫ φ := by rw [Category.id_comp, h₂]
  exact (Units.mul_right_inj _).1 ((thru_sv ht' _ H e₁ e₂ y hJ hJ').symm.trans (thru_sv key _ H e₁ e₂ y hJ hJ'))

theorem cmb_iff (hL : L.IsLB) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (k : ℤ) T)) (a : Fin n → Γ(T.left, ⊤))
    (t : LB.Sec (LPow G L (k : ℤ) T)) :
    ((∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J) ∧
    ((∀ (z : (T ⊗ G).left) (J), Good L z J →
      sv G L k t (𝟙 _) z J = ∑ i, gT (𝟙 _ ≫ (fst T G).left) z (a i) * sv G L k (b i) (𝟙 _) z J) →
      ∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) := by
  have key : ∀ t : LB.Sec (LPow G L (k : ℤ) T), (∀ j, t.f j = ∑ i, liftFun G _ (a i) * (b i).f j) →
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ G).left) (z : Z) (J), Good L z J →
      sv G L k t r z J = ∑ i, gT (r ≫ (fst T G).left) z (a i) * sv G L k (b i) r z J := fun t H Z r z J hJ =>
    (SectionScalarValuation.sval_lin (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (k : ℤ)) (s := t)
      (fun i => (fst T G).left.appTop.hom (a i)) b H r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ((gs_top _ _ _).trans (gT_comp _ _ _ _)) rfl)
  refine ⟨key t, fun H j => ?_⟩
  let σ := SectionLimit.linSec (fun i => (fst T G).left.appTop.hom (a i)) b
  exact sec_ext_val (s := t) (s' := σ) hL (fun y J hJ => (H y J hJ).trans (key σ (fun _ => rfl) _ _ y J hJ).symm) j

theorem cmb_of_lin (hφ : φ ≫ G.hom = G'.hom ≫ f) (hL : L.IsLB) (hL' : L'.IsLB) {g : T'.left ⟶ T₁.left}
    (hg : g ≫ T₁.hom = T'.hom ≫ f) {h : T₁ ⟶ T} {p : T'.left ⟶ T.left} (hp : p = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {c : Fin n → Γ(T₁.left, ⊤)} {s : LB.Sec (LPow G L (k : ℤ) T₁)}
    {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')} {t : LB.Sec (LPow G' L' (k : ℤ) T')} (hl : Lin G L k h b c s)
    (hb : ∀ i, Thru w k p (b i) (b' i)) (ht : Thru w k g s t) :
    ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  subst hp
  refine (cmb_iff hL' b' _ t).2 fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL z
  obtain ⟨H, h₁, h₂⟩ := exists_prod hφ hg
  have e := lin_all hL hl H z hJ
  rw [thru_sv ht (𝟙 _) H (by rw [Category.id_comp, h₁]) (by rw [Category.id_comp, h₂]) z hJ hJ'] at e
  refine (Units.mul_right_inj _).1 (e.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [thru_sv (hb i) (𝟙 _) (H ≫ (h ▷ G).left)
    (by rw [Category.id_comp, Category.assoc, wh_fst, ← Category.assoc, h₁, Category.assoc])
    (by rw [Category.id_comp, Category.assoc, wh_snd, h₂]) z hJ hJ', gT_comp, h₁, Category.id_comp,
    Category.id_comp, mul_left_comm]

theorem exists_thru_up (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _) :
    ∃ H : (T₁ ⊗ G).left ⟶ (T' ⊗ G').left, H ≫ (fst T' G').left ≫ g = (fst T₁ G).left ∧
      H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left ∧
      ∀ t : LB.Sec (LPow G' L' (k : ℤ) T'), ∃ s : LB.Sec (LPow G L (k : ℤ) T₁), Thru w k g s t := by
  have hp : (snd T₁ G).left ≫ G.hom = (((fst T₁ G).left ≫ p) ≫ T'.hom) ≫ f := by
    rw [Category.assoc, ← hg, Category.assoc, ← Category.assoc p, pg, Category.id_comp, prod_w]
  obtain ⟨H, h₁, h₂⟩ := exists_lift (T := T') (G := G') ((fst T₁ G).left ≫ p) (hφ.lift _ _ hp) (hφ.lift_snd _ _ hp).symm
  have h₃ : H ≫ (snd T' G').left ≫ φ = (snd T₁ G).left := by rw [← Category.assoc, h₂, hφ.lift_fst]
  refine ⟨H, by rw [← Category.assoc, h₁, Category.assoc, pg, Category.comp_id], h₃, fun t => ?_⟩
  obtain ⟨t₁, ht₁⟩ := exists_sec_up (φ' := fun _ : Fin 1 => (snd T' G').left) (ε := fun _ => (k : ℤ))
    ((isGen_iff w).1 hw) hL hL' t
  obtain ⟨s, -, hs⟩ := SectionLimit.exists_pull t₁ H (fun _ : Fin 1 => (snd T₁ G).left) (fun _ => h₃)
  refine ⟨s, fun Z r' r e₁ e₂ z J J' hJ hJ' => ?_⟩
  have e₁' : r ≫ H ≫ (fst T' G').left = r' ≫ (fst T' G').left := by
    rw [h₁, ← Category.assoc, e₁, Category.assoc, Category.assoc, gp, Category.comp_id]
  have e : r ≫ H = r' := prod_ext' (by rw [Category.assoc, e₁']) (hφ.hom_ext
    (by rw [Category.assoc, Category.assoc, h₃, e₂, Category.assoc])
    (by rw [Category.assoc, Category.assoc, Category.assoc, ← prod_w, ← Category.assoc H, ← Category.assoc, e₁',
      Category.assoc]))
  have ST : SecThrough w (fun _ : Fin 1 => (snd T' G').left) (fun _ => (snd T' G').left ≫ φ) (fun _ => (k : ℤ)) t t₁
      (𝟙 _) := fun Z r z p q hp hq => by
    rw [Category.comp_id]
    exact ht₁ Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)
  have a := ST.sval (fun _ => (Category.id_comp _).symm) r' hJ hJ'
  rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, Category.comp_id] at a
  exact (hs Z r z J hJ).trans ((congrArg (fun q => sval t₁ q z J) e).trans a)

theorem basis_thru (hφ : IsPullback φ G'.hom G.hom f) (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB)
    {g : T'.left ⟶ T₁.left} {p : T₁.left ⟶ T'.left} (hg : g ≫ T₁.hom = T'.hom ≫ f) (gp : g ≫ p = 𝟙 _) (pg : p ≫ g = 𝟙 _)
    {h : T₁ ⟶ T} {q : T'.left ⟶ T.left} (hq : q = g ≫ h.left) {n : ℕ}
    {b : Fin n → LB.Sec (LPow G L (k : ℤ) T)} {b' : Fin n → LB.Sec (LPow G' L' (k : ℤ) T')}
    (hB : BasisAlong G L k h b) (hb : ∀ i, Thru w k q (b i) (b' i)) (t : LB.Sec (LPow G' L' (k : ℤ) T')) :
    ∃! c : Fin n → Γ(T₁.left, ⊤), ∀ j, t.f j = ∑ i, liftFun G' _ (g.appTop.hom (c i)) * (b' i).f j := by
  obtain ⟨H, h₁, h₃, hs⟩ := exists_thru_up (k := k) hφ hw hL hL' hg gp pg
  obtain ⟨s, hst⟩ := hs t
  obtain ⟨c, hc, hu⟩ := hB s
  refine ⟨c, cmb_of_lin hφ.w hL hL' hg hq hc hb hst, fun c' hc' => hu c' fun z J hJ => ?_⟩
  subst hq
  obtain ⟨J', hJ'⟩ := exists_good' hL' z
  have a := thru_sv hst H (𝟙 _) ((Category.id_comp _).trans h₁.symm) ((Category.id_comp _).trans h₃.symm) z hJ hJ'
  refine a.trans ?_
  rw [(cmb_iff hL' b' _ t).1 hc' _ H z J' hJ', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have d := thru_sv (hb i) H (h ▷ G).left (by rw [wh_fst, ← h₁]; simp only [Category.assoc]) (by rw [wh_snd, h₃]) z hJ hJ'
  rw [mul_left_comm, ← d, gT_comp, Category.assoc, h₁]
  exact congrArg₂ (· * ·) (gs_top _ _ _).symm rfl

theorem appTop_fnR {R F : Type} [CommRing R] [CommRing F] (y : R →+* F) (c : R) :
    (spMap y).appTop.hom (fnR c) = fnR (y c) :=
  (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))).symm

theorem main : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] (L₀ : LB G₀.left), L₀.IsLB → ∀ (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ Z) (A : PolAV (Sp (FractionRing R))) (φ : A.A.left ⟶ G₀.left) (w : LB.Iso A.L (L₀.pull φ)), IsGrpPullback A.A G₀ x φ → w.IsGen → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (T : Over Z) (p : Sp F ⟶ T.left), p ≫ T.hom = jFK (R := R) F ≫ x → ∀ s : LB.Sec (LPow G₀ L₀ (k : ℤ) T), ∃! t : SecA A F k, Thru w k (T' := TFK (R := R) F) p s t) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Z) (T : Over Z) (h : Over.mk y ⟶ T) (ga : R' →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (b : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) T)) (c : Fin n → R') (s : LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (bF : Fin n → SecA A F k) (t : SecA A F k), Lin G₀ L₀ k h b (fun i => fnR (c i)) s → (∀ i, Thru w k (T' := TFK (R := R) F) (spMap ga ≫ h.left) (b i) (bF i)) → Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) s t → Cmb bF (fun i => ga (c i)) t) ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Z) (ga : K →+* F), spMap ga ≫ y = jFK (R := R) F ≫ x → ∀ (n : ℕ) (τ : Fin n → LB.Sec (LPow G₀ L₀ (k : ℤ) (Over.mk y))) (τF : Fin n → SecA A F k), AllBasis G₀ L₀ k y τ → (∀ i, Thru w k (T' := TFK (R := R) F) (T := Over.mk y) (spMap ga) (τ i) (τF i)) → ∀ t : SecA A F k, ∃! a : Fin n → F, Cmb τF a t := by
  intro Z G₀ _ L₀ hL R _ _ x A φ w gp hw F _ _ k
  refine ⟨fun T p hp s => existsUnique_thru (T' := TFK (R := R) F) gp.1.w hw hL A.isLB hp s,
    fun R' _ y T h ga e n b c s bF t hl hb ht j => ?_, fun K _ y ga e n τ τF hB hτ t => ?_⟩
  · have := cmb_of_lin (T' := TFK (R := R) F) (T₁ := Over.mk y) (g := spMap ga) gp.1.w hL A.isLB e rfl hl hb ht j
    exact this.trans (Finset.sum_congr rfl fun i _ =>
      congrArg (fun q => liftFun A.A _ q * (bF i).f j) (appTop_fnR ga (c i)))
  · obtain ⟨c, hc, hu⟩ := basis_thru (T' := TFK (R := R) F) (T₁ := Over.mk (jFK (R := R) F ≫ x)) (g := 𝟙 (Sp F))
      (p := 𝟙 (Sp F)) gp.1 hw hL A.isLB (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)
      (Category.id_comp _).symm (hB F ga _ e) hτ t
    let ε := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm
    refine ⟨fun i => ε.symm (c i), fun j => (hc j).trans (Finset.sum_congr rfl fun i _ => ?_), fun a ha => funext fun i => ?_⟩
    · exact congrArg (fun q => liftFun A.A _ q * (τF i).f j) (ε.apply_symm_apply (c i)).symm
    · exact ε.eq_symm_apply.2 (congrFun (hu (fun i => ε (a i)) ha) i)

end GlobalTheory.OneBasis.Calc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ShortestRepresentativesFormSumDependsOnLattice
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

namespace GlobalTheory.OneBasis.ShortSum

variable {X : Type} [AddCommGroup X]

abbrev mulSub (X : Type) [AddCommGroup X] (k : ℕ) : AddSubgroup X := (nsmulAddMonoidHom (α := X) k).range

theorem mk_eq_iff (k : ℕ) (a b : X) :
    (QuotientAddGroup.mk a : X ⧸ mulSub X k) = QuotientAddGroup.mk b ↔ ∃ z, b = a + k • z := by
  rw [QuotientAddGroup.eq]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have : k • z = -a + b := hz
    rw [this]; abel
  · rintro ⟨z, rfl⟩
    exact ⟨z, by simp⟩

theorem surj {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Function.Surjective (fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)) := by
  intro c
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨i, z, hz⟩ := h.2.2.1 a
  exact ⟨i, (mk_eq_iff k _ _).2 ⟨z, hz⟩⟩

theorem sum_comp {k r mu : ℕ} {Q : X → ℤ} {cls : Fin r → X} (h : Adapted k Q cls mu)
    [Fintype (X ⧸ mulSub X k)] (g : X ⧸ mulSub X k → ℤ) :
    ∑ i, g (QuotientAddGroup.mk (cls i)) = mu * ∑ c, g c := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun i => (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨i₀, rfl⟩ := surj h c
  rw [Finset.sum_congr rfl (g := fun _ => g (QuotientAddGroup.mk (cls i₀)))
    (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← h.2.2.2 i₀, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.filter_congr fun i _ => ⟨fun hi => ?_, fun hi => by simp only [hi]⟩
  exact h.2.1 i i₀ ((mk_eq_iff k _ _).1 hi.symm)

theorem val_eq {k r r' mu mu' : ℕ} {Q : X → ℤ} {cls : Fin r → X} {cls' : Fin r' → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') {i : Fin r} {i' : Fin r'}
    (e : (QuotientAddGroup.mk (cls i) : X ⧸ mulSub X k) = QuotientAddGroup.mk (cls' i')) :
    Q (cls i) = Q (cls' i') := by
  apply le_antisymm
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e
    rw [hz]; exact h.1 i z
  · obtain ⟨z, hz⟩ := (mk_eq_iff k _ _).1 e.symm
    rw [hz]; exact h'.1 i' z

theorem sum_eq {k r mu mu' : ℕ} {Q : X → ℤ} {cls cls' : Fin r → X} (h : Adapted k Q cls mu)
    (h' : Adapted k Q cls' mu') : ∑ i, Q (cls i) = ∑ i, Q (cls' i) := by
  haveI : Finite (X ⧸ mulSub X k) := Finite.of_surjective _ (surj h)
  letI : Fintype (X ⧸ mulSub X k) := Fintype.ofFinite _
  have a := sum_comp h (fun _ => 1)
  have a' := sum_comp h' (fun _ => 1)
  have hm : (mu : ℤ) = mu' := by
    have hp : (∑ _c : X ⧸ mulSub X k, (1 : ℤ)) ≠ 0 := by simp
    exact mul_right_cancel₀ hp (a.symm.trans a')
  have b := sum_comp h (fun c => Q (cls (Function.surjInv (surj h) c)))
  have b' := sum_comp h' (fun c => Q (cls (Function.surjInv (surj h) c)))
  calc ∑ i, Q (cls i) = _ := Finset.sum_congr rfl fun i _ =>
        val_eq h h (Function.surjInv_eq (surj h) _).symm
    _ = _ := b
    _ = _ := by rw [hm]
    _ = _ := b'.symm
    _ = _ := Finset.sum_congr rfl fun i _ => val_eq h h' (Function.surjInv_eq (surj h) _)

theorem transport {X₀ : Type} [AddCommGroup X₀] {q₀ : X₀ → ℤ} {Q : X → ℤ} (e : X₀ ≃+ X) {w : ℕ} (hw : 0 < w)
    (hQ : ∀ y, Q (e y) = w * q₀ y) {k r mu : ℕ} {cls : Fin r → X} (h : Adapted k Q cls mu) :
    Adapted k q₀ (fun i => e.symm (cls i)) mu := by
  refine ⟨fun i z => ?_, fun i i' ⟨z, hz⟩ => ?_, fun α => ?_, fun i₀ => ?_⟩
  · have h1 := h.1 i (e z)
    have h2 := hQ (e.symm (cls i))
    have h3 := hQ (e.symm (cls i) + k • z)
    rw [map_add (f := _), map_nsmul] at h3
    rw [e.apply_symm_apply] at h2 h3
    rw [h2, h3] at h1
    exact le_of_mul_le_mul_left h1 (by exact_mod_cast hw)
  · have h1 := congrArg e hz
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply] at h1
    simp only [h.2.1 i i' ⟨_, h1⟩]
  · obtain ⟨i, z, hz⟩ := h.2.2.1 (e α)
    refine ⟨i, e.symm z, e.injective ?_⟩
    simp only [map_add (f := _), map_nsmul, e.apply_symm_apply]
    exact hz
  · rw [← h.2.2.2 i₀]
    simp only [e.symm.injective.eq_iff]

end GlobalTheory.OneBasis.ShortSum

namespace GlobalTheory.OneBasis

theorem sum_adapted_eq : ∀ (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (q₀ : X₀ → ℤ) (k r : ℕ), 1 ≤ k → (∀ y, 0 ≤ q₀ y) → ∃ d C : ℕ, 1 ≤ d ∧ ∀ (X : Type) [AddCommGroup X] (Q : X → ℤ) (e : X₀ ≃+ X) (w : ℕ), 0 < w → (∀ y, Q (e y) = w * q₀ y) → ∀ (cls : Fin r → X) (mu : ℕ), Adapted k Q cls mu → (d : ℤ) * ∑ i, Q (cls i) = C * w * k := by
  intro X₀ _ _ _ q₀ k r hk hq
  by_cases hex : ∃ (c₀ : Fin r → X₀) (m₀ : ℕ), Adapted k q₀ c₀ m₀
  · obtain ⟨c₀, m₀, h₀⟩ := hex
    refine ⟨k, (∑ i, q₀ (c₀ i)).toNat, hk, fun X _ Q e w hw hQ cls mu h => ?_⟩
    rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hq _),
      ShortSum.sum_eq h₀ (ShortSum.transport e hw hQ h)]
    have : ∑ i, Q (cls i) = w * ∑ i, q₀ (e.symm (cls i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hQ, e.apply_symm_apply]
    rw [this]; ring
  · exact ⟨k, 0, hk, fun X _ Q e w hw hQ cls mu h => (hex ⟨_, _, ShortSum.transport e hw hQ h⟩).elim⟩

end GlobalTheory.OneBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StalkUnitsSymmGm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch GlobalTheory.ArcPull GlobalTheory.FrameValue

noncomputable section
namespace GlobalTheory.Ex.Arch.FibRos

theorem exists_ros_down {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] [IsCommMonObj A]
    [IsCommMonObj A'] {f : S' ⟶ S} {Φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (gp : IsGrpPullback A' A f Φ) (hL : L.IsLB) (hL' : L'.IsLB)
    {w : LB.Iso L' (L.pull Φ)} (hw : w.IsGen) {a b : A ⟶ A} {a' b' : A' ⟶ A'}
    (a₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ a' = 1) (b₁ : (1 : 𝟙_ (Over S') ⟶ A') ≫ b' = 1)
    (ha : a'.left ≫ Φ = Φ ≫ a.left) (hb : b'.left ≫ Φ = Φ ≫ b.left)
    {r : LB.Gen (LB.LinComb L (rosatiφ A a b) rosatiε)} (hr : TorusExt.IsRos L a b r) :
    ∃ t : LB.Gen (LB.LinComb L' (rosatiφ A' a' b') rosatiε), TorusExt.IsRos L' a' b' t ∧
      ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
        y'.left ≫ Φ = m ≫ (snd A A).left → ∀ (z : T'.left) J J', Good L z J → Good L' z J' →
        val r m z J = (∏ k, om w z J J' ((lift x' y').left ≫ rosatiφ A' a' b' k) ^ rosatiε k) *
          val t (lift x' y').left z J' := by
  let Φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left := (lift (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A'))).left
  have f₁ : (fst A' A').left ≫ Φ = Φ₂ ≫ (fst A A).left :=
    (congrArg (fun q => q.left) (lift_fst (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₂ : (snd A' A').left ≫ Φ = Φ₂ ≫ (snd A A).left :=
    (congrArg (fun q => q.left) (lift_snd (pushPt gp.1.w (fst A' A')) (pushPt gp.1.w (snd A' A')))).symm
  have f₃ : (fst A' A' ≫ a').left ≫ Φ = Φ₂ ≫ (fst A A ≫ a).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, ha, ← Category.assoc, f₁, Category.assoc]
  have f₄ : (snd A' A' ≫ b').left ≫ Φ = Φ₂ ≫ (snd A A ≫ b).left := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, hb, ← Category.assoc, f₂, Category.assoc]
  have hψ : ∀ i, rosatiφ A' a' b' i ≫ Φ = Φ₂ ≫ rosatiφ A a b i := fun i => by
    fin_cases i
    exacts [mul_push gp Φ₂ f₃ f₂, f₃, f₂, mul_push gp Φ₂ f₁ f₄, f₁, f₄]
  have cmp : ∀ {T' : Over S'} (x' y' : T' ⟶ A') (m : T'.left ⟶ (A ⊗ A).left), x'.left ≫ Φ = m ≫ (fst A A).left →
      y'.left ≫ Φ = m ≫ (snd A A).left → (lift x' y').left ≫ Φ₂ = m := fun x' y' m hx hy => by
    apply pullback.hom_ext
    · refine Eq.trans ?_ hx
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₁.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_fst]
    · refine Eq.trans ?_ hy
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) f₂.symm).trans ?_)
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
  obtain ⟨t, ht, vt⟩ := exists_down_om hw hL hL' Φ₂ hψ r hr.1
  refine ⟨t, ⟨ht, corr_of_val hL' fun y I' hI' => ?_⟩, fun x' y' m hx hy z J J' hJ hJ' => ?_⟩
  · obtain ⟨I, hI⟩ := DegPull.exists_good' hL y
    have o : lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A') = lift η[A'] η[A'] := by simp [Hom.one_def]
    have he : eSec A' ≫ Φ = f ≫ eSec A := (cubeMapOf gp).e_comm
    have o₁ : (1 : 𝟙_ (Over S') ⟶ A').left = eSec A' := Category.id_comp _
    have e := vt _ (lift (1 : 𝟙_ (Over S') ⟶ A') (1 : 𝟙_ (Over S') ⟶ A')).left y I I' hI hI'
    rw [prod_ros, cmp 1 1 (f ≫ zero2 A) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_fst]; rfl) (by
        rw [o₁, he, Category.assoc, ← Over.comp_left, lift_snd]; rfl),
      a₁, b₁, _root_.mul_one, o] at e
    have e₁ := (val_pull hI _ _ _).symm.trans ((val_corr hI hr.2 f).trans (val_one _))
    rw [e₁] at e
    rw [val_pull hI', val_one, Category.id_comp]
    simpa using e.symm
  · have e := vt _ (lift x' y').left z J J' hJ hJ'
    rwa [cmp x' y' m hx hy] at e

theorem stalkUnits_symm_gm {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U)
    (a : Γ(X, U)ˣ) : (((TorusExt.stalkUnits z).symm (gm x z U a) : Fˣ) : F) = valF x U a.val := by
  refine (TorusExt.stalkConst z).injective ?_
  rw [← TorusExt.stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (toStk_valF x U z h a).symm

theorem vF_eq_genVal {X Y Y' : Scheme.{0}} {L : LB X} {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ}
    {u : HolUnif A L' g} (hL' : L'.IsLB) {Φ : A.left ⟶ X} {w : LB.Iso L' (L.pull Φ)} {J : (Sp ℂ ⟶ X) → L.ι}
    (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ A.left)} {ε : K → ℤ}
    (r : LB.Gen (LB.LinComb L φ ε)) {t : LB.Gen (LB.LinComb L' φ' ε)} (ht : t.IsGen) (m : Sp ℂ ⟶ Y) {y : Sp ℂ ⟶ Y'}
    {z : K → Fin g → ℂ} (hz : IsLift u φ' y z)
    (h : ∀ (p : Sp ℂ) J', Good L' p J' → val r m p J = (∏ k, om w p J J' (y ≫ φ' k) ^ ε k) * val t y p J') :
    vF r m J = genVal u hL' t y z * ((∏ k, fr (z k) ^ ε k : ℂˣ) : ℂ) := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : Good L p J := fun ψ => hJ ψ trivial
  have gJ' : Good L' p (chartAt hL') := fun ψ => le_chartAt hL' ψ trivial
  have e := congrArg (fun q => (((TorusExt.stalkUnits p).symm q : ℂˣ) : ℂ)) (h p _ gJ')
  simp only [map_mul, map_prod, map_zpow, Units.val_mul, Units.coe_prod, Units.val_zpow_eq_zpow_val] at e ⊢
  have e₁ : (((TorusExt.stalkUnits p).symm (val r m p J) : ℂˣ) : ℂ) = vF r m J :=
    stalkUnits_symm_gm _ _ p (gJ.mem φ m) _
  have e₂ : (((TorusExt.stalkUnits p).symm (val t y p (chartAt hL')) : ℂˣ) : ℂ) =
      genVal u hL' t y z * frameProd u ε z fun k => chartAt hL' (y ≫ φ' k) :=
    (stalkUnits_symm_gm _ _ p (gJ'.mem φ' y) _).trans (valAt'_gen hL' ht hz (le_wchart_chartAt hL' φ' y))
  rw [e₁, e₂, mul_left_comm, frameProd, ← Finset.prod_mul_distrib] at e
  refine e.trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_))
  rw [← mul_zpow, hz k, hfr _ _ (le_chartAt hL' _)]
  refine congrArg (fun q => (q * _) ^ ε k) ?_
  have hm : (u.ex (z k)).left p ∈ (L.pull Φ).U (fun _ => J ((u.ex (z k)).left ≫ Φ)) ⊓
      L'.U (chartAt hL' (u.ex (z k)).left) := ⟨mem_pull.2 (gJ ((u.ex (z k)).left ≫ Φ)), gJ' _⟩
  exact stalkUnits_symm_gm _ _ p hm _

theorem fibRosSt : Laws → FibRosSt := by
  rintro - R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, hΛ, gp, hw, hAH, -, -, -, hex, hfr⟩ f f' - - F G hF hG r hr
  have down : ∀ (a : D.P.A ⟶ D.P.A) (H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, ex (H z) = ex z ≫ a) →
      ∃ a' : P'.A ⟶ P'.A, a'.left ≫ φ = φ ≫ a.left ∧ (∀ z, u.ex (H z) = u.ex z ≫ a') ∧
        (1 : 𝟙_ (Over (Sp ℂ)) ⟶ P'.A) ≫ a' = 1 := fun a H hH => by
    let a' : P'.A ⟶ P'.A := Over.homMk (gp.1.lift (φ ≫ a.left) P'.A.hom
      (by rw [Category.assoc, Over.w, gp.1.w])) (gp.1.lift_snd _ _ _)
    have ha : a'.left ≫ φ = φ ≫ a.left := gp.1.lift_fst _ _ _
    have hu : ∀ z, u.ex (H z) = u.ex z ≫ a' := fun z =>
      Over.OverMorphism.ext (gp.1.hom_ext (by
        rw [← hex, hH, Over.comp_left, Over.comp_left, hex, Category.assoc, Category.assoc, ha]) (by rw [Over.w, Over.w]))
    refine ⟨a', ha, hu, ?_⟩
    have h0 : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)
    rw [← h0, ← hu, map_zero]
  obtain ⟨a, ha, ua, a₁⟩ := down f F hF
  obtain ⟨b, hb, ub, b₁⟩ := down f' G hG
  obtain ⟨t, ht, vt⟩ := exists_ros_down gp D.P.isLB P'.isLB hw a₁ b₁ ha hb (r := r) hr
  obtain ⟨adj, one⟩ := genVal_rosati P'.isLB hAH ua ub t ht.1 ht.2
  refine ⟨adj, fun x z => ?_⟩
  have e := vF_eq_genVal P'.isLB hJ (fun z i hi => by rw [← hex]; exact hfr z i hi) r ht.1 (lift (ex x) (ex z)).left
    (isLift_rosati ua ub x z) (fun p J' hJ' => vt (u.ex x) (u.ex z) _
      ((hex x).symm.trans (congrArg (fun q => q.left) (lift_fst (ex x) (ex z)).symm))
      ((hex z).symm.trans (congrArg (fun q => q.left) (lift_snd (ex x) (ex z)).symm)) p J J'
      (fun ψ => hJ ψ trivial) hJ')
  rw [e, one, _root_.one_mul]
  simp only [Fin.prod_univ_six, rosatiLift, rosatiε, Matrix.cons_val, zpow_neg, zpow_one, Units.val_mul,
    Units.val_inv_eq_inv_val]
  field_simp

end GlobalTheory.Ex.Arch.FibRos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionActionInValues
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

noncomputable section
namespace GlobalTheory.Relabel
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Ex.GtValues

section
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem gtAct_pt (hG : GlobalFnsSt) {y : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L y J) (oa : D.OAct O) (a : O)
    {u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)}
    (hu : TorusExt.IsRos D.P.L _ _ u) (g g' : GtPtF D F) :
    GtAct oa a g g' ↔ g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ,
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
  have vv : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) χ,
      val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 (TF (R := R) F).left) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun u χ =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)))
  refine ⟨fun h => ⟨h.1, fun χ => (val_corr hJ (h.2 _ hu.1 hu.2 χ) _).symm.trans (vv _ χ)⟩,
    fun ⟨hb, hv⟩ => ⟨hb, fun u' hu' u₀ χ => corr_pt D.P.isLB (fun U _ h => ?_)
      (mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu' _)) (g'.isGen χ) hJ
      ((vv u' χ).trans ((congrArg₂ (· * ·) rfl
        (TorusExt.IsRos.unique hG D.P.isAb D.P.isLB ⟨hu', u₀⟩ hu hJ _ _)).trans (hv χ).symm))⟩⟩
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
    (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
  rw [prod_gt, TorusExt.cPoint_smul oa, hb]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end

theorem gtAct_values : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (N : NumD F) (ν : NumOf D F N) (O : Type) [CommRing O] [StarRing O], (∀ (oa : D.P.OAct O) (x : O), ∃ ρ, RosV ν oa x ρ) ∧ ∀ [Module O D.X] (oa : D.OAct O) (x : O) (ρ : N.A → N.A → F), RosV ν oa.onB x ρ → ∀ g g' v v', ν.Pt g v → ν.Pt g' v' → (GtAct oa x g g' ↔ v'.b = actV ν oa.onB x v.b ∧ ∀ χ, (v'.s χ : F) = v.s (ν.eX.symm (star x • ν.eX χ)) * ρ (N.c χ) v.b) := by
  intro hG R _ _ D F _ _ N ν O _ _
  refine ⟨fun oa x => ?_, fun oa x ρ ⟨u, hu, u₀, hρ⟩ g g' v v' h h' => ?_⟩
  · have := oa.hom x
    have := oa.hom (star x)
    have hr := oa.rosati (star x)
    rw [star_star] at hr
    obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
    exact ⟨_, u, hu, u₀, fun _ _ => rfl⟩
  · let y : Sp F := (⊥ : PrimeSpectrum F)
    have hJ := good ν y
    obtain ⟨a, b⟩ := (pt_iff ν y _ _).1 h
    obtain ⟨a', b'⟩ := (pt_iff ν y _ _).1 h'
    rw [gtAct_pt hG hJ oa x ⟨hu, u₀⟩, ν.eX.surjective.forall]
    refine and_congr ?_ (forall_congr' fun χ => ?_)
    · rw [← a, ← a', actV, ν.eA.eq_symm_apply]
    · have e := b (ν.eX.symm (star x • ν.eX χ))
      rw [ν.eX.apply_symm_apply] at e
      have r : toStk y (ρ (N.c χ) v.b) = (val₂ u y ν.J (cP D _ (ν.eX χ)) g.b).val := by
        rw [hρ, toStk_vF _ _ hJ, c_eq, a]; rfl
      rw [← (toStk y).injective.eq_iff, map_mul, r, ← e, ← b', ← Units.val_inj, Units.val_mul]
      rfl

end GlobalTheory.Relabel
end
end

