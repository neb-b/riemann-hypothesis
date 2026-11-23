module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallDescentH1Surjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueBaseChangeNatura
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem val_sub_pull {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Y Y' : Scheme.{0}}
    {t : Y ⟶ Sp R} {t' : Y' ⟶ Sp R'} {φ : Y' ⟶ Y} (m : IsMor (dp0 R) t (dp0 R') t' σ φ)
    (E : SqExt R) (E' : SqExt R') (ρ : E.C →+* E'.C) (ρ₀ : E.B →+* E'.B)
    (hρ : ∀ r, ρ (algebraMap R E.C r) = algebraMap R' E'.C (σ r))
    (hρ₀ : ∀ r, ρ₀ (algebraMap R E.B r) = algebraMap R' E'.B (σ r))
    (hπ : ∀ c, ρ₀ (E.π c) = E'.π (ρ c)) (hi : ∀ b, ρ (E.i b) = E'.i (ρ₀ b))
    {T₀ : Thick (dp0 R) t} {T₀' : Thick (dp0 R') t'} (a : T₀ ⟶ m.obj T₀')
    (z : Sp E.C ⟶ Y) (hz : z ≫ t = spMap (algebraMap R E.C))
    (z' : Sp E'.C ⟶ Y') (hz' : z' ≫ t' = spMap (algebraMap R' E'.C))
    (τ : T₀ ⟶ Thick.triv E.C z hz) (τ' : T₀' ⟶ Thick.triv E'.C z' hz')
    (h : ∀ c, ρ (τ.φ c) = τ'.φ (a.φ c)) (f : Z1 (O (dp0 R) t)) :
    ∃ b : E'.B, E'.val z' hz' (m.coef.pullbackOneCocycle f) - ev (m.coef.pullbackOneCocycle f) τ' =
      ρ (E.val z hz f - ev f τ) + τ'.φ (ev f a) - E'.i b := by
  have e : spMap ρ ≫ z = z' ≫ φ := by
    let u : T₀.B₀ →+* E.C := τ.φ₀
    let u' : T₀'.B₀ →+* E'.C := τ'.φ₀
    let a₀ : T₀.B₀ →+* T₀'.B₀ := a.φ₀
    have h1 : spMap u ≫ T₀.x = z := τ.pt
    have h2 : spMap u' ≫ T₀'.x = z' := τ'.pt
    have h3 : spMap a₀ ≫ T₀.x = T₀'.x ≫ φ := a.pt
    rw [← h1, ← h2, Category.assoc, ← h3, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    refine RingHom.ext fun c ↦ ?_
    obtain ⟨c, rfl⟩ := T₀.surj c
    exact (congrArg ρ (τ.comm c)).trans ((h c).trans
      ((τ'.comm (a.φ c)).symm.trans (congrArg τ'.φ₀ (a.comm c).symm)))
  have e₀ : spMap ρ₀ ≫ spMap (E.π : E.C →+* E.B) ≫ z = (spMap (E'.π : E'.C →+* E'.B) ≫ z') ≫ φ := by
    rw [Category.assoc, ← e, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext hπ
  let Φ : E.thick _ (E.red_w hz) ⟶ m.obj (E'.thick _ (E'.red_w hz')) :=
    { φ := { ρ with commutes' := hρ }
      φ₀ := ρ₀
      comm := hπ
      dp := isDPMorphism_sqDP E.sq E'.sq _ fun c hc ↦ by
        have hc' : E.π c = 0 := hc
        change E'.π (ρ c) = 0
        rw [← hπ, hc', map_zero]
      pt := e₀ }
  let b : Thick.triv E.B _ (E.red_w hz) ⟶ m.obj (Thick.triv E'.B _ (E'.red_w hz')) :=
    Thick.trivHom { ρ₀ with commutes' := hρ₀ } e₀
  have k1 := ev_sq f b (m.functor.map (E'.secHom (E'.red_w hz') E'.i E'.π_i))
    (E.secHom (E.red_w hz) E.i E.π_i) Φ fun c ↦ (hi c).symm
  have k2 := ev_sq f a (m.functor.map (τ' ≫ E'.idHom hz')) (τ ≫ E.idHom hz) Φ fun c ↦ (h c).symm
  have k3 := ev_comp f τ (E.idHom hz)
  have k4 := ev_comp (m.coef.pullbackOneCocycle f) τ' (E'.idHom hz')
  have key : ∀ (A B C : E.C) (x y u v w k l : E'.C) (N : E.C), x + y = ρ A + w → l + k = ρ N + w → N = C + B →
      k = v + u → y - u - v = ρ (A - B - C) + l - x := fun A B C x y u v w k l N h1 h2 h3 h4 ↦ by
    subst h3 h4
    rw [map_add (f := _)] at h2
    rw [map_sub, map_sub]
    linear_combination h1 - h2
  exact ⟨ev f b, key _ _ _ _ _ _ _ _ _ _ _ k1 k2 k3 k4⟩

attribute [local instance] cotOp cotCentral cotTower

def cotRingHom {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {D D' : Type} [CommRing D] [Bialgebra R D]
    [CommRing D'] [Bialgebra R' D'] (s : SemiBialgHom σ D D') :
    TrivSqZeroExt R (Cot R D) →+* TrivSqZeroExt R' (Cot R' D') where
  toFun c := TrivSqZeroExt.inl (σ c.fst) + TrivSqZeroExt.inr ((SemiBialgHom.cot s) c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [map_smulₛₗ]

set_option backward.isDefEq.respectTransparency false in
theorem cotVal_pull (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R')
    (X : Over (Sp R)) (X' : Over (Sp R')) (φ : X'.left ⟶ X.left)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R') (X'.hom ≫ 𝟙 _) σ φ)
    (D D' : Type) [CommRing D] [Bialgebra R D] [CommRing D'] [Bialgebra R' D']
    (s : SemiBialgHom σ D D') (y : Pt X D) (y' : Pt X' D')
    (a : trivAt y ⟶ m.obj (trivAt y')) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (ha : ∀ r : D, (a.φ r : D') = s r) :
    cotVal (m.coef.pullbackOneCocycle f) y' =
      (SemiBialgHom.cot s) (cotVal f y) + dUnit (R := R') (A := D') (ev f a) := by
  have hf : ∀ c, (cotRingHom s c).fst = σ c.fst := fun c ↦ add_zero _
  have hs : ∀ c, (cotRingHom s c).snd = (SemiBialgHom.cot s) c.snd := fun c ↦ zero_add _
  have pf : ∀ c : D, TrivSqZeroExt.fst (cotPt R D c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps : ∀ c : D, TrivSqZeroExt.snd (cotPt R D c) = dUnit (R := R) c := fun c ↦ zero_add _
  have pf' : ∀ c : D', TrivSqZeroExt.fst (cotPt R' D' c) = Coalgebra.counit c := fun c ↦ add_zero _
  have ps' : ∀ c : D', TrivSqZeroExt.snd (cotPt R' D' c) = dUnit (R := R') c := fun c ↦ zero_add _
  obtain ⟨b, hb⟩ := val_sub_pull m (cotExt R D) (cotExt R' D') (cotRingHom s) σ
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) (fun _ ↦ rfl) (fun c ↦ (hf c).symm)
    (fun r ↦ TrivSqZeroExt.ext (hf _) ((hs _).trans (map_zero _))) a
    (spOver (cotPt R D) ≫ y).left (Pt.w _) (spOver (cotPt R' D') ≫ y').left (Pt.w _)
    (trivMap (cotPt R D) y) (trivMap (cotPt R' D') y') (fun c ↦ by
      change cotRingHom s (cotPt R D c) = cotPt R' D' (a.φ c : D')
      have h := congrArg (fun u : D' ↦ cotPt R' D' u) (ha (show D from c))
      refine Eq.trans ?_ h.symm
      ext
      · rw [hf, pf, pf', s.counit_map]
      · rw [hs, ps, ps', s.cot_d]) f
  refine (congrArg (cotSnd R' D') hb).trans ?_
  rw [map_sub, map_add (f := _)]
  refine (sub_zero _).trans ?_
  exact congrArg₂ (· + ·) (hs _) (ps' _)

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyRestrictAffinePointPairsBij
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.SmallPairs

variable {R : Type} [CommRing R] {I : Ideal R} (κ : DividedPowers I) {X : Scheme.{0}} (t : X ⟶ Sp R)
  {Y : Scheme.{0}} (i : X ⟶ Y)

def cov (V : Y.affineOpens) : X.Opens := i ⁻¹ᵁ V.1

theorem iSup_cov : ⨆ V, cov i V = ⊤ := by
  simp only [cov]
  rw [← Scheme.Hom.preimage_iSup, AlgebraicGeometry.iSup_affineOpens_eq_top Y]
  simp

abbrev SC : Type 1 := (IsSmall κ t (cov i)).FullSubcategory

abbrev PC : Type 1 := (IsSm κ t i).FullSubcategory

def fgt : PC κ t i ⥤ SC κ t i where
  obj a := ⟨a.obj.T, by obtain ⟨V, hV⟩ := a.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk f.hom.1

def sec : SC κ t i ⥤ PC κ t i where
  obj T := ⟨⟨T.obj, ⊤, Or.inr rfl, by simp⟩, by obtain ⟨V, hV⟩ := T.property; exact ⟨V, hV⟩⟩
  map f := ObjectProperty.homMk ⟨f.hom, le_rfl⟩

abbrev OS : SC κ t i ⥤ CommAlgCat.{0} R := (IsSmall κ t (cov i)).ι ⋙ O κ t

abbrev OP : PC κ t i ⥤ CommAlgCat.{0} R := ((IsSm κ t i).ι ⋙ Pr.fgt κ t i) ⋙ O κ t

def nS : CoefMap (RingHom.id R) (OS κ t i) (OP κ t i) where
  G := fgt κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def kP : CoefMap (RingHom.id R) (OP κ t i) (OS κ t i) where
  G := sec κ t i
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

def θP : fgt κ t i ⋙ sec κ t i ⟶ 𝟭 (PC κ t i) where
  app a := ObjectProperty.homMk ⟨𝟙 a.obj.T, le_top⟩
  naturality a b f :=
    ObjectProperty.hom_ext _ (Subtype.ext ((Category.comp_id f.hom.1).trans (Category.id_comp f.hom.1).symm))

def θS : sec κ t i ⋙ fgt κ t i ⟶ 𝟭 (SC κ t i) where
  app T := ObjectProperty.homMk (𝟙 T.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((Category.comp_id f.hom).trans (Category.id_comp f.hom).symm)

theorem kn1 (c : H1 (OP κ t i)) : (nS κ t i).pull1 ((kP κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyOne_id]

theorem nk1 (c : H1 (OS κ t i)) : (kP κ t i).pull1 ((nS κ t i).pull1 c) = c := by
  rw [← CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyOne_id]

theorem kn2 (c : H2 (OP κ t i)) : (nS κ t i).pull2 ((kP κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θP κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj.T b), CoefMap.pullCohomologyTwo_id]

theorem nk2 (c : H2 (OS κ t i)) : (kP κ t i).pull2 ((nS κ t i).pull2 c) = c := by
  rw [← CoefMap.pullCohomologyTwo_comp, CoefMap.pullCohomologyTwo_eq_of_natTrans _ (CoefMap.id _) (θS κ t i)
    (fun T b ↦ mp_id (O κ t) T.obj b), CoefMap.pullCohomologyTwo_id]

theorem fac1 (c : H1 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 c =
    (nS κ t i).pull1 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 c) := by
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c; rfl

theorem fac2 (c : H2 (O κ t)) : (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 c =
    (nS κ t i).pull2 ((CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 c) := by
  obtain ⟨f, rfl⟩ := H2.mk_surjective _ c; rfl

end GlobalTheory.PDForm.SmallPairs

namespace GlobalTheory.PDForm

open SmallPairs

theorem pull_isSm_bijective (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y) :
    Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 ∧
      Function.Bijective (CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 := by
  have b1 := SmallDescent.pull1_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have b2 := small_descent_H2_bijective R I κ X t Y.affineOpens (cov i) (iSup_cov i)
  have n1 : Function.Bijective (nS κ t i).pull1 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull1, nk1 κ t i, kn1 κ t i⟩
  have n2 : Function.Bijective (nS κ t i).pull2 :=
    Function.bijective_iff_has_inverse.2 ⟨(kP κ t i).pull2, nk2 κ t i, kn2 κ t i⟩
  refine ⟨?_, ?_⟩
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull1 =
        ⇑(nS κ t i).pull1 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull1 := funext (fac1 κ t i)
    rw [e]; exact n1.comp b1
  · have e : ⇑(CoefMap.restrict (O κ t) ((IsSm κ t i).ι ⋙ Pr.fgt κ t i)).pull2 =
        ⇑(nS κ t i).pull2 ∘ ⇑(CoefMap.restrict (O κ t) (IsSmall κ t (cov i)).ι).pull2 := funext (fac2 κ t i)
    rw [e]; exact n2.comp b2

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAlgebraQuotientRingSurjectiveAndKernel
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

section Quot

variable {R B G : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing G] [Algebra R G]
  {q : B →+* G} (h : SemiHom (RingHom.id R) q)

theorem SemiHom.oneFormMap_surjective_of_surjective (hq : Function.Surjective q) : Function.Surjective h.m1 := by
  intro ω
  induction ω using ind1 with
  | h g g' =>
    obtain ⟨b, rfl⟩ := hq g
    obtain ⟨b', rfl⟩ := hq g'
    exact ⟨b • D R B b', by rw [h.oneFormMap_smul_semilinear, h.m1_D]⟩
  | h0 => exact ⟨0, map_zero _⟩
  | ha x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

theorem SemiHom.exists_mDR_eq (hq : Function.Surjective q) {j : ℕ} {x : DR R G}
    (hx : x ∈ ⋀[G]^j Ω[G⁄R]) : ∃ y ∈ ⋀[B]^j Ω[B⁄R], h.mDR y = x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap g =>
    obtain ⟨b, rfl⟩ := hq g
    refine ⟨algebraMap B _ b, ?_, h.mDR_algebraMap b⟩
    change _ ∈ LinearMap.range _ ^ 0
    rw [pow_zero]; exact Submodule.algebraMap_mem _
  | add x y i _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, add_mem ha hb, map_add _ _ _⟩
  | mem_mul m hm i x hx ih =>
    obtain ⟨ω, rfl⟩ := hm
    obtain ⟨ω', rfl⟩ := h.oneFormMap_surjective_of_surjective hq ω
    obtain ⟨y, hy, rfl⟩ := ih
    refine ⟨ι1 ω' * y, ?_, by rw [map_mul, h.mDR_ι]⟩
    have := mul_mem (ι_mem ω') hy
    rwa [add_comm] at this

theorem SemiHom.mOm_surjective (hq : Function.Surjective q) (j : ℕ) : Function.Surjective (h.mOm j) := by
  intro x
  obtain ⟨y, hy, e⟩ := h.exists_mDR_eq hq x.2
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

theorem SemiHom.mDR_surjective (hq : Function.Surjective q) : Function.Surjective h.mDR := by
  intro x
  induction x using indDR with
  | h g =>
    obtain ⟨b, rfl⟩ := hq g
    exact ⟨_, h.mDR_algebraMap b⟩
  | hd g =>
    obtain ⟨b, rfl⟩ := hq g
    exact ⟨ι1 (D R B b), by rw [h.mDR_ι, h.m1_D]⟩
  | hm x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a * b, map_mul _ _ _⟩
  | ha x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

theorem SemiHom.mem_of_mDR_eq_zero (hq : Function.Surjective q) (K : Ideal (DR R B))
    (hr : ∀ x ∈ K, ∀ y, x * y ∈ K)
    (hk : ∀ b, q b = 0 → algebraMap B (DR R B) b ∈ K ∧ ι1 (D R B b) ∈ K)
    (x : DR R B) (hx : h.mDR x = 0) : x ∈ K := by
  haveI : K.IsTwoSided := ⟨fun b ha ↦ hr _ ha b⟩
  let π : DR R B →+* DR R B ⧸ K := Ideal.Quotient.mk K
  let s : G → B := Function.surjInv hq
  have hs : Function.RightInverse s q := Function.surjInv_eq hq
  have k1 : ∀ a b : B, q a = q b → π (ι1 (D R B a)) = π (ι1 (D R B b)) := by
    intro a b e
    rw [← sub_eq_zero, ← map_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact (hk _ (by rw [map_sub, e, sub_self])).2
  let φ : G →+* DR R B ⧸ K := q.liftOfRightInverse s hs ⟨π.comp (algebraMap B (DR R B)), fun b hb ↦ by
    rw [RingHom.mem_ker] at hb ⊢
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (hk b hb).1⟩
  have hφ : ∀ b, φ (q b) = π (algebraMap B _ b) := fun b ↦
    q.liftOfRightInverse_comp_apply s hs _ b
  letI : Algebra G (DR R B ⧸ K) := φ.toAlgebra' fun g y ↦ by
    obtain ⟨b, rfl⟩ := hq g
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change φ (q b) * π y = π y * φ (q b)
    rw [hφ, ← map_mul, ← map_mul, Algebra.commutes]
  have hsm : ∀ (g : G) (y : DR R B ⧸ K), g • y = φ g * y := fun _ _ ↦ rfl
  have hπr : ∀ (r : R) (z : DR R B), π (r • z) = r • π z := fun r z ↦
    map_smul (Ideal.Quotient.mkₐ R K) r z
  haveI : IsScalarTower R G (DR R B ⧸ K) := ⟨fun r g y ↦ by
    obtain ⟨b, rfl⟩ := hq g
    rw [hsm, hsm, show r • q b = q (r • b) from (h r b).symm, hφ, hφ,
      show algebraMap B (DR R B) (r • b) = r • algebraMap B (DR R B) b from
        map_smul (IsScalarTower.toAlgHom R B (DR R B)) r b, hπr, smul_mul_assoc]⟩

  let δ : Derivation R G (DR R B ⧸ K) := Derivation.mk'
    { toFun g := π (ι1 (D R B (s g)))
      map_add' a b := by
        rw [← map_add (f := _), ← map_add (f := _), ← map_add (f := _)]
        exact k1 _ _ (by rw [map_add (f := _), hs, hs, hs])
      map_smul' r g := by
        rw [RingHom.id_apply, ← hπr, ← LinearMap.map_smul_of_tower, ← Derivation.map_smul]
        exact k1 _ _ (by rw [hs, h r (s g), hs]; rfl) }
    fun a b ↦ by
      change π (ι1 (D R B (s (a * b)))) = a • π (ι1 (D R B (s b))) + b • π (ι1 (D R B (s a)))
      have e : π (ι1 (D R B (s a * s b))) = π (algebraMap B _ (s a)) * π (ι1 (D R B (s b))) +
          π (algebraMap B _ (s b)) * π (ι1 (D R B (s a))) := by
        rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
          map_add, map_mul, map_mul]
      rw [← hφ, ← hφ, hs, hs] at e
      rw [hsm, hsm, ← e]
      exact k1 _ _ (by rw [hs, map_mul, hs, hs])
  let f : Ω[G⁄R] →ₗ[G] DR R B ⧸ K := δ.liftKaehlerDifferential
  have hf : ∀ ω : Ω[B⁄R], f (h.m1 ω) = π (ι1 ω) := by
    intro ω
    induction ω using ind1 with
    | h b c =>
      rw [h.oneFormMap_smul_semilinear, h.m1_D, map_smul, Derivation.liftKaehlerDifferential_comp_D, hsm, hφ, map_smul,
        Algebra.smul_def, map_mul]
      congr 1
      exact k1 _ _ (hs _)
    | h0 => simp
    | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hsq : ∀ ω, f ω * f ω = 0 := by
    intro ω
    obtain ⟨ω', rfl⟩ := h.oneFormMap_surjective_of_surjective hq ω
    rw [hf, ← map_mul, ExteriorAlgebra.ι_sq_zero, map_zero]
  let ψ : DR R G →ₐ[G] DR R B ⧸ K := ExteriorAlgebra.lift G ⟨f, hsq⟩
  have key : ∀ y : DR R B, ψ (h.mDR y) = π y := by
    intro y
    induction y using indDR with
    | h b => rw [h.mDR_algebraMap, AlgHom.commutes]; exact hφ b
    | hd b =>
      rw [h.mDR_ι, ExteriorAlgebra.lift_ι_apply]
      exact hf _
    | hm x y hx hy => rw [map_mul, map_mul, hx, hy, map_mul]
    | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
  have := key x
  rw [hx, map_zero] at this
  exact (Ideal.Quotient.eq_zero_iff_mem).1 this.symm

theorem semiHom_quotient_surjective_ker : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (G : Type) [CommRing G] [Algebra R G] (q : B →+* G) (h : SemiHom (RingHom.id R) q), Function.Surjective q → Function.Surjective h.m1 ∧ (∀ j, Function.Surjective (h.mOm j)) ∧ Function.Surjective h.mDR ∧ ∀ 𝔎 : Ideal (DR R B), (∀ x ∈ 𝔎, ∀ y, x * y ∈ 𝔎) → (∀ b, q b = 0 → algebraMap B (DR R B) b ∈ 𝔎 ∧ ι1 (D R B b) ∈ 𝔎) → ∀ x, h.mDR x = 0 → x ∈ 𝔎 :=
  fun _ _ _ _ _ _ _ _ _ h hq ↦ ⟨h.oneFormMap_surjective_of_surjective hq, h.mOm_surjective hq, h.mDR_surjective hq,
    fun K hr hk x hx ↦ h.mem_of_mDR_eq_zero hq K hr hk x hx⟩

end Quot

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem mem_of_finite_conj {K : Type} [Field K] [IsAlgClosed K] (k₀ : Subfield K) (hk : IsAlgClosed k₀)
    (a : K) (h : Set.Finite {b : K | ∃ σ : K ≃+* K, (∀ c ∈ k₀, σ c = c) ∧ b = σ a}) : a ∈ k₀ := by
  haveI := hk
  by_contra ha
  have htr : Transcendental k₀ a := by
    intro halg
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible k₀ (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k₀ a hdeg
    exact ha (hc ▸ c.2)
  have hc : ∀ c : k₀, ∃ σ : K ≃ₐ[k₀] K, σ a = a + algebraMap k₀ K c := by
    intro c
    have htr' : Transcendental k₀ (a + algebraMap k₀ K c) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub (isIntegral_algebraMap (x := c))).isAlgebraic)
    exact GroundTheory.Global.exists_algEquiv_apply_eq_of_transcendental htr htr'
  refine Set.infinite_of_injective_forall_mem (f := fun c : k₀ => a + algebraMap k₀ K c) ?_ ?_ h
  · intro c d hcd
    simpa using hcd
  · intro c
    obtain ⟨σ, hσ⟩ := hc c
    exact ⟨σ.toRingEquiv, fun b hb => σ.commutes ⟨b, hb⟩, hσ.symm⟩

theorem defOver_of_finite_orbit : ∀ (K : Type) [Field K] [IsAlgClosed K] (k₀ : Subfield K), IsAlgClosed k₀ →
    ∀ (Y : Scheme.{0}) (P : Sp K ⟶ Y),
    Set.Finite {P' : Sp K ⟶ Y | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ P' = spMap σ.toRingHom ≫ P} →
    DefOver k₀ P := by
  intro K _ _ k₀ hk Y P hfin
  classical
  let e := SpecToEquivOfLocalRing Y (CommRingCat.of K)
  let x := (e P).1
  let f := (e P).2.1
  have hP : P = Spec.map f ≫ Y.fromSpecStalk x := (e.left_inv P).symm
  let Φ : {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} → (Sp K ⟶ Y) :=
    fun g => e.symm ⟨x, g⟩
  have hΦ : Function.Injective Φ := by
    intro g₁ g₂ h
    have := e.symm.injective h
    exact eq_of_heq (Sigma.mk.inj this).2
  have hloc : ∀ σ : K ≃+* K, IsLocalHom (f ≫ CommRingCat.ofHom σ.toRingHom).hom := by
    intro σ
    have : IsLocalHom f.hom := (e P).2.2
    show IsLocalHom (σ.toRingHom.comp f.hom)
    infer_instance
  let T : Set {g : Y.presheaf.stalk x ⟶ CommRingCat.of K // IsLocalHom g.hom} :=
    {g | ∃ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) ∧ g.1 = f ≫ CommRingCat.ofHom σ.toRingHom}
  have hT : T.Finite := by
    refine Set.Finite.of_finite_image (hfin.subset ?_) hΦ.injOn
    rintro _ ⟨g, ⟨σ, hσ, hg⟩, rfl⟩
    refine ⟨σ, hσ, ?_⟩
    show Spec.map g.1 ≫ Y.fromSpecStalk x = _
    rw [hg, Spec.map_comp, Category.assoc, ← hP]
  have hmem : ∀ s, f.hom s ∈ k₀ := by
    intro s
    refine mem_of_finite_conj k₀ hk _ ((hT.image fun g => g.1.hom s).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨f ≫ CommRingCat.ofHom σ.toRingHom, hloc σ⟩, ⟨σ, hσ, rfl⟩, rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (f.hom.codRestrict k₀ hmem)) ≫ Y.fromSpecStalk x, ?_⟩
  refine Eq.trans ?_ hP.symm
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PowE8

def e8LB {S : Scheme.{0}} (G₀ : Over S) [GrpObj G₀] (L : LB G₀.left) (W : Matrix (Fin 8) (Fin 8) ℤ) :
    LB (powObj G₀ 8).left :=
  LB.LinComb L (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))

end GlobalTheory.PowE8
end
end

