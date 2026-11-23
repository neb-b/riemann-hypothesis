module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2225
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D d : ℕ}

def part (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

variable {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ}

def transMat (c c' : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1) a

def IsForm (M : AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    M c y = chg (transMat c c' y) (M c' y)) ∧
  (∀ c : AlgChart p σ D, ContinuousOn (fun v => M c (c.e.symm v)) c.e.target) ∧
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, (M c y).IsHermitian

variable {A M M' J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

def chernMat {B : LB X} (φ : Weight p σ B) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess φ (pick φ.isLB y) y

theorem chernMat_congr {L N : HermLB p} (e : L.Isometric N) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : chernMat (L.φ σ) c y = chernMat (N.φ σ) c y := by
  unfold chernMat
  exact (e.hess_eq c hy (mem_pick _ y) (mem_pick _ y)).symm

section Flag

variable {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r)

end Flag

section Cell

variable {ι : Type} [Fintype ι] {r : ι → ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))



def emb {m : ℕ} (i : Fin m) : Fin i ⊕ Fin 1 → Fin m := Sum.elim (Fin.castLE i.isLt.le) fun _ => i



variable {m : ℕ}

variable {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)

end Cell

end GlobalTheory.MixDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem translate_baseChange_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  intro R R₁ _ _ ρ G _ V hV a
  let f := spMap ρ
  let G₁ := (Over.pullback f).obj G
  let a₁ : Over.mk (𝟙 (Sp R₁)) ⟶ G₁ :=
    Over.homMk (pullback.lift (f := G.hom) (g := f) a.left (𝟙 (Sp R₁))
      ((Over.w a).trans (Category.id_comp _).symm))
      (by show pullback.lift _ _ _ ≫ pullback.snd G.hom f = 𝟙 _; simp)
  let e : G₁ ⟶ Over.mk (𝟙 (Sp R₁)) := Over.homMk G₁.hom (by simp)
  let c : G₁ ⟶ G₁ := e ≫ a₁
  have hc : ∀ g : G₁ ⟶ G₁, g ≫ c = c := fun g =>
    by rw [← Category.assoc]; congr 1; ext; simp [e]
  let T : G₁ ⟶ G₁ := 𝟙 G₁ * c
  let T' : G₁ ⟶ G₁ := 𝟙 G₁ * c⁻¹
  have h₁ : T ≫ T' = 𝟙 G₁ := by
    simp only [T', MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, hc, T, mul_inv_cancel_right]
  have h₂ : T' ≫ T = 𝟙 G₁ := by
    simp only [T, MonObj.comp_mul, Category.comp_id, T', hc, inv_mul_cancel_right]
  haveI : IsIso T := ⟨⟨T', h₁, h₂⟩⟩
  haveI : IsIso T.left := Functor.map_isIso (Over.forget _) T
  haveI : IsAffineHom (pullback.fst G.hom f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.hom f).flip
      (inferInstanceAs (IsAffineHom (spMap ρ)))
  refine ⟨(T.left ≫ pullback.fst G.hom f) ⁻¹ᵁ V, hV.preimage _, ?_⟩
  intro Ω _ z t x a' hx ha hxa w
  have ht : t = (z ≫ pullback.snd G.hom f) ≫ f := by
    have h0 : x.left ≫ G.hom = t := Over.w x
    rw [← h0, hx, Category.assoc, pullback.condition, Category.assoc]
  subst ht
  let Z : Over (Sp R₁) := Over.mk (z ≫ pullback.snd G.hom f)
  let z' : Z ⟶ G₁ := Over.homMk z (by simp [G₁, Z])
  have key := (isGrpPullback_pullback G f).2 Z z' (z' ≫ c) x a' (by simpa [z'] using hx)
    (by rw [ha]; simp [z', c, e, a₁, G₁, pullback.lift_fst]; rfl)
  have hT : z' * (z' ≫ c) = z' ≫ T := by simp only [T, MonObj.comp_mul, Category.comp_id]
  rw [hT] at key
  have : (z ≫ T.left ≫ pullback.fst G.hom f) w ∈ V := by
    have e2 : z ≫ T.left ≫ pullback.fst G.hom f = (x * a').left := by
      rw [key]; simp [z']
    rw [e2]; exact hxa w
  simpa using this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFraction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem transport_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (A₁ : PolAV (Sp K')) (α₁ : A₁.A.left ⟶ A.A.left) (α₁₂ : (G2 A₁.A).left ⟶ (G2 A.A).left), IsGrpPullback A₁.A A.A (spMap io) α₁ → Geo.Tor.IsSquare α₁ α₁₂ → LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A.A A.L).pull α₁₂) → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂), Function.Injective ρ → (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) → ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (q : A₂.A.left ⟶ A₁.A.left), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q ∧ LBIso A₂.L (A₁.L.pull q) ∧ gen₂.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
  intro R _ _ _ G _ _ A gen hgen PP hExt K' _ io A₁ α₁ α₁₂ hα hsqα hΛ R₂ _ _ _ ρ i hρ hi G₂ _ _ β β₂ hβ hsqβ
  haveI := hgen
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R₂)).obj G₂) := Functor.isCommMonObj_obj
  obtain ⟨A₂, q, pq, -, mq, t, ht⟩ := GlobalTheory.polBaseChange_holds _ _ (spMap i.toRingHom) A₁
  have hq : IsGrpPullback A₂.A A₁.A (spMap i.toRingHom) q := ⟨pq, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pq.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pq.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mq]; rfl⟩
  have hLq : LBIso A₂.L (A₁.L.pull q) := LBIso.symm ⟨t, ht⟩
  have hsq : jK R₂ ≫ spMap ρ = spMap i.toRingHom ≫ spMap io ≫ jK R := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp [hi]
  haveI : IsMonHom gen.symm.hom := by show IsMonHom gen.inv; infer_instance
  have hgi : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) gen.inv.left := isGrpPullback_of_iso gen.symm
  have gG : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hgi.comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  have gA : IsGrpPullback A₂.A G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)) := hq.comp (hα.comp gG)
  have g₂ : IsGrpPullback ((Over.pullback (jK R₂)).obj G₂) G (spMap i.toRingHom ≫ spMap io ≫ jK R)
      (pullback.fst G₂.hom (jK R₂) ≫ β) :=
    ((isGrpPullback_pullback G₂ (jK R₂)).comp hβ).congr hsq rfl
  obtain ⟨e, he, hee⟩ := grpPullback_iso g₂ gA
  haveI := he
  have hei : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hgh : gen.inv.left ≫ gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have h5 : e.inv.left ≫ pullback.fst G₂.hom (jK R₂) ≫ β = q ≫ α₁ ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) := by
    rw [← hee, ← Category.assoc, hei, Category.id_comp]
  refine ⟨A₂, e, q, he, ⟨pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩, hq, hLq, h5⟩

  obtain ⟨g₂m, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
    (isGrpPullback_pullback G (jK R))
  obtain ⟨γ₁, hsqγ, Ha⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) A.A _ hgi
  obtain ⟨q₂, hsqq, Hc⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₁.A A₂.A _ hq
  obtain ⟨e₂, hsqe, Hd⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ A₂.A ((Over.pullback (jK R₂)).obj G₂) _
    (isGrpPullback_of_iso e)
  have hLK := pull_isLB A.isLB gen.hom.left
  have i₀ : LBIso A.L ((A.L.pull gen.hom.left).pull gen.inv.left) :=
    LBIso.chartPull (chartPullUnpull A.L (𝟙 _) rfl)
      (chartPullLinComb A.L gen.hom.left (fun _ => gen.inv.left) (fun _ => 𝟙 _) _ (𝟙 _)
        (fun _ => by rw [hgh, Category.id_comp]))
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A.isLB (𝟙 _)))
  have Ha' := Ha _ _ _ PP g₂m hLK A.isLB hExt.1 i₀ (hExt.2 g₂m hg₂)
  have Hb : LBIso (abelian₂ A₁.A A₁.L) (PP.pull (α₁₂ ≫ γ₁ ≫ g₂m)) :=
    LBIso.trans (DVR.linComb_isLB _ A₁.isLB _ _) (pull_isLB (DVR.linComb_isLB _ A.isLB _ _) _)
      (pull_isLB hExt.1 _) hΛ
      (LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ α₁₂ α₁₂ rfl)
        (chartPullSame PP (fun _ => α₁₂ ≫ γ₁ ≫ g₂m) (fun _ => γ₁ ≫ g₂m) _ α₁₂ fun _ => rfl) Ha')
  have Hc' := Hc _ _ _ PP _ A₁.isLB A₂.isLB hExt.1 hLq Hb
  have Hd' := Hd _ _ _ PP _ A₂.isLB (pull_isLB A₂.isLB _) hExt.1
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB A₂.isLB _)) Hc'
  have E : e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      simp only [Category.assoc, hg₂.1, reassoc_of% hsqγ.1, reassoc_of% hsqα.1, reassoc_of% hsqq.1,
        reassoc_of% hsqe.1, hsqβ.1, reassoc_of% hκ₂.1, hee]
    · show (e₂ ≫ q₂ ≫ α₁₂ ≫ γ₁ ≫ g₂m) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      simp only [Category.assoc, hg₂.2, reassoc_of% hsqγ.2, reassoc_of% hsqα.2, reassoc_of% hsqq.2,
        reassoc_of% hsqe.2, hsqβ.2, reassoc_of% hκ₂.2, hee]
  exact LBIso.trans (DVR.linComb_isLB _ (pull_isLB A₂.isLB _) _ _) (pull_isLB hExt.1 _)
    (pull_isLB (pull_isLB hExt.1 β₂) κ₂) Hd'
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => E) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwicePicardClassEqZeroOfTranslatesMemOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualTriv

theorem range_sub {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S) (p : Y ⟶ A)
    (hY : ∀ y, Y.hom y ∈ U) : Set.range p.left ⊆ Set.range (A.hom ⁻¹ᵁ U).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  show A.hom (p.left y) ∈ U
  rw [← Scheme.Hom.comp_apply, Over.w p]
  exact hY y

noncomputable def liftU {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : Y.left ⟶ (A.hom ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (A.hom ⁻¹ᵁ U).ι p.left (range_sub A U Y p hY)

theorem liftU_fac {S : Scheme.{0}} (A : Over S) (U : S.Opens) (Y : Over S)
    (hY : ∀ y, Y.hom y ∈ U) (p : Y ⟶ A) : liftU A U Y hY p ≫ (A.hom ⁻¹ᵁ U).ι = p.left :=
  IsOpenImmersion.lift_fac _ _ _

end GlobalTheory.DualTriv

open GlobalTheory.DualTriv in
theorem GlobalTheory.twice_cls_eq_zero_of_translates_mem : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), A.hom ⁻¹ᵁ U ≤ W → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A), (∀ y, Y.hom y ∈ U) → (∀ y, v.left y ∈ V) → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → ∀ l : Y.left ⟶ W.toScheme, l ≫ W.ι = x.left → GlobalTheory.CechPic.pull l (2 • c) = 0 := by
  intro S _ A _ _ U V W hV hW c hc Y x a v hY hv hxa l hl
  set cU := GlobalTheory.CechPic.pull (A.left.homOfLE hW) c with hcU
  have zero_of : ∀ p : Y ⟶ A, (∀ y, p.left y ∈ V) →
      GlobalTheory.CechPic.pull (liftU A U Y hY p) cU = 0 := by
    intro p hp
    have H : Set.range p.left ⊆ Set.range V.ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hp y
    have e : liftU A U Y hY p ≫ A.left.homOfLE hW = IsOpenImmersion.lift V.ι p.left H ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι,
        liftU_fac, IsOpenImmersion.lift_fac]
    rw [hcU, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp, hc, map_zero]
  have s1 := _root_.GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) x a
  have s2 := _root_.GlobalTheory.SquareOpen.pull_mul_add_pull_mul_inv_of_opens S A ‹_› U cU Y (liftU A U Y hY) hY (liftU_fac A U Y hY) v a
  rw [zero_of _ (fun y => (hxa y).1), zero_of _ (fun y => (hxa y).2.1)] at s1
  rw [zero_of _ (fun y => (hxa y).2.2.1), zero_of _ (fun y => (hxa y).2.2.2), zero_of _ hv] at s2
  have two : 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU = 0 := by
    calc 2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU
        = (2 • GlobalTheory.CechPic.pull (liftU A U Y hY x) cU + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) -
          (2 • (0 : GlobalTheory.CechPic.Pic _) + GlobalTheory.CechPic.pull (liftU A U Y hY a) cU +
            GlobalTheory.CechPic.pull (liftU A U Y hY a⁻¹) cU - 2 • GlobalTheory.CechPic.pull (liftU A U Y hY 1) cU) := by abel
      _ = 0 := by rw [← s1, ← s2, sub_self]
  have el : l = liftU A U Y hY x ≫ A.left.homOfLE hW := by
    rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, liftU_fac, hl]
  rw [map_nsmul, el, GlobalTheory.CechPic.pull_comp, ← hcU, two]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPolarisationClassGenericDiagonalDoubling
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DiagPic

open GlobalTheory.CechPic

theorem pull_inv {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull (GrpObj.inv : A.A ⟶ A.A).left (cls A.L A.isLB) = cls A.L A.isLB := by
  obtain ⟨U, hU, ht⟩ := A.sym (default : PrimeSpectrum K)
  have h := (cls_eq_zero_iff (LB.isLB_linComb A.isLB _ _)).2 ht
  rw [cls_linComb A.isLB, Fin.sum_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, add_neg_eq_zero] at h
  have hr : Set.range (𝟙 A.A.left : A.A.left ⟶ A.A.left) ⊆ Set.range (A.A.hom ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    intro x _
    have e : A.A.hom x = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    show A.A.hom x ∈ U
    rw [e]
    exact hU
  have h' := congrArg (pull (IsOpenImmersion.lift (A.A.hom ⁻¹ᵁ U).ι (𝟙 _) hr)) h
  rwa [← pull_comp, ← pull_comp, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac, Category.id_comp,
    pull_id] at h'

theorem pull_one {S : Scheme.{0}} (A : PolAV S) {T : Over S} :
    pull (1 : T ⟶ A.A).left (cls A.L A.isLB) = 0 := by
  have h := (cls_eq_zero_iff (pull_isLB A.isLB _)).2 A.rigid
  rw [cls_pull A.isLB] at h
  rw [Hom.one_def, Over.comp_left, pull_comp]
  exact (congrArg _ h).trans (map_zero _)

theorem lam_self {K : Type} [Field K] (A : PolAV (Sp K)) :
    lam (cls A.L A.isLB) (𝟙 A.A) (𝟙 A.A) = 2 • cls A.L A.isLB := by
  have h := lam_mul_left A.isLB (GlobalTheory.Moduli.cube_of_isLB _ A A.L A.isLB) (𝟙 A.A) (𝟙 A.A)⁻¹ (𝟙 A.A)
  rw [mul_inv_cancel, lam_one_left] at h
  have e : lam (cls A.L A.isLB) (𝟙 A.A)⁻¹ (𝟙 A.A) = -(2 • cls A.L A.isLB) := by
    rw [lam, inv_mul_cancel, pull_one, Hom.inv_def, Category.id_comp, pull_inv, Over.id_left, pull_id]
    abel
  rw [e] at h
  exact (add_neg_eq_zero.1 h.symm)

theorem pull_sq {K : Type} [Field K] (A : PolAV (Sp K)) :
    pull ((𝟙 A.A) ^ 2 : A.A ⟶ A.A).left (cls A.L A.isLB) = 4 • cls A.L A.isLB := by
  have h := lam_self A
  rw [lam, pull_one, Over.id_left, pull_id, add_zero, sub_sub, sub_eq_iff_eq_add] at h
  rw [pow_two, h]
  abel

end GlobalTheory.Mum.DiagPic

namespace GlobalTheory.Mum

open GlobalTheory.CechPic

theorem two_smul_cls_eq_pull_diag_and_pull_sq : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (c : GlobalTheory.CechPic.Pic (pullback G.hom (jK R))) (d : GlobalTheory.CechPic.Pic G.left) (hL : (A.L.pull gen.hom.left).IsLB) (hP : (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left).IsLB), c = GlobalTheory.CechPic.cls (A.L.pull gen.hom.left) hL → d = GlobalTheory.CechPic.cls (PP.pull (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left) hP → 2 • c = GlobalTheory.CechPic.pull (pullback.fst G.hom (jK R)) d ∧ ∃ φ : pullback G.hom (jK R) ⟶ pullback G.hom (jK R), φ ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ ((𝟙 G) ^ 2 : G ⟶ G).left ∧ GlobalTheory.CechPic.pull φ c = 4 • c := by
  intro R _ _ G _ _ A gen hgen PP hExt c d hL hP hc hd
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have hc' : c = pull gen.hom.left (cls A.L A.isLB) := hc
  refine ⟨?_, ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left, ?_, ?_⟩
  · obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _
      (isGrpPullback_pullback G (jK R))
    have h₁ := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hExt.1 g₂)).2 (hExt.2 g₂ hg₂)
    have h₂ := (cls_cube_two hL (fst _ _) (snd _ _) (LB.isLB_linComb hL _ _)).symm.trans h₁
    have h₃ := congrArg (pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left) h₂
    have e : (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left ≫ g₂ =
        pullback.fst G.hom (jK R) ≫ (lift (𝟙 G) (𝟙 G) : G ⟶ G2 G).left := by
      apply pullback.hom_ext
      · show (_ ≫ g₂) ≫ (fst G G).left = (_ ≫ _) ≫ (fst G G).left
        rw [Category.assoc, hg₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
          lift_fst, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      · show (_ ≫ g₂) ≫ (snd G G).left = (_ ≫ _) ≫ (snd G G).left
        rw [Category.assoc, hg₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
          lift_snd, Over.id_left, Over.id_left]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    rw [pull_lam, lift_fst, lift_snd, cls_pull hExt.1, ← pull_comp, e, pull_comp, cls_pull A.isLB, lam_pull,
      Category.id_comp] at h₃
    have h₄ := pull_lam gen.hom (cls A.L A.isLB) (𝟙 _) (𝟙 _)
    rw [Category.comp_id, DiagPic.lam_self, map_nsmul] at h₄
    rw [hc', hd]
    exact h₄.trans h₃
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) = (Over.pullback (jK R)).map ((𝟙 G) ^ 2) := by
      rw [pow_two, pow_two, Functor.map_mul, CategoryTheory.Functor.map_id]
    rw [e]
    exact pullback.lift_fst _ _ _
  · have e : ((𝟙 ((Over.pullback (jK R)).obj G)) ^ 2 : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G) ≫ gen.hom = gen.hom ≫ (𝟙 A.A) ^ 2 := by
      rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
    have h := congrArg (pull gen.hom.left) (DiagPic.pull_sq A)
    rw [← pull_comp, ← Over.comp_left, ← e, Over.comp_left, pull_comp, map_nsmul] at h
    rw [hc']
    exact h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def GeomIso {K₀ K' Ω : Type} [CommRing K₀] [CommRing K'] [CommRing Ω] (A₀ : PolAV (Sp K₀)) (A' : PolAV (Sp K'))
    (e₀ : K₀ →+* Ω) (e' : K' →+* Ω) : Prop :=
  ∃ (B : PolAV (Sp Ω)) (b₀ : B.A.left ⟶ A₀.A.left) (b' : B.A.left ⟶ A'.A.left),
    IsGrpPullback B.A A₀.A (spMap e₀) b₀ ∧ LBIso B.L (A₀.L.pull b₀) ∧
    IsGrpPullback B.A A'.A (spMap e') b' ∧ LBIso B.L (A'.L.pull b')

def UniTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (A : PolAV (Sp (FractionRing R))) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (_ : Unif (maximalIdeal W) D' A' G') (_ : IsPullDeg φ D D'.toPre) (a : A'.A.left ⟶ A.A.left),
    GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsSemiAbelian G' ∧ IsFib φ A A' a

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
namespace GlobalTheory.Mum

theorem actsAs_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (b : D.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D.toPre.X) (g g' : G ⟶ G), IsMonHom g → IsMonHom g' → ActsAs U.toUnifPre b h g → ActsAs U.toUnifPre b h g' → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U b h g g' hg hg' H H'
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨q1, t, ht, i1⟩ := H e
  obtain ⟨q2, t', ht', i2⟩ := H' e
  have htt : t = t' := GlobalTheory.LinearUnifCheck.torusEndOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U.gt e) GlobalTheory.globalFns_holds _ _
    (q1.trans q2.symm) (i1.trans (htt ▸ i2.symm))

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | exact GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | (intros; apply GlobalTheory.LabelTorsion.pow_eq_one_of_over_label <;> assumption)
end

