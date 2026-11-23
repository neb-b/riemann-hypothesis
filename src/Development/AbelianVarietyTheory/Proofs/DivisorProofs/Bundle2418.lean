module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2383
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2342

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRationalPoints
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ModelChangeTo

theorem change_to_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair co hco
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om₁, hW, hint⟩ := _root_.GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨c₀, hc₀, hth⟩ := _root_.GlobalTheory.ThetaChange.main F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, om₁, e, c₀, rfl, ⟨hpair.base, hpair.herm, hpair.skew, hM₁, hpair.hX, hpair.hW, hpair.resX, hpair.resW, hW⟩,
    hc₀, fun Φ hΦ => ⟨hmaps Φ hΦ, hth Φ hΦ, fun x => hint x Φ hΦ⟩⟩

end GlobalTheory.ModelChangeTo

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeOneClassPullbackOfCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem kaehlerDifferential_map_commutative_pentagon {R₁ R₂ A₁ A₂ A₃ A₄ A₅ : Type} [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [CommRing A₃] [CommRing A₄] [CommRing A₅] [Algebra R₁ A₁] [Algebra R₁ A₂] [Algebra R₁ A₃] [Algebra R₂ A₄]
    [Algebra R₂ A₅] {σ₁ σ₂ : R₁ →+* R₁} {σ₃ σ₄ : R₁ →+* R₂} {σ₅ : R₂ →+* R₂} {a : A₁ →+* A₂} {b : A₂ →+* A₃}
    {c : A₃ →+* A₄} {d : A₁ →+* A₅} {e : A₅ →+* A₄} (ha : SemiHom σ₁ a) (hb : SemiHom σ₂ b) (hc : SemiHom σ₃ c)
    (hd : SemiHom σ₄ d) (he : SemiHom σ₅ e) (h : ∀ x, c (b (a x)) = e (d x)) (x : Ω[A₁⁄R₁]) :
    hc.m1 (hb.m1 (ha.m1 x)) = he.m1 (hd.m1 x) := by
  rw [SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) (fun _ ↦ rfl), SemiHom.oneFormMap_comp_oneFormMap _ _ (ha.comp hb) (fun _ ↦ rfl)]
  exact SemiHom.oneFormMap_comp_oneFormMap _ _ (hd.comp he) h x

theorem isPull1_of_pair_coboundary : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G), (∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) = Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a)) → ∀ (k : (KK D.κ D.t).Z1) (k' : (KK D'.κ D'.t).Z1) (w : cechDeRhamTotalCocyclesOne (OAff D.s)) (w' : cechDeRhamTotalCocyclesOne (OAff D'.s)), Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k.1) w.1 → Λ'.Res1 (((KK D'.κ D'.t).resMap Λ'.L).p1 k'.1) w'.1 → ∀ g, ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D0 g = ((pairB Λ' φ m).pre θ).p1 k.1 - ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p1 k'.1 → IsPull1 hφ (Hyp1.mk _ w) (Hyp1.mk _ w') := by
  intro D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg
  unfold IsPull1
  rw [pullHyp1_mk, pullHyp1_mk, Hyp1.mk_eq_mk]
  refine ⟨fun p ↦ (Λ'.e (Opposite.op p.unop.1.1)).symm (g p), Tot1.ext (fun p q a ↦ ?_) fun p ↦ ?_⟩
  · let B : Type := (Λ'.L.obj (Opposite.op q.unop.1.1)).B
    have e : @HSub.hSub B B B _ (g q) ((Λ'.L.map ((pairFst φ).map a)).φ (g p)) =
        @HSub.hSub B B B _ ((θ.app q).φ (k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a))))
          (k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a))) :=
      congrArg (fun c ↦ c.1 p q a) hg
    have h1 : k.1.1 _ _ (Λ.L.map ((pairSnd φ).map a)) =
        Λ.e (Opposite.op q.unop.1.2) (w.1.1 _ _ ((pairSnd φ).map a)) := hw.1 _ _ _
    have h2 : k'.1.1 _ _ (Λ'.L.map ((pairFst φ).map a)) =
        Λ'.e (Opposite.op q.unop.1.1) (w'.1.1 _ _ ((pairFst φ).map a)) := hw'.1 _ _ _
    have h3 := Λ'.nat ((pairFst φ).map a) ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))
    have h4 := hθ q (w.1.1 _ _ ((pairSnd φ).map a))
    apply (Λ'.e (Opposite.op q.unop.1.1)).injective
    refine ((map_sub _ _ _).trans ?_).trans (map_sub _ _ _).symm
    refine (congrArg₂ (fun x y : B ↦ x - y) (AlgEquiv.apply_symm_apply _ _) (h3.trans
      (congrArg _ (AlgEquiv.apply_symm_apply _ _)))).trans (e.trans ?_)
    exact congrArg₂ (fun x y : B ↦ x - y) ((congrArg (θ.app q).φ h1).trans h4) h2
  · let B : Type := K1 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ
    have e : kd0 D'.R (Λ'.L.obj (Opposite.op p.unop.1.1)).δ (g p) =
        @HSub.hSub B B B _ (km1 (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (morDP m _)
          (km1 (SemiHom.of_algHom (θ.app p).φ) (θ.app p).dp
          (k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2))))) (k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1))) :=
      congrArg (fun c ↦ c.2 p) hg
    have h1 : k.1.2 (Λ.L.obj (Opposite.op p.unop.1.2)) =
        Submodule.Quotient.mk ((Λ.semi _).m1 (w.1.2 (Opposite.op p.unop.1.2))) := hw.2 _
    have h2 : k'.1.2 (Λ'.L.obj (Opposite.op p.unop.1.1)) =
        Submodule.Quotient.mk ((Λ'.semi _).m1 (w'.1.2 (Opposite.op p.unop.1.1))) := hw'.2 _
    rw [h1, h2] at e
    apply (_root_.GlobalTheory.PDForm.lift_forms_bij D' Λ' (Opposite.op p.unop.1.1)).1.1
    have h3 : (Λ'.semi (Opposite.op p.unop.1.1)).m1 (KaehlerDifferential.D D'.R _
        ((Λ'.e (Opposite.op p.unop.1.1)).symm (g p))) = KaehlerDifferential.D D'.R _ (g p) :=
      (SemiHom.m1_D _ _).trans (congrArg _ ((Λ'.e _).apply_symm_apply _))
    have h4 := kaehlerDifferential_map_commutative_pentagon (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      (morSemi m (Λ'.L.obj (Opposite.op p.unop.1.1))) (semiHom_secPull hφ p.unop)
      (Λ'.semi (Opposite.op p.unop.1.1)) (hθ p) (w.1.2 (Opposite.op p.unop.1.2))
    have h5 : q1 (pairRes φ D'.s) p (w'.1.2 (Opposite.op p.unop.1.1)) = w'.1.2 (Opposite.op p.unop.1.1) :=
      cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) p _
    refine (congrArg Submodule.Quotient.mk h3).trans (e.trans ?_)
    refine (Submodule.Quotient.mk_sub _).symm.trans (congrArg Submodule.Quotient.mk ?_)
    refine Eq.trans ?_ (map_sub _ _ _).symm
    exact congrArg₂ (· - ·) h4 (congrArg (Λ'.semi (Opposite.op p.unop.1.1)).m1 h5.symm)

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamDegreeTwoClassPullbackOfCoboundary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.PullTwo

section Lift

variable {D : Data} (Λ : Lift D)

def j1 (U : AffOp D.X) : Ω[Sec D.s U.unop.1⁄D.R] →+ K1 D.R (Λ.L.obj U).δ where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).m1 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add (f := _), Submodule.Quotient.mk_add]

def j2 (U : AffOp D.X) : Om D.R (Sec D.s U.unop.1) 2 →+ K D.R (Λ.L.obj U).δ 2 where
  toFun ω := Submodule.Quotient.mk ((Λ.semi U).mOm 2 ω)
  map_zero' := by rw [map_zero, Submodule.Quotient.mk_zero]
  map_add' a b := by rw [map_add (f := _), Submodule.Quotient.mk_add]

theorem compatibleOneFormClass_restriction_natural {U V : AffOp D.X} (a : U ⟶ V) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j1 Λ V (p1 (OAff D.s) a ω) = km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi V).m1 ((semiHom_mp (OAff D.s) a).m1 ω)) : K1 D.R (Λ.L.obj V).δ) =
    km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [divPowerCompatOneFormMap_mk]
  congr 1
  rw [SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun _ ↦ rfl),
    SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom (Λ.L.map a).φ) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
      (fun b ↦ (Λ.nat a b).symm)]

theorem compatibleOneFormClass_kaehler_differential (U : AffOp D.X) (b : Sec D.s U.unop.1) :
    j1 Λ U (KaehlerDifferential.D D.R _ b) = kd0 D.R (Λ.L.obj U).δ (Λ.e U b) := by
  show (Submodule.Quotient.mk ((Λ.semi U).m1 (KaehlerDifferential.D D.R _ b)) : K1 D.R (Λ.L.obj U).δ) = _
  rw [SemiHom.m1_D, divPowerCompatFunctionDifferential_apply]
  all_goals rfl

theorem compatibleTwoFormClass_exterior_derivative (U : AffOp D.X) (ω : Ω[Sec D.s U.unop.1⁄D.R]) :
    j2 Λ U (dOne D.R _ ω) = kd1 D.R (Λ.L.obj U).δ (j1 Λ U ω) := by
  show (Submodule.Quotient.mk ((Λ.semi U).mOm 2 (dOne D.R _ ω)) : K D.R (Λ.L.obj U).δ 2) =
    kd1 D.R (Λ.L.obj U).δ (Submodule.Quotient.mk ((Λ.semi U).m1 ω))
  rw [SemiHom.mOm_dOne, divPowerCompatOneFormDerivative_mk]

end Lift

section Pull

variable {D D' : Data} (Λ : Lift D) (Λ' : Lift D') {σ : D.R →+* D'.R} {φ : D'.X ⟶ D.X} {φ₀ : D'.X₀ ⟶ D.X₀}
  (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
  (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
    Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))

include hθ

theorem movedDatum_compatibleOneFormClass (p : (Pair φ)ᵒᵖ) (ω : Ω[Sec D.s p.unop.1.2.1⁄D.R]) :
    ((pairB Λ' φ m).pre θ).a1 p (j1 Λ (Opposite.op p.unop.1.2) ω) =
      j1 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).m1 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg (morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).m1 (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.oneFormMap_comp_oneFormMap (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

theorem movedDatum_compatibleTwoFormClass (p : (Pair φ)ᵒᵖ) (ω : Om D.R (Sec D.s p.unop.1.2.1) 2) :
    ((pairB Λ' φ m).pre θ).a2 p (j2 Λ (Opposite.op p.unop.1.2) ω) =
      j2 Λ' (Opposite.op p.unop.1.1) ((semiHom_secPull hφ p.unop).mOm 2 ω) := by
  exact congrArg Submodule.Quotient.mk
    (((congrArg ((morSemi m ((pairFst φ ⋙ Λ'.L).obj p)).mOm 2) (SemiHom.mOm_mOm (Λ.semi (Opposite.op p.unop.1.2)) (SemiHom.of_algHom (θ.app p).φ)
      ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (fun _ ↦ rfl) ω)).trans
      (SemiHom.mOm_mOm ((Λ.semi (Opposite.op p.unop.1.2)).comp (SemiHom.of_algHom (θ.app p).φ)) (morSemi m ((pairFst φ ⋙ Λ'.L).obj p))
        ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1))) (fun b ↦ hθ p b) ω)).trans
      (SemiHom.mOm_mOm (semiHom_secPull hφ p.unop) (Λ'.semi (Opposite.op p.unop.1.1)) ((semiHom_secPull hφ p.unop).comp (Λ'.semi (Opposite.op p.unop.1.1)))
        (fun _ ↦ rfl) ω).symm)

end Pull

section Pairs

variable {D D' : Data} (Λ' : Lift D') (φ : D'.X ⟶ D.X)

abbrev Kp : Cx (Pair φ)ᵒᵖ := (KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)

def i0 (p : (Pair φ)ᵒᵖ) : (OPair φ D'.s).obj p →+ (Kp Λ' φ).M0.obj p :=
  (Λ'.e ((pairFst φ).obj p)).toAddEquiv.toAddMonoidHom

def i1 (p : (Pair φ)ᵒᵖ) : Ω[(OPair φ D'.s).obj p⁄D'.R] →+ (Kp Λ' φ).M1.obj p := j1 Λ' ((pairFst φ).obj p)

def i2 (p : (Pair φ)ᵒᵖ) : Om D'.R ((OPair φ D'.s).obj p) 2 →+ (Kp Λ' φ).M2.obj p := j2 Λ' ((pairFst φ).obj p)

variable {φ}

theorem pairFirstOpenFunctionSections_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : (OPair φ D'.s).obj p) :
    i0 Λ' φ q (mp (OPair φ D'.s) a x) = (Kp Λ' φ).M0.map a (i0 Λ' φ p x) := Λ'.nat ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_natural {p q : (Pair φ)ᵒᵖ} (a : p ⟶ q) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i1 Λ' φ q (p1 (OPair φ D'.s) a x) = (Kp Λ' φ).M1.map a (i1 Λ' φ p x) := compatibleOneFormClass_restriction_natural Λ' ((pairFst φ).map a) x

theorem pairFirstOpenOneForms_kaehler_differential (p : (Pair φ)ᵒᵖ) (x : (OPair φ D'.s).obj p) :
    i1 Λ' φ p (KaehlerDifferential.D D'.R _ x) = (Kp Λ' φ).d0 p (i0 Λ' φ p x) := compatibleOneFormClass_kaehler_differential Λ' _ x

theorem pairFirstOpenTwoForms_exterior_derivative (p : (Pair φ)ᵒᵖ) (x : Ω[(OPair φ D'.s).obj p⁄D'.R]) :
    i2 Λ' φ p (dOne D'.R _ x) = (Kp Λ' φ).d1 p (i1 Λ' φ p x) := compatibleTwoFormClass_exterior_derivative Λ' _ x

def Cor (k : (Kp Λ' φ).T2) (w : Tot2 (OPair φ D'.s)) : Prop :=
  (∀ p q r a b, i0 Λ' φ r (w.1 p q r a b) = k.1 p q r a b) ∧ (∀ p q a, i1 Λ' φ q (w.2.1 p q a) = k.2.1 p q a) ∧
    ∀ p, i2 Λ' φ p (w.2.2 p) = k.2.2 p

theorem Cor.sub {k k' : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k' w') :
    Cor Λ' (k - k') (w - w') := by
  unfold Cor at h h' ⊢
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · simp only [Prod.fst_sub, Pi.sub_apply, map_sub, h1, h1']
  · simp only [Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, map_sub, h2, h2']
  · simp only [Prod.snd_sub, Pi.sub_apply, map_sub, h3, h3']

theorem deRhamCochainCorrespondence_degree_one_coboundary {g : (Kp Λ' φ).T1} {c : Tot1 (OPair φ D'.s)} (hf : ∀ p q a, i0 Λ' φ q (c.1 p q a) = g.1 p q a)
    (hω : ∀ p, i1 Λ' φ p (c.2 p) = g.2 p) : Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamTotalDifferentialOne_functionPart, map_add (f := _), map_sub, pairFirstOpenFunctionSections_natural, hf, hf, hf]
    all_goals rfl
  · rw [dTot1_a, map_sub, map_sub, hω, pairFirstOpenOneForms_natural, hω, pairFirstOpenOneForms_kaehler_differential, hf]
    all_goals rfl
  · rw [dTot1_η, pairFirstOpenTwoForms_exterior_derivative, hω]
    all_goals rfl

theorem Cor.unique {k : (Kp Λ' φ).T2} {w w' : Tot2 (OPair φ D'.s)} (h : Cor Λ' k w) (h' : Cor Λ' k w') : w = w' := by
  unfold Cor at h h'
  have e0 : ∀ p, Function.Injective (i0 Λ' φ p) := fun p ↦ (Λ'.e _).injective
  have e1 : ∀ p, Function.Injective (i1 Λ' φ p) := fun p ↦ (_root_.GlobalTheory.PDForm.lift_forms_bij D' Λ' _).1.1
  have e2 : ∀ p, Function.Injective (i2 Λ' φ p) := fun p ↦ (_root_.GlobalTheory.PDForm.lift_forms_bij D' Λ' _).2.1
  exact Tot2.ext (fun p q r a b ↦ e0 r ((h.1 p q r a b).trans (h'.1 p q r a b).symm))
    (fun p q a ↦ e1 q ((h.2.1 p q a).trans (h'.2.1 p q a).symm))
    (fun p ↦ e2 p ((h.2.2 p).trans (h'.2.2 p).symm))

theorem cor_res {k' : (KK D'.κ D'.t).T2} {w' : Tot2 (OAff D'.s)}
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k') w') :
    Cor Λ' (((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k') (pullTot2 (pairRes φ D'.s) w') := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    exact (hw'.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    exact (congrArg (i1 Λ' φ q) (cechDeRhamCoefMapOneForms_restrictAlongFunctor (OAff D'.s) (pairFst φ) q _)).trans (hw'.2.1 _ _ _).symm
  · rw [pullTot2_η]
    exact (congrArg (i2 Λ' φ p) (qOm_restrict (OAff D'.s) (pairFst φ) p _)).trans (hw'.2.2 _).symm

theorem cor_pull (Λ : Lift D) {σ : D.R →+* D'.R} {φ₀ : D'.X₀ ⟶ D.X₀}
    (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀) (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    {k : (KK D.κ D.t).T2} {w : Tot2 (OAff D.s)} (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k) w) :
    Cor Λ' (((pairB Λ' φ m).pre θ).p2 k) (pullTot2 (pairPull hφ) w) := by
  unfold Cor
  refine ⟨fun p q r a b ↦ ?_, fun p q a ↦ ?_, fun p ↦ ?_⟩
  · rw [cechDeRhamPullbackTotalDegreeTwo_function_part]
    refine (hθ r _).symm.trans ?_
    exact congrArg (fun y ↦ (θ.app r).φ y) (hw.1 _ _ _ _ _).symm
  · rw [pullTot2_a]
    refine (movedDatum_compatibleOneFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) q _).symm.trans ?_
    exact congrArg _ (hw.2.1 _ _ _).symm
  · rw [pullTot2_η]
    refine (movedDatum_compatibleTwoFormClass (Λ := Λ) (Λ' := Λ') (hφ := hφ) (m := m) (θ := θ) (hθ := hθ) p _).symm.trans ?_
    exact congrArg _ (hw.2.2 _).symm

theorem exists_deRhamCochainCorrespondence_degree_one (g : (Kp Λ' φ).T1) : ∃ c : Tot1 (OPair φ D'.s), Cor Λ' ((Kp Λ' φ).D1 g) (dTot1 _ c) := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ∀ (p q : (Pair φ)ᵒᵖ) (_ : p ⟶ q), (OPair φ D'.s).obj q,
      ∀ p q a, i0 Λ' φ q (c1 p q a) = g.1 p q a :=
    ⟨fun p q a ↦ (Λ'.e _).symm (g.1 p q a), fun p q a ↦ (Λ'.e _).apply_symm_apply _⟩
  choose c2 hc2 using fun p ↦ (_root_.GlobalTheory.PDForm.lift_forms_bij D' Λ' ((pairFst φ).obj p)).1.2 (g.2 p)
  exact ⟨(c1, c2), deRhamCochainCorrespondence_degree_one_coboundary Λ' (c := (c1, c2)) hc1 hc2⟩

set_option maxHeartbeats 1000000 in
private theorem isPull2_aux_lemma (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := by
  have h1 := cor_pull Λ' Λ hφ m θ hθ hw
  have h2 := cor_res Λ' (φ := φ) hw'
  obtain ⟨c, hc⟩ := exists_deRhamCochainCorrespondence_degree_one Λ' g
  rw [hg] at hc
  have h3 := Cor.unique Λ' hc (Cor.sub Λ' h1 h2)
  unfold IsPull2
  rw [pullHyp2_mk, pullHyp2_mk, Hyp2.mk_eq_mk]
  refine ⟨c, ?_⟩
  rw [coe_pullZZ2, coe_pullZZ2]
  exact h3

end Pairs

theorem isPull2_of_coboundary (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X)
    (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀)
    (θ : pairSnd φ ⋙ Λ.L ⟶ (pairB Λ' φ m).G)
    (hθ : ∀ (p : (Pair φ)ᵒᵖ) a, (θ.app p).φ (Λ.e (Opposite.op p.unop.1.2) a) =
      Λ'.e (Opposite.op p.unop.1.1) (GlobalTheory.CechDR.secPull D.s D'.s p.unop a))
    (k : (KK D.κ D.t).Z2) (k' : (KK D'.κ D'.t).Z2) (w : cechDeRhamTotalCocyclesTwo (OAff D.s)) (w' : cechDeRhamTotalCocyclesTwo (OAff D'.s))
    (hw : Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 k.1) w.1)
    (hw' : Λ'.Res2 (((KK D'.κ D'.t).resMap Λ'.L).p2 k'.1) w'.1)
    (g : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).T1)
    (hg : ((KK D'.κ D'.t).res (pairFst φ ⋙ Λ'.L)).D1 g = ((pairB Λ' φ m).pre θ).p2 k.1 -
      ((KK D'.κ D'.t).resMap (pairFst φ ⋙ Λ'.L)).p2 k'.1) :
    IsPull2 hφ (Hyp2.mk _ w) (Hyp2.mk _ w') := isPull2_aux_lemma D D' Λ Λ' σ φ φ₀ hφ m θ hθ k k' w w' hw hw' g hg

end GlobalTheory.PDForm.PullTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperIdentificationChainAgreesGenerically
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.tied_chain_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D w₁ w₂ hT c₀ hc R' fg frac hth hev ρ' G _ α β h1 c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ G₂ _
    α₂ β₂ h2
  obtain ⟨mT, pT, bT, tT⟩ := hT
  obtain ⟨m₁, p₁, b₁, t₁⟩ := h1
  obtain ⟨m₂, p₂, b₂, t₂⟩ := h2
  refine ⟨w₂.G, inferInstance, mT ≫ m₁, m₂, ?_, p₂, ?_, ?_⟩
  · exact (pT.comp p₁).congr (Geo.Tor.spMap_comp (ratHull R').val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · rw [Category.assoc, b₁, bT, b₂]
  · intro x
    obtain ⟨w, hw, hw'⟩ := tT x
    obtain ⟨w₁', hw₁, hw₁'⟩ := t₁ x
    obtain ⟨w₂', hw₂, hw₂'⟩ := t₂ (D.lab x)
    have s0 : w ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w _ hw'
    have s1 : w₁' ≫ w₁.G.hom = 𝟙 _ := SameChain.sec_of_pt X₁.ρ w₁.α w₁.hα.1 w₁' _ hw₁
    have s2 : w₂' ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w₂' _ hw₂
    have hwm : w ≫ mT = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁' := by
      apply w₁.hα.1.hom_ext
      · rw [Category.assoc, hw, Category.assoc, hw₁]
      · rw [Category.assoc, pT.1.w, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w = w₂' := by
      apply w₂.hα.1.hom_ext
      · rw [hw', hw₂]
      · rw [s0, s2]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, ← Category.assoc, hwm]
      simp only [Category.assoc]
      rw [hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁), Category.assoc]
    · rw [hwe, hw₂']
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegDataFromLowerBaseAfterMonomialExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.PrimCocycle
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullFrom

theorem exists_cart_of_pullDeg : ∀ {V V₁ V₂ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing V₂] [IsDomain V₂] (D : DegPre V) (f₁ : V →+* V₁) (f₂ : V₁ →+* V₂) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.P.A.left) (D' : DegPre V₂) (hD : IsPullDeg (f₂.comp f₁) D D'), IsGrpPullback B' D.P.A (spMap f₁) β' → ∃ Φ : D'.P.A.left ⟶ B'.left, IsGrpPullback D'.P.A B' (spMap f₂) Φ ∧ Φ ≫ β' = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁)) ∧ ∀ (a : D'.X) (y : 𝟙_ (Over (Sp V₁)) ⟶ B'), y.left ≫ β' = spMap f₁ ≫ (D.c (hD.xe a)).left → (D'.c a).left ≫ Φ = spMap f₂ ≫ y.left := by
  intro V V₁ V₂ _ _ _ _ _ _ D f₁ f₂ B' _ β' D' hD gp'
  have gp := pull_grp hD
  have hsp : spMap f₂ ≫ spMap f₁ = spMap (f₂.comp f₁) := GlobalTheory.HalfBC.spMap_comp_spMap' f₁ f₂
  have w₀ : (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (f₂.comp f₁))) ≫ D.P.A.hom =
      (D'.P.A.hom ≫ spMap f₂) ≫ spMap f₁ := by
    rw [gp.1.w, Category.assoc, hsp]
  refine ⟨gp'.1.lift _ _ w₀, ?_, gp'.1.lift_fst _ _ w₀, fun a y hy => ?_⟩
  · exact IsGrpPullback.cancel gp' (gp.congr hsp.symm (gp'.1.lift_fst _ _ w₀).symm) (gp'.1.lift_snd _ _ w₀)
  · apply gp'.1.hom_ext
    · rw [Category.assoc, gp'.1.lift_fst, Category.assoc, hy, ← Category.assoc (spMap f₂), hsp]
      exact hD.c_pr a
    · rw [Category.assoc, gp'.1.lift_snd, Category.assoc, Over.w y, ← Category.assoc, Over.w (D'.c a)]
      rfl

theorem degFrom_of_periodRel : ∀ (n : ℕ) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegData V (maximalIdeal V)) (r : ℕ) (e₀ : (Fin r → ℤ) ≃+ D.toPre.X) (L : LowBase (zetaAway n) n) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (f₁ : V →+* V₁) (κ₁ : L.W →+* V₁) (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)) (B' : Over (Sp V₁)) [GrpObj B'] (β' : B'.left ⟶ D.toPre.P.A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 D.toPre.P.A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsCN V → IsDiscreteValuationRing V → IsCN V₁ → IsDiscreteValuationRing V₁ → Function.Injective f₁ → f₁.Finite → IsLocalHom f₁ → IsLocalHom κ₁ → IsGrpPullback B' D.toPre.P.A (spMap f₁) β' → IsGrpPullback B' L.T.B (spMap κ₁) β'' → IsSquare β' β₂ → IsSquare β'' β₂' → ∀ (x : (Fin L.T.r → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ B')), (∀ a, (x a).left ≫ β' = spMap f₁ ≫ (D.toPre.c (e₀ (e a))).left ∧ (x a).left ≫ β'' = spMap κ₁ ≫ (L.T.c₀ ((n : ℤ) • a)).left) → ∀ (w₁ : LB.Iso ((abelian₂ D.toPre.P.A D.toPre.P.L).pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂')) (q : (Fin L.T.r → ℤ) → (Fin L.T.r → ℤ) → (FractionRing V₁)ˣ), w₁.IsGen → PeriodRel D.toPre L.T f₁ κ₁ w₁ (e.trans e₀) x n q → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (f₂ : V₁ →+* V₂) (fK : FractionRing V₁ →+* FractionRing V₂) {I : Type} [Fintype I] (s : I → V₂) (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)), IsCN V₂ → Function.Injective f₂ → f₂.Finite → IsLocalHom f₂ → (∀ a, fK (algebraMap V₁ _ a) = algebraMap V₂ _ (f₂ a)) → (∀ a b, fK (q a b : FractionRing V₁) = ∏ k, algebraMap V₂ _ (s k) ^ ((n : ℤ) * ε k a b)) → ∀ (D' : DegData V₂ (maximalIdeal V₂)) (hD : IsPullDeg (f₂.comp f₁) D.toPre D'.toPre), DegFrom L.T (f₂.comp κ₁) s ε n D'.toPre (hD.xe.trans (e₀.symm.trans e.symm)) := by
  intro n V _ _ _ D r e₀ L V₁ _ _ _ f₁ κ₁ e B' _ β' β'' β₂ β₂' hV hVd hV₁ hV₁d hf₁i hf₁f hf₁l hκ₁l gp' gp'' sq' sq'' x hx w₁ q hw₁ hPR V₂ _ _ _ f₂ fK I _ s ε hV₂ hf₂i hf₂f hf₂l hfK hq D' hD
  obtain ⟨Φ, gΦ, hΦ, hc₀⟩ := exists_cart_of_pullDeg D.toPre f₁ f₂ B' β' D'.toPre hD gp'
  have hc : ∀ a, (D'.toPre.c a).left ≫ Φ = spMap f₂ ≫ (x (hD.xe.trans (e₀.symm.trans e.symm) a)).left := fun a =>
    hc₀ a _ (by
      have := (hx (hD.xe.trans (e₀.symm.trans e.symm) a)).1
      simpa using this)
  have hΛD : (abelian₂ D.toPre.P.A D.toPre.P.L).IsLB := DVR.linComb_isLB _ D.toPre.P.isLB _ _
  obtain ⟨w, hw, hval⟩ := _root_.GlobalTheory.LamPullComp.lamIso_comp_pull D.toPre.P.A B' D'.toPre.P.A L.T.B (spMap f₁) (spMap f₂) β' Φ (GlobalTheory.PsiEvenPull.proj hD) β₂ β₂'
    D.toPre.P.L D'.toPre.P.L L.T.M.L gp' gΦ sq' hΦ D.toPre.P.isLB D'.toPre.P.isLB L.T.M.isLB hD.w w₁ hD.w_gen hw₁
  have hsp : spMap f₂ ≫ spMap κ₁ = spMap (f₂.comp κ₁) := GlobalTheory.HalfBC.spMap_comp_spMap' κ₁ f₂
  refine ⟨Wit.ofDeg D'.toPre D'.tau_bimult, AddEquiv.refl _, Wit.refines_ofDeg _ _, Φ ≫ β'', GlobalTheory.HalfBC.sqOf gΦ ≫ β₂', w,
    (IsGrpPullback.comp gΦ gp'').congr hsp rfl, ⟨?_, ?_⟩, hw, fun a => ?_, fun a b => ?_⟩
  · have e₁ : GlobalTheory.HalfBC.sqOf gΦ ≫ (fst B' B').left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_fst (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (fst L.T.B L.T.B).left = (fst D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.1, ← Category.assoc, e₁, Category.assoc]
  · have e₂ : GlobalTheory.HalfBC.sqOf gΦ ≫ (snd B' B').left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ :=
      congrArg (fun z => z.left) (lift_snd (pushPt gΦ.1.w (fst D'.toPre.P.A D'.toPre.P.A)) (pushPt gΦ.1.w (snd D'.toPre.P.A D'.toPre.P.A)))
    show (GlobalTheory.HalfBC.sqOf gΦ ≫ β₂') ≫ (snd L.T.B L.T.B).left = (snd D'.toPre.P.A D'.toPre.P.A).left ≫ Φ ≫ β''
    rw [Category.assoc, sq''.2, ← Category.assoc, e₂, Category.assoc]
  · refine (congrArg (· ≫ β'') (hc a)).trans ?_
    rw [Category.assoc, (hx _).2, ← Category.assoc, hsp]
    rfl
  · obtain ⟨k, hk, hk'⟩ := _root_.GlobalTheory.PeriodPull.periods_pull n V D.toPre r e₀ L.T V₁ f₁ κ₁ e B' β₂ β₂' x w₁ q hf₁i hPR V₂ f₂ fK s ε hfK hq D'.toPre hD Φ gΦ hc w hval a b
    refine ⟨k, hk, fun z J J' hJ hJ' => ?_⟩
    refine ((Wit.exists_tau D'.toPre a b).choose_spec.2 _ _ z J' hJ').trans ?_
    exact hk' z J J' hJ hJ'

end GlobalTheory.PullFrom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCDvrOfIsDiscreteValuationRing
section
namespace GlobalTheory.DvrCompletion

theorem exists_cDvr_of_isDiscreteValuationRing : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ ι : A →+* V, Function.Injective ι ∧ IsLocalHom ι := by
  intro A _ _ _ _
  obtain ⟨V, _, _, _, ι, h, h1, h2⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom A
  exact ⟨V, inferInstance, inferInstance, inferInstance, h, ι, h1, h2⟩

end GlobalTheory.DvrCompletion
end

