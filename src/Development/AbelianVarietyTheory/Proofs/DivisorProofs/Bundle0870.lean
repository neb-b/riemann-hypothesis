module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  GlobalTheory.FieldBC
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} {r n : ℕ}

def unfExt (hle : c.F ≤ c'.F) {σ : c.F →+* ℂ} (σ' : c'.F →+* ℂ) (hσ : ∀ a, σ' (incF c c' hle a) = σ a)
    (U : Unf Xo c σ r) : Unf Xo c' σ' r :=
  letI : Algebra c.F (CAt σ') := σ.toAlgebra
  { Comp := U.Comp
    fin := U.fin
    X := U.X
    un := fun k x => FrPt.ext hle (S := CAt σ') hσ (U.un k x) }

def covBC (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F) : DeltaDat Xo c' n :=
  { ddBC hle d with cδ := ((show (covCoeff hle d).F from u) • rulBC (le_covCoeff hle d) d.cδ : Rul d.Xo₂ (covCoeff hle d)) }

def covUnf (hle : c.F ≤ c'.F) (d : DeltaDat Xo c n) (u : c'.F)
    (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) :
    Unf (covBC hle d u).Xo₂ (covBC hle d u).c₂
      (c'.F.val.toRingHom.comp ((covBC hle d u).eF.symm : (covBC hle d u).c₂.F →+* c'.F)) r :=
  unfExt (le_covCoeff hle d) _ (fun _ => rfl) U₂

end Gen

section Val

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r : ℕ}

def CXiAt {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) : Prop :=
  IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif d.Xo₂ ((σ0.comp (d.eF.symm : d.c₂.F →+* c.F)).comp
          (IntermediateField.inclusion d.c₂.le).toRingHom)
        (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
      (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
      (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
      ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
        rdU U₂ d.cδ (dict₂ h).1 (dict₂ h).2 =
          c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ)

theorem cXiVal_iff {c : Coeff l} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) {Tup : Type} (dδ : Tup → DeltaDat Xo c n)
    (U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r)
    (dict₂ : ∀ t, GA D V → Σ k, Frame ((U₂ t).X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (xi : Tup → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) :
    CXiVal V hr σ0 dδ U₂ dict₂ ι x₀ xi ↔ ∃ c0 : ℂ, (∃ m : ℕ, 0 < m ∧ c0 ^ m = 1) ∧
      ∀ t, CXiAt V hr σ0 (dδ t) (U₂ t) (dict₂ t) ι x₀ (xi t) c0 := Iff.rfl

end Val

end GlobalTheory.OneMapAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonGaugeBiadditiveOfLogSumActionLinear
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.GaugeBiadd

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.LawLog
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

section

variable {C : Type} [Field C] {d : ℕ} {σ : Type}

def famPt {n : ℕ} (x : Fin n → Fin d → MvPowerSeries σ C) : Fin n × Fin d → MvPowerSeries σ C :=
  fun q => x q.1 q.2

theorem hs_famPt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) :
    HasSubst (famPt x) :=
  hasSubst_of_constantCoeff_zero fun q => hx q.1 q.2

theorem constantCoeff_vecCons_pair_eq_zero {τ : Type} {x y : Fin d → MvPowerSeries τ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (j : Fin 2) (i : Fin d) :
    constantCoeff ((![x, y] : Fin 2 → Fin d → MvPowerSeries τ C) j i) = 0 := by
  fin_cases j
  exacts [hx i, hy i]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt C d j i) = 0 := by simp [pt]

theorem constantCoeff_germEvalPair_eq_zero {n : ℕ} {x y : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) {f : PS C 2 d} (hf : constantCoeff f = 0) :
    constantCoeff (ev ![x, y] f) = 0 :=
  constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero hx hy)) (fun q => constantCoeff_vecCons_pair_eq_zero hx hy q.1 q.2) hf

theorem cc_comp1 {n : ℕ} {x : Pt C n d} (hx : ∀ i, constantCoeff (x i) = 0)
    {φ : Pt C 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin d) :
    constantCoeff (comp1 φ x i) = 0 := by
  have h : ∀ (j : Fin 1) i, constantCoeff ((![x] : Fin 1 → Pt C n d) j i) = 0 := fun j i => by
    fin_cases j; exact hx i
  exact constantCoeff_subst_eq_zero (hs_famPt h) (fun q => h q.1 q.2) (hφ i)

theorem subst_famPt_pt {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (j : Fin n) : (fun i => (subst (famPt x) (pt C d j i) : MvPowerSeries σ C)) = x j :=
  funext fun i => subst_X (hs_famPt hx) _

theorem subst_pointFamily_germEvalPair {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    {a b : Pt C n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (f : PS C 2 d) :
    (subst (famPt x) (ev ![a, b] f) : MvPowerSeries σ C) =
      subst (famPt ![fun i => (subst (famPt x) (a i) : MvPowerSeries σ C), fun i => subst (famPt x) (b i)]) f := by
  refine (subst_comp_subst_apply (hs_famPt (constantCoeff_vecCons_pair_eq_zero ha hb)) (hs_famPt hx) f).trans ?_
  congr 1
  funext ⟨j, i⟩
  fin_cases j <;> rfl

theorem subst_famPt_comp1 {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0)
    (φ : Pt C 1 d) (j : Fin n) :
    (fun i => (subst (famPt x) (comp1 φ (pt C d j) i) : MvPowerSeries σ C)) =
      fun i => subst (fun q : Fin 1 × Fin d => x j q.2) (φ i) := by
  have h : ∀ (l : Fin 1) i, constantCoeff ((![pt C d j] : Fin 1 → Pt C n d) l i) = 0 := fun l i => by
    fin_cases l; exact cc_pt j i
  funext i
  refine (subst_comp_subst_apply (hs_famPt h) (hs_famPt hx) (φ i)).trans ?_
  congr 1
  funext ⟨l, e⟩
  fin_cases l
  exact subst_X (hs_famPt hx) _

theorem subst_elim_twoVars {x y : Fin d → MvPowerSeries σ C} (hx : ∀ i, constantCoeff (x i) = 0)
    (hy : ∀ i, constantCoeff (y i) = 0) (f : PS C 2 d) :
    (subst (Sum.elim x y) (subst (twoVars C d) f) : MvPowerSeries σ C) = subst (famPt ![x, y]) f := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (i | i); exacts [hx i, hy i])
  rw [subst_comp_subst_apply hs_twoVars hs]
  congr 1
  funext ⟨j, i⟩
  rw [twoVars, subst_X hs]
  fin_cases j <;> simp [famPt]

theorem logUnit_subst [CharZero C] {v : AddValuation C (WithTop ℝ)} {n : ℕ}
    {x : Fin n → Fin d → MvPowerSeries σ C} (hx : ∀ j i, constantCoeff (x j i) = 0) (hI : ∀ j i, MvIsInt v (x j i))
    {U f : PS C n d} (hU : MvIsInt v U) (hf : constantCoeff f = 0) (e : U = FB.expS C f) :
    LogUnit v (subst (famPt x) f : MvPowerSeries σ C) := by
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt hx) (fun q => hx q.1 q.2) hf, ?_⟩
  have h := ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v hU (a := famPt x) (fun q => hI q.1 q.2) (fun q => hx q.1 q.2)
  rw [e] at h
  unfold FB.expS PowerSeries.subst at h
  rw [subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const (hs_famPt hx)] at h
  exact h

end

theorem biadd_of_add_of_act : AddSt → ActSt → BiaddSt := by
  intro hAdd hAct C _ _ v d R _ _ O _ _ B hB h H σ _ w w' z hw hw' hz
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis H.ax0
  have hF : ∀ i, constantCoeff (B.FK C i) = 0 := GlobalTheory.GaugeBaseChange.gp_FK B
  have hA : ∀ a i, constantCoeff (B.actK C a i) = 0 := fun a => GlobalTheory.GaugeBaseChange.gp_actK B a
  have cw := cc_expPt (fglOf hB) hw.1
  have cw' := cc_expPt (fglOf hB) hw'.1
  have cz := cc_expPt (fglOf hB) hz.1
  have hadd : expPt (fglOf hB) (w + w') =
      fun i => subst (famPt ![expPt (fglOf hB) w, expPt (fglOf hB) w']) (B.FK C i) := by
    rw [(hAdd C v d (fglOf hB) σ).2.1 w w' hw.1 hw'.1]
    funext i
    exact subst_elim_twoVars cw cw' (B.FK C i)
  have cA : ∀ {n : ℕ} (j l : Fin n) i, constantCoeff (addOf (B.FK C) (pt C d j) (pt C d l) i) = 0 :=
    fun j l i => constantCoeff_germEvalPair_eq_zero (cc_pt j) (cc_pt l) (hF i)
  have sA : ∀ {n : ℕ} {x : Fin n → Fin d → MvPowerSeries σ C} (_ : ∀ j i, constantCoeff (x j i) = 0) (j l : Fin n),
      (fun i => (subst (famPt x) (addOf (B.FK C) (pt C d j) (pt C d l) i) : MvPowerSeries σ C)) =
        fun i => subst (famPt ![x j, x l]) (B.FK C i) := fun hx j l => by
    funext i
    unfold addOf
    rw [subst_pointFamily_germEvalPair hx (cc_pt j) (cc_pt l), subst_famPt_pt hx, subst_famPt_pt hx]
  refine ⟨constantCoeff_subst_eq_zero (hs_famPt (constantCoeff_vecCons_pair_eq_zero cw cz)) (fun q => constantCoeff_vecCons_pair_eq_zero cw cz q.1 q.2) hc, ?_, ?_,
    fun a => ?_⟩
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) w, expPt (fglOf hB) w', expPt (fglOf hB) z] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cw i, cw' i, cz i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hw'.2 i, hz.2 i]) hB.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cA _ _) (cc_pt _) hc]; simp) H.ph1
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cA _ _) (cc_pt _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx : ∀ (j : Fin 3) i, constantCoeff ((![expPt (fglOf hB) z, expPt (fglOf hB) w, expPt (fglOf hB) w'] :
        Fin 3 → Fin d → MvPowerSeries σ C) j i) = 0 := fun j i => by
      fin_cases j; exacts [cz i, cw i, cw' i]
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hz.2 i, hw.2 i, hw'.2 i]) hB.2.2.2.1
      (by rw [map_sub, map_add (f := _), constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc, constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cA _ _) hc]; simp) H.ph2
    rw [subst_sub (hs_famPt hx), subst_add (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_pt _), subst_pointFamily_germEvalPair hx (cc_pt _) (cA _ _), sA hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [hadd]
    exact k
  · have hx := constantCoeff_vecCons_pair_eq_zero cw cz
    have k := logUnit_subst (v := v) hx (fun j i => by fin_cases j; exacts [hw.2 i, hz.2 i]) (hB.2.2.2.2 a)
      (by rw [map_sub, constantCoeff_germEvalPair_eq_zero (cc_comp1 (cc_pt _) (hA _)) (cc_pt _) hc,
        constantCoeff_germEvalPair_eq_zero (cc_pt _) (cc_comp1 (cc_pt _) (hA _)) hc]; simp) (H.ad a)
    rw [subst_sub (hs_famPt hx), subst_pointFamily_germEvalPair hx (cc_comp1 (cc_pt _) (hA _)) (cc_pt _),
      subst_pointFamily_germEvalPair hx (cc_pt _) (cc_comp1 (cc_pt _) (hA _)), subst_famPt_comp1 hx, subst_famPt_comp1 hx] at k
    simp only [subst_famPt_pt hx] at k
    unfold pairSer
    rw [(hAct C v d R O B hB σ a).1 w hw.1, (hAct C v d R O B hB σ (star a)).1 z hz.1]
    exact k

end GlobalTheory.IsoTriv.GaugeBiadd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionOfProperFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.FibreTorsion

theorem card_torsion_of_proper_fibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ (F : Type) [Field F] [IsAlgClosed F] (p : Sp F ⟶ S), IsProper (pullback.snd G.hom p) → ∀ N : ℕ, (N : F) ≠ 0 → Nat.card {x : Over.mk p ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
  intro S G _ _ hG g hg F _ _ p hprop N hN
  let B := (Over.pullback p).obj G
  haveI : IsProper B.hom := hprop
  have hB : IsAbelianScheme B :=
    AbelianSchemeGerms.isAbelianScheme_of_proper B (IsSemiAbelian.pullback p G hG)
  have hg' : SmoothOfRelativeDimension g B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  have h := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional F B g N hB hg' hN
  have hp := isGrpPullback_pullback G p
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp F)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom p = y.left ≫ pullback.fst G.hom p := congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp F))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Nat.card {x : Over.mk ((𝟙_ (Over (Sp F))).hom ≫ p) ⟶ G // x ^ N = 1} = N ^ (2 * g) := by
    rw [← h]
    refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
    show x ^ N = 1 ↔ e x ^ N = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp F))).hom ≫ p = p := Category.id_comp p
  rw [h3] at h2
  exact h2

end GlobalTheory.FibreTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyPsiEqMapMinpoly
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem charpoly_psi_eq_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C)
    (hdeg : (minpoly G.F γ).natDegree = G.n) :
    (G.psi v γ).charpoly = (minpoly G.F γ).map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) ((minpoly G.F γ).map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : ((minpoly G.F γ).map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : ((minpoly G.F γ).map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem charpoly_psi_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (g : G.C),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).Separable → (G.psi v g).charpoly.Separable := by
  intro p _ G v g hdeg hsep
  rw [charpoly_psi_eq_map_minpoly G v g hdeg]
  exact hsep.map

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTensorLeftMulConjOneTmul
section
open GlobalTheory.LKTrip GlobalTheory.LKMid
open scoped TensorProduct Classical

namespace GlobalTheory

theorem conj_one_tmul_charpoly : ∀ (R : Type) [CommRing R] [Algebra ℚ R] (A : Type) [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] (x : (R ⊗[ℚ] A)ˣ) (y : A), (LevelExists.mulMatAlg R A ((x : R ⊗[ℚ] A) * (1 ⊗ₜ[ℚ] y) * ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A))).charpoly = (LinearMap.mulLeft ℚ y).charpoly.map (algebraMap ℚ R) := by
  intro R _ _ A _ _ _ x y
  set b := Module.finBasis ℚ A
  set u := Units.map (LevelExists.mulMatAlg R A).toMonoidHom x with hu
  have h1 : LevelExists.mulMatAlg R A (x : R ⊗[ℚ] A) = (u : Matrix _ _ R) := rfl
  have h2 : LevelExists.mulMatAlg R A ((x⁻¹ : (R ⊗[ℚ] A)ˣ) : R ⊗[ℚ] A) = ((u⁻¹ : (Matrix _ _ R)ˣ) : Matrix _ _ R) := by
    rw [hu, ← map_inv]; rfl
  have hM : LevelExists.mulMatAlg R A (1 ⊗ₜ[ℚ] y) =
      (LinearMap.toMatrix b b (LinearMap.mulLeft ℚ y)).map (algebraMap ℚ R) := by
    ext i j
    simp [LevelExists.mulMatAlg, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply,
      Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_repr_tmul, b, Algebra.leftMulMatrix_eq_repr_mul]
  rw [map_mul, map_mul, h1, h2, Matrix.coe_units_inv, Matrix.charpoly_units_conj, hM, Matrix.charpoly_map,
    LinearMap.charpoly_toMatrix]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldConjExtendsOfAdjoinAbsSq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem cm_conj_extends_of_adjoin :
    ∀ (F M : Type) [Field F] [NumberField F] [IsCMField F] [Field M] [NumberField M] [Algebra F M]
      (π : M) (c : ℚ), Algebra.adjoin F {π} = ⊤ → c ≠ 0 → (∀ φ : M →+* ℂ, ‖φ π‖ ^ 2 = (c : ℝ)) →
      ∃ σ : M →+* M, (∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x)) ∧
        σ π * π = (c : M) ∧ ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x) := by
  intro F M _ _ _ _ _ _ π c hadj hc hπ

  have gen : ∀ S : Subring M, (∀ x : F, algebraMap F M x ∈ S) → π ∈ S → ∀ y : M, y ∈ S := by
    intro S hS hpS y
    let A : Subalgebra F M := { S with algebraMap_mem' := hS }
    have hle : Algebra.adjoin F {π} ≤ A := Algebra.adjoin_le (Set.singleton_subset_iff.mpr (show π ∈ A from hpS))
    rw [hadj] at hle
    exact hle (Algebra.mem_top (x := y))

  have hconj : ∀ φ : M →+* ℂ, φ π ≠ 0 ∧ (starRingEnd ℂ) (φ π) = φ ((c : M) / π) := by
    intro φ
    have hn : Complex.normSq (φ π) = (c : ℝ) := by rw [← Complex.sq_norm]; exact hπ φ
    have hne : φ π ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hn
      exact hc (by exact_mod_cast hn.symm)
    refine ⟨hne, ?_⟩
    rw [map_div₀, map_ratCast, eq_div_iff hne, mul_comm, Complex.mul_conj, hn]
    norm_cast
  obtain ⟨φ₀⟩ : Nonempty (M →+* ℂ) := inferInstance
  let ψ : M →+* ℂ := (starRingEnd ℂ).comp φ₀
  have hrange : ∀ y : M, ψ y ∈ φ₀.range := by
    refine gen (Subring.comap ψ φ₀.range) ?_ ?_
    · intro x
      show ψ (algebraMap F M x) ∈ φ₀.range
      refine ⟨algebraMap F M (IsCMField.complexConj F x), ?_⟩
      exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x)
    · show ψ π ∈ φ₀.range
      exact ⟨(c : M) / π, ((hconj φ₀).2).symm⟩
  let e : M ≃+* φ₀.range := RingEquiv.ofBijective φ₀.rangeRestrict
    ⟨fun a b h => φ₀.injective (congrArg Subtype.val h), φ₀.rangeRestrict_surjective⟩
  let σ : M →+* M := e.symm.toRingHom.comp (ψ.codRestrict φ₀.range hrange)
  have hσ0 : ∀ x : M, φ₀ (σ x) = (starRingEnd ℂ) (φ₀ x) := by
    intro x
    have h1 : e (σ x) = ψ.codRestrict φ₀.range hrange x := by simp [σ]
    have h2 : ((e (σ x) : φ₀.range) : ℂ) = ((ψ.codRestrict φ₀.range hrange x : φ₀.range) : ℂ) := congrArg Subtype.val h1
    exact h2
  have hσF : ∀ x : F, σ (algebraMap F M x) = algebraMap F M (IsCMField.complexConj F x) := by
    intro x
    apply φ₀.injective
    rw [hσ0]
    exact (IsCMField.complexEmbedding_complexConj F (φ₀.comp (algebraMap F M)) x).symm
  have hσπ : σ π = (c : M) / π := by
    apply φ₀.injective
    rw [hσ0]; exact (hconj φ₀).2
  have hπ0 : π ≠ 0 := fun h => (hconj φ₀).1 (by rw [h, map_zero])
  refine ⟨σ, hσF, ?_, ?_⟩
  · rw [hσπ, div_mul_cancel₀ _ hπ0]
  · intro φ
    have := gen (RingHom.eqLocus (φ.comp σ) ((starRingEnd ℂ).comp φ)) ?_ ?_
    · intro x; exact this x
    · intro x
      show φ (σ (algebraMap F M x)) = (starRingEnd ℂ) (φ (algebraMap F M x))
      rw [hσF]
      exact IsCMField.complexEmbedding_complexConj F (φ.comp (algebraMap F M)) x
    · show φ (σ π) = (starRingEnd ℂ) (φ π)
      rw [hσπ]; exact ((hconj φ).2).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenLevelConjCommensurable
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem level_conj_commensurable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (g : G.GAf),
    Subgroup.Commensurable (L.K.toSubgroup.map (MulAut.conj g).toMonoidHom) L.K.toSubgroup := by
  intro p _ G L g
  obtain ⟨hc', ho'⟩ := GlobalTheory.RelIndexCompact.conj_map_isCompact_isOpen L.K.toSubgroup g L.compact L.K.isOpen
  exact ⟨⟨GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open L.compact ho'⟩,
    ⟨GlobalTheory.RelIndexCompact.relIndex_ne_zero_of_compact_open hc' L.K.isOpen⟩⟩

end GlobalTheory.LKMid
end

