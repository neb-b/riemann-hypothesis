module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoTypeSpaceMaximalCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenFormsStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenForm_eq_finite_sum_autRep_eigenForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Wt E n) (C : Subgroup (UA E n)) (χ : C →* ℂˣ) (f : algForms W), (∀ (c : C) v g, f.1 v (g * c) = (χ c : ℂ) * f.1 v g) → ∃ (I : Finset (AutSub E n)) (F : AutSub E n → algForms W), (∀ π ∈ I, F π ∈ π.finPart W) ∧ (∀ π ∈ I, ∀ (c : C) v g, (F π).1 v (g * c) = (χ c : ℂ) * (F π).1 v g) ∧ f = ∑ π ∈ I, F π := by
  first | (exact @GlobalTheory.EigenDecomp.eigen_decomp) | (exact GlobalTheory.EigenDecomp.eigen_decomp) | (intros; apply GlobalTheory.EigenDecomp.eigen_decomp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFramesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberRepresentative_moved_at_twist_eq_tupleFrames : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∀ (k : GA B (B.R.N 0)), I.Reads u I.mu0 0 (fun _ => ()) (fun _ => F.to0.cls0.lev.Lb) (fun _ => F.to0.cls0.lev.U) (fun _ => F.to0.cls0.lev.chi) (fun c => (F.to0.cls0.y c).1) (fun c s => (F.to0.cls0.stabI c s).1) (fun _ => k) → ∀ c, ∃ κ : F.to0.cls0.lev.U, (∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) ∧ F.to0.cls0.lev.chi κ = 1 ∧ PtOf (B := B) ((show GA B (B.R.N 0) from (F.to0.cls0.y c).1 * κ.1) * k) (extTo I.SQ ((I.stp u a 0).rep (I.eCls0 l u a c)).1.1) := by
  first | exact @GlobalTheory.Mem.Col2.ZeroMove.main | exact GlobalTheory.Mem.Col2.ZeroMove.main | (intros; apply GlobalTheory.Mem.Col2.ZeroMove.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityEighth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.StrSplitDict.cast_ne_zero : ∀ (D : D7) (μ : D.what₂.Tup) (a b : ℕ) (h : a = b) (f : D.what₂.Mt μ a), f ≠ 0 → (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  intro D μ a b h f hf
  subst h
  exact hf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityFirst
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigSplit

open Formalism.IndefR.Links in
theorem cast_add {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (x y : D.what₂.Mt μ a) :
    (h ▸ (x + y) : D.what₂.Mt μ b) = (h ▸ x : D.what₂.Mt μ b) + (h ▸ y : D.what₂.Mt μ b) := by
  subst h; rfl

theorem cast_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) :
    (h ▸ (0 : D.what₂.Mt μ a) : D.what₂.Mt μ b) = 0 := by
  subst h; rfl

theorem cast_inj {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) {x y : D.what₂.Mt μ a}
    (hxy : (h ▸ x : D.what₂.Mt μ b) = (h ▸ y : D.what₂.Mt μ b)) : x = y := by
  subst h; exact hxy

theorem cast_symm {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (m : D.what₂.Mt μ b) :
    (h ▸ (h.symm ▸ m : D.what₂.Mt μ a) : D.what₂.Mt μ b) = m := by
  subst h; rfl

theorem fn_zero {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) : X.fn hμ j 0 = 0 := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem fn_add {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (x y : D.what₂.Mt μ (j.1 + 1)) :
    X.fn hμ j (x + y) = X.fn hμ j x + X.fn hμ j y := by
  unfold GlobalTheory.NJoin.RealAt.fn; simp; rfl

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem twist_eq {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (rr : G →* H) (F : H → W) (g γ : G) (h1 : ρ γ⁻¹ = 1) :
    ρ (g * γ)⁻¹ (F (rr (g * γ))) = ρ g⁻¹ (F (rr g * rr γ)) := by
  rw [mul_inv_rev, map_mul, map_mul, h1, one_mul]

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem transport {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  apply X.hinj j t
  funext g
  have e1 : X.R.extV j t (c • y) g = c • X.R.extV j t y g :=
    congrFun ((X.R.extV j t).map_smul c y) g
  have e3 : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) =
      (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g *
        (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict γ)) := by
    intro γ hγ
    exact twist_eq (X.R.cV j).ρ (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict ((X.R.HV j t).e y) g γ
      (hcv γ⁻¹ (inv_mem (rep_mem _ Pp d hγ)))
  have e2 : X.R.extV j t (h Pp (Finsupp.single d 1) y) g =
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) := by
    refine Eq.trans ?_ (Finset.sum_congr rfl e3).symm
    show (X.R.cV j).ρ g⁻¹ ((X.R.HV j t).e (h Pp (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g)) = _
    refine Eq.trans (congrArg ((X.R.cV j).ρ g⁻¹) (congrFun (hh Pp hG (Finsupp.single d 1) y)
      ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g))) ?_
    unfold GlobalTheory.Hk3.hkF
    exact (congrArg ((X.R.cV j).ρ g⁻¹) (sum_single_one d _)).trans (map_sum ((X.R.cV j).ρ g⁻¹) _ _)
  exact e2.trans ((hc g).trans e1.symm)

theorem eig_zero {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j 0 (g * γ) = c • X.fn hμ j 0 g := by
  intro g
  rw [fn_zero]
  simp

theorem eig_add {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (f₁ f₂ : D.what₂.Mt μ (j.1 + 1)) (h₁ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c • X.fn hμ j f₁ g) (h₂ : ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c • X.fn hμ j f₂ g) :
    ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j (f₁ + f₂) (g * γ) = c • X.fn hμ j (f₁ + f₂) g := by
  intro g
  rw [fn_add]
  simp only [Pi.add_apply, Finset.sum_add_distrib, smul_add, h₁ g, h₂ g]

theorem alongEig {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (Pp : DIV.Pl D.host.E) (d : List ℤ) (c : ℂ)
    (hc : ∀ Q : D.naut.AV i, D.naut.ptV i Q = some x → ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) :
    ∀ m ∈ eigC D.nd D.naut i x, ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g := by
  intro m hm
  unfold eigC at hm
  refine Submodule.iSup_induction (fun Q => ⨆ (_ : Q ∈ {P | D.naut.ptV i P = some x}), D.naut.typeV i Q)
    (motive := fun m => ∀ f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1),
      (hj ▸ f' : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) = m → ∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f' (g * γ) = c • X.fn hμ j f' g) hm ?_ ?_ ?_
  · intro Q m' hm' f' hf'
    by_cases hQ : D.naut.ptV i Q = some x
    · rw [iSup_pos (show Q ∈ {P | D.naut.ptV i P = some x} from hQ)] at hm'
      exact hc Q hQ f' (hf' ▸ hm')
    · rw [iSup_neg (show Q ∉ {P | D.naut.ptV i P = some x} from hQ), Submodule.mem_bot] at hm'
      have : f' = 0 := cast_inj hj (hf'.trans (hm'.trans (cast_zero hj).symm))
      subst this
      exact eig_zero X hμ j Pp d c
  · intro f' hf'
    have : f' = 0 := cast_inj hj (hf'.trans (cast_zero hj).symm)
    subst this
    exact eig_zero X hμ j Pp d c
  · intro m1 m2 ih1 ih2 f' hf'
    have hsplit : f' = (hj.symm ▸ m1 : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) + (hj.symm ▸ m2) := by
      apply cast_inj hj
      rw [hf', cast_add, cast_symm, cast_symm]
    subst hsplit
    exact eig_add X hμ j Pp d c _ _ (ih1 _ (cast_symm hj m1)) (ih2 _ (cast_symm hj m2))

end GlobalTheory.EigSplit
end

