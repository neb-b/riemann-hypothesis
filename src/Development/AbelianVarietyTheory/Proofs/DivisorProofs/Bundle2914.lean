module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2884
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem rank_le (hn : 3 ≤ n) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := _root_.GlobalTheory.Poinc.Trait.finrank_le_of_three_le g n F hn T

theorem lam (hE : IsE8 W) (hT : ThetaInt F W i) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) : ∃ C : ℝ, ∀ (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X), x ≠ 0 →
      ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁), Real.exp (-(C * (c.sc * c.T.β x x))) ≤ ‖c.val h‖ :=
  _root_.GlobalTheory.Poinc.LamBound.main _ n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm hE hT X₁.projM p z₁ hz

variable {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}

def evC (c : CTrait X₁ p z₁) : X₁.M.Z.presheaf.stalk z₁ →+* PadicAlgCl p :=
  (RatModel.valHomOf (gPt p ≫ c.y) z₁ (RatModel.gPt_specializes c.cen)).comp (X₁.M.stalkEquiv z₁).toRingHom

theorem evC_apply (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : evC c a = c.val a := rfl

theorem norm_evC_le (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) : ‖evC c a‖ ≤ 1 :=
  RatModel.norm_val_le_one c.cen (X₁.M.stalkEquiv z₁ a).2

theorem norm_evC_lt (c : CTrait X₁ p z₁) (a : X₁.M.Z.presheaf.stalk z₁) (ha : a ∈ maximalIdeal _) :
    ‖evC c a‖ < 1 := by
  have h1 : ¬ IsUnit (X₁.M.stalkEquiv z₁ a) := fun hu => ha ((isUnit_map_iff (X₁.M.stalkEquiv z₁) a).1 hu)
  exact (RatModel.norm_val_lt_one_iff c.cen (X₁.M.stalkEquiv z₁ a).2).2 h1

theorem sc_pos (c : CTrait X₁ p z₁) : 0 < c.sc := by
  have hϖ0 : algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 c.T.irr.ne_zero
  have h0 : c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ < 1 := by
    by_contra hge
    push_neg at hge
    have hinv : ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ hge
    obtain ⟨w, hw⟩ := (c.int _).1 hinv
    apply c.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective c.T.V (FractionRing c.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold CTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem beta_pos (c : CTrait X₁ p z₁) (x : c.T.D.toPre.X) (hx : x ≠ 0) : 0 < c.T.β x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal c.T.V).ne_top c.T.mono hx
  fin_cases j
  simpa using hj

end GlobalTheory.Poinc.PreSys

namespace GlobalTheory.Poinc.PreSys

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}


variable (X₁ p) in
abbrev Key : Type := (Sp (OO p) ⟶ X₁.M.Z) × (Σ k : ℕ, (Fin k → ℤ) → (Fin k → ℤ) → ℝ)

def Rep (c : CTrait X₁ p z₁) (q : Key X₁ p) : Prop :=
  c.y = q.1 ∧ ∃ e : (Fin q.2.1 → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X, ∀ u v, q.2.2 u v = c.sc * c.T.β (e u) (e v)

def coord (c : CTrait X₁ p z₁) : (Fin (Module.finrank ℤ c.T.D.toPre.X) → ℤ) ≃ₗ[ℤ] c.T.D.toPre.X :=
  (Module.finBasis ℤ c.T.D.toPre.X).equivFun.symm

def keyOf (c : CTrait X₁ p z₁) : Key X₁ p :=
  (c.y, ⟨Module.finrank ℤ c.T.D.toPre.X, fun u v => c.sc * c.T.β (coord c u) (coord c v)⟩)

theorem rep_keyOf (c : CTrait X₁ p z₁) : Rep c (keyOf c) := ⟨rfl, coord c, fun _ _ => rfl⟩


variable (X₁ p z₁) in
def Pts : Type := {q : Key X₁ p // ∃ c : CTrait X₁ p z₁, Rep c q}

noncomputable def pick (y : Pts X₁ p z₁) : CTrait X₁ p z₁ := Classical.choose y.2

theorem pick_rep (y : Pts X₁ p z₁) : Rep (pick y) y.1 := Classical.choose_spec y.2


variable (X₁ p z₁) in
noncomputable def sys : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁) where
  Y := Pts X₁ p z₁
  ev y := evC (pick y)
  ev_le y h := norm_evC_le _ h
  ev_lt y h hh := norm_evC_lt _ h hh
  X y := (pick y).T.D.toPre.X
  rank_le y := rank_le X₁.three_le _
  β y := (pick y).T.β
  bal y := ⟨(pick y).T.symm, fun a u v => by simp⟩
  pos y x hx := beta_pos _ x hx
  sc y := (pick y).sc
  sc_pos y := sc_pos _

theorem sys_matches : (sys X₁ p z₁ (g := g)).Matches := by
  intro c
  refine ⟨⟨keyOf c, c, rep_keyOf c⟩, fun a => ?_, ?_⟩
  · obtain ⟨hy, -⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    show evC _ a = c.val a
    rw [evC_apply]
    unfold CTrait.val
    rw [hy]
    rfl
  · obtain ⟨-, e', he'⟩ := pick_rep ⟨keyOf c, c, rep_keyOf c⟩
    have key : ∀ a b : (pick ⟨keyOf c, c, rep_keyOf c⟩).T.D.toPre.X,
        (pick ⟨keyOf c, c, rep_keyOf c⟩).sc * (pick ⟨keyOf c, c, rep_keyOf c⟩).T.β a b =
          c.sc * c.T.β (coord c (e'.symm a)) (coord c (e'.symm b)) := by
      intro a b
      have h := he' (e'.symm a) (e'.symm b)
      rw [e'.apply_symm_apply, e'.apply_symm_apply] at h
      exact h.symm
    exact ⟨e'.symm.trans (coord c), key⟩

theorem sys_lam (hE : IsE8 W) (hT : ThetaInt F W i) (hz : IsClosed ({z₁} : Set X₁.M.Z)) :
    (sys X₁ p z₁ (g := g)).abelian₂ := by
  obtain ⟨C, hC⟩ := lam hE hT X₁ p z₁ hz
  exact ⟨C, fun y x hx => by
    obtain ⟨h, hm, hle⟩ := hC (pick y) x hx
    exact ⟨h, hm, hle⟩⟩

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z),
    IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z), IsClosed ({z₁} : Set X₁.M.Z) →
      ∃ Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁), Φ.Matches ∧ Φ.abelian₂ ∧
        (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X,
          ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) := by
  intro g n F W Z i hE hT X₁ p _ z₁ hz
  exact ⟨sys X₁ p z₁, sys_matches, sys_lam hE hT hz, fun y => ⟨pick y, fun a => rfl, LinearEquiv.refl ℤ _,
    fun a b => rfl⟩⟩

end GlobalTheory.Poinc.PreSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemePullbackAdjointEndomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.EndLoc.AdjClosed

variable {S : Scheme.{0}}

theorem hom_ext_sq {A : Over S} {X : Scheme.{0}} {u v : X ⟶ (A ⊗ A).left}
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have p : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  exact p.hom_ext h₁ h₂

theorem comm_left {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A' ≫ g) (snd A' A')).left ≫ φ₂ = φ₂ ≫ (lift (fst A A ≫ f) (snd A A)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, hsq.2]

theorem comm_right {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A') (snd A' A' ≫ g)).left ≫ φ₂ = φ₂ ≫ (lift (fst A A) (snd A A ≫ f)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.2]

end GlobalTheory.EndLoc.AdjClosed


open GlobalTheory.EndLoc.AdjClosed in
theorem GlobalTheory.EndLoc.exists_closed_adj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ _ Q hA hQ h0l h0r hsym hamp f f' hf hf'
  let β := (lift (fst A A ≫ f) (snd A A)).left
  let β' := (lift (fst A A) (snd A A ≫ f')).left
  let N := LB.LinComb Q (K := Fin 2) ![β, β'] ![1, -1]
  have hN : N.IsLB := LB.isLB_linComb hQ _ _
  have hc : cls N hN = pull β (cls Q hQ) - pull β' (cls Q hQ) := by
    rw [cls_linComb hQ]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  have hrig : Out.Rigidified (A ⊗ A) N := by
    have e : η[A ⊗ A] ≫ lift (fst A A ≫ f) (snd A A) = η[A ⊗ A] ≫ lift (fst A A) (snd A A ≫ f') := by
      have h₁ : η[A ⊗ A] ≫ fst A A = η[A] := IsMonHom.one_hom (fst A A)
      have h₂ : η[A ⊗ A] ≫ snd A A = η[A] := IsMonHom.one_hom (snd A A)
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, h₁, IsMonHom.one_hom]
      · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, h₂, IsMonHom.one_hom]
    have e' : eSec (A ⊗ A) ≫ β = eSec (A ⊗ A) ≫ β' := by
      simp only [eSec, β, β', ← Over.comp_left, e]
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, hc, map_sub, ← pull_comp, ← pull_comp, e', sub_self]
  let L₀ := Out.boxLB (Q.pull (lift (𝟙 A) (𝟙 A)).left) (GlobalTheory.SquarePol.sqIsPowGrp A).pr
  have hL₀ : L₀.IsLB := LB.isLB_linComb (pull_isLB hQ _) _ _
  have hamp₀ : Out.RelAmple (A ⊗ A) L₀ :=
    GlobalTheory.relAmple_boxLB S _ A 2 (GlobalTheory.SquarePol.sqIsPowGrp A) _ (pull_isLB hQ _) hamp
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨Z, i, hi, hZ⟩ := _root_.GlobalTheory.TrivLocus.trivLocus_closed_of_relAmple S (A ⊗ A) L₀ N hAA hL₀ hamp₀ hN hrig
  refine ⟨Z, i, hi, fun T t A' _ _ φ' φ₂' g g' hpb hsq hg hg' => ?_⟩
  have hpb₂ := GlobalTheory.WeilIntegral.isGrpPullback_prod hpb hpb hsq.1 hsq.2
  rw [← hZ T t (A' ⊗ A') φ₂' hpb₂, ← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, hc, map_sub, ← pull_comp,
    ← pull_comp, ← comm_left hsq f g hg, ← comm_right hsq f' g' hg', pull_comp, pull_comp, sub_eq_zero,
    ← cls_eq_iff (pull_isLB (pull_isLB hQ _) _) (pull_isLB (pull_isLB hQ _) _)]
  rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreDerivationOfTwoDualNumberPullbacks
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.KS.TwoPull

variable {X Y Z : Scheme.{0}}

theorem pull_pull (f : Z ⟶ Y) (g : Y ⟶ X) (h : Z ⟶ X) (e : f ≫ g = h) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (e₃ : W ≤ h ⁻¹ᵁ U) (a : Γ(X, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom a) = (h.appLE U W e₃).hom a := by
  subst e
  exact congrArg (fun φ => φ.hom a) (Scheme.Hom.appLE_comp_appLE f g U V W e₁ e₂)

theorem res_pull (φ : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((φ.appLE U V h).hom a) = (φ.appLE U W (h'.trans h)).hom a :=
  congrArg (fun q => q.hom a) (φ.appLE_map h (homOfLE h').op)

theorem pull_res (φ : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U') (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.appLE U' V h).hom (resG X h' a) = (φ.appLE U V (h.trans fun _ hy => h' hy)).hom a :=
  congrArg (fun q => q.hom a) (φ.map_appLE h (homOfLE h').op)

theorem app_res (φ : Y ⟶ X) {U U' : X.Opens} (h' : U' ≤ U) (a : Γ(X, U)) :
    (φ.app U').hom (resG X h' a) = resG Y (fun _ hy => h' hy) ((φ.app U).hom a) := by
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE]
  exact (pull_res φ _ _ _).trans (res_pull φ _ _ _).symm

theorem id_pull {U : X.Opens} (h : U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U) (a : Γ(X, U)) :
    ((𝟙 X : X ⟶ X).appLE U U h).hom a = a := by
  have : (𝟙 X : X ⟶ X).appLE U U h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (X.presheaf.map_id _)
  rw [this]
  rfl

theorem spec_pull_inv {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (e : ⊤ ≤ spMap f ⁻¹ᵁ ⊤)
    (r : R) :
    ((spMap f).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (f r) := by
  have h := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  have h2 : (spMap f).appLE ⊤ ⊤ e = (spMap f).appTop := (Scheme.Hom.app_eq_appLE (spMap f) (U := ⊤)).symm
  rw [h2]
  exact h.symm

theorem pull_const {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (φ : Y ⟶ X) (p : X ⟶ Sp R)
    (p' : Y ⟶ Sp R') (hφ : φ ≫ p = p' ≫ spMap f) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (r : R) :
    (φ.appLE U V h).hom (constFn p U r) = constFn p' V (f r) := by
  unfold constFn
  rw [← spec_pull_inv f le_top r]
  exact (pull_pull φ p _ hφ _ _ le_top _).trans (pull_pull p' (spMap f) _ rfl _ _ _ _).symm

theorem res_const {R : Type} [CommRing R] (q : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    resG X h (constFn q U a) = constFn q V a :=
  res_pull q _ h _

def twoPullConstantsRingHom {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (q.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem const_eq {R : Type} [CommRing R] (q : X ⟶ Sp R) (U : X.Opens) (a : R) :
    constFn q U a = twoPullConstantsRingHom q U a := rfl

theorem dual_decomp {k : Type} [Field k] (x : DualNumber k) :
    x = algebraMap k (DualNumber k) x.fst + DualNumber.eps * algebraMap k (DualNumber k) x.snd := by
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.KS.TwoPull


open GlobalTheory.KS.TwoPull in
theorem GlobalTheory.KS.TwoPull.exists_locDerK_of_two_pullbacks : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∃ d : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.A.hom m₀ (fun r => (ρ r).snd) ⊤ d ∧ (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (d W f) (π₂ ⁻¹ᵁ W)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ hπ₁ hπ₂ hagr A₀ _ m₀ hm₀ pr hpr hprA
  subst hpr
  have hsp : spMap (constHom ρ) =
      spMap (algebraMap k (DualNumber k)) ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    rw [← spMap_comp]; rfl
  have hpb : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) := by
    refine IsPullback.of_right ?_ hprA hm₀.1
    rw [← hsp]; exact hπ₂.1
  have hid : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← spMap_comp]
    have : ((TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k))) = RingHom.id k := by
      ext x; simp [TrivSqZeroExt.algebraMap_eq_inl]
    rw [this]; simp [spMap]
  have hcomp : 𝟙 A₀.left ≫ A₀.hom =
      (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ spMap (algebraMap k (DualNumber k)) := by
    rw [Category.assoc, hid, Category.id_comp, Category.comp_id]
  set j := hpb.lift (𝟙 _) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) hcomp with hjdef
  have hjρ : j ≫ pr = 𝟙 _ := hpb.lift_fst _ _ _
  have hjπ : j ≫ B'.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := hpb.lift_snd _ _ _
  have hm : j ≫ π₁ = m₀ := by
    rw [hagr _ j A₀.hom hjπ, ← Category.assoc, hjρ, Category.id_comp]
  have hp : π₁ ≫ P.A.hom = B'.hom ≫ spMap ρ := hπ₁.1.w
  have hW : ∀ W : P.A.left.Opens, pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) = π₁ ⁻¹ᵁ W := fun W =>
    (_root_.GlobalTheory.LogKS.preimage_eq_of_agree_closedFibre k _ _ B'.hom π₁ (pr ≫ m₀) hagr W).symm
  have hdec := _root_.GlobalTheory.EpsThick.existsUnique_add_eps_mul_of_field k A₀.left B'.left A₀.hom B'.hom pr hpb
  have uniq : ∀ (O : A₀.left.Opens) (a b a' b' : Γ(A₀.left, O)),
      (pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b =
        (pr.app O).hom a' + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b' → b = b' := fun O a b a' b' h =>
    congrArg Prod.snd ((hdec O ((pr.app O).hom a + constFn B'.hom _ DualNumber.eps * (pr.app O).hom b)).unique
      (y₁ := (a, b)) (y₂ := (a', b')) rfl h)
  have ex : ∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), ∃ b : Γ(A₀.left, m₀ ⁻¹ᵁ W),
      (π₁.appLE W _ (hW W).le).hom f = (pr.app _).hom ((m₀.app W).hom f) +
        constFn B'.hom _ DualNumber.eps * (pr.app _).hom b := by
    intro W f
    obtain ⟨⟨a, b⟩, hab, -⟩ := hdec (m₀ ⁻¹ᵁ W) ((π₁.appLE W _ (hW W).le).hom f)
    refine ⟨b, ?_⟩
    have hle : m₀ ⁻¹ᵁ W ≤ j ⁻¹ᵁ (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) := by
      rw [← Scheme.Hom.comp_preimage, hjρ]; exact le_rfl
    have h1 := congrArg (j.appLE _ _ hle).hom hab
    rw [map_add (f := _), map_mul, pull_const _ j B'.hom A₀.hom hjπ, pull_pull j π₁ m₀ hm _ _ le_rfl] at h1
    have h2 : (j.appLE _ _ hle).hom ((pr.app (m₀ ⁻¹ᵁ W)).hom a) = a := by
      rw [Scheme.Hom.app_eq_appLE]
      exact (pull_pull j pr (𝟙 _) hjρ (U := m₀ ⁻¹ᵁ W) (W := m₀ ⁻¹ᵁ W) le_rfl hle le_rfl a).trans (id_pull _ a)
    have h3 : constFn A₀.hom (m₀ ⁻¹ᵁ W) ((TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps) = 0 := by
      have : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
      rw [this, const_eq, map_zero]
    have h4 : (m₀.app W).hom f = a := by
      rw [Scheme.Hom.app_eq_appLE]
      refine h1.trans ?_
      rw [h3, zero_mul, add_zero]
      exact h2
    rw [h4]
    exact hab
  choose d hd using ex
  have hee : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 := fun O => by
    rw [const_eq, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  refine ⟨d, ⟨fun W _ f f' => ?_, fun W _ f f' => ?_, fun W W' h _ f => ?_, fun W _ r => ?_⟩, ?_⟩
  · refine uniq _ ((m₀.app W).hom (f + f')) _ ((m₀.app W).hom (f + f')) _ ?_
    rw [← hd, map_add (f := _), hd, hd]
    simp only [map_add (f := _)]
    ring
  · refine uniq _ ((m₀.app W).hom (f * f')) _ ((m₀.app W).hom (f * f')) _ ?_
    rw [← hd, map_mul, hd, hd]
    simp only [map_add (f := _), map_mul]
    linear_combination (pr.app _).hom (d W f) * (pr.app _).hom (d W f') * hee _
  · have h0 : m₀ ⁻¹ᵁ W' ≤ m₀ ⁻¹ᵁ W := fun _ hy => h hy
    rw [show rsT (d W f) (m₀ ⁻¹ᵁ W') = resG _ h0 (d W f) from dif_pos h0]
    refine uniq _ ((m₀.app W').hom (resG _ h f)) _ ((m₀.app W').hom (resG _ h f)) _ ?_
    have h0' : pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W') ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun _ hy => h hy
    have h1 := congrArg (resG _ h0') (hd W f)
    rw [res_pull, map_add (f := _), map_mul, res_const] at h1
    rw [← hd, pull_res]
    refine h1.trans ?_
    rw [app_res m₀ h f]
    exact congrArg₂ (· + ·) (app_res pr h0 _).symm (congrArg (_ * ·) (app_res pr h0 _).symm)
  · refine uniq _ ((m₀.app W).hom (constFn P.A.hom W r)) _ (constFn A₀.hom _ (ρ r).fst) _ ?_
    rw [← hd, pull_const ρ π₁ P.A.hom B'.hom hp, Scheme.Hom.app_eq_appLE, pull_const _ pr A₀.hom B'.hom hpb.w,
      pull_const _ pr A₀.hom B'.hom hpb.w]
    simp only [const_eq]
    rw [← map_mul, ← map_add (f := _)]
    exact congrArg _ (dual_decomp _)
  · intro W f
    show pbT π₁ f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT (pr ≫ m₀) f (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) +
      constFn B'.hom (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) DualNumber.eps * pbT pr (d W f) (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W))
    unfold pbT
    rw [dif_pos (hW W).le, dif_pos le_rfl, dif_pos (show pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) ≤ (pr ≫ m₀) ⁻¹ᵁ W from le_rfl), hd W f, Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE,
      pull_pull pr m₀ (pr ≫ m₀) rfl]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataAStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringOfIntegers_module_on_tensor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  first | exact @GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | exact GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data | (intros; apply GlobalTheory.TensAct.exists_integer_ring_action_on_tensor_degeneration_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RayTan

theorem smooth_H : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Smooth Y.H.hom := by
  intro R _ _ Q O _ _ _ oa Y
  have h1 : Smooth Y.q.left := Y.smooth_q
  have := Q.P.smoothDim
  have h2 : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
  rw [← Over.w Y.q]
  infer_instance

theorem exists_basis_isInv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  intro R _ _ _ _ Q O _ _ _ oa Y
  obtain ⟨n, ⟨v⟩⟩ := _root_.GlobalTheory.TanBasis.exists_basis_tanM R Y.H (smooth_H R Q O oa Y)
  choose dd hdd using fun a => _root_.GlobalTheory.InvFieldBase.exists_isInv R Y.H (v a)
  exact ⟨n, v, dd, hdd⟩

end GlobalTheory.RayTan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalRepresentingSchemeHomFixedPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_representing_scheme_homFixedPullback : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∀ p : Sp Rg, ∃ U : (Sp Rg).Opens, p ∈ U ∧ ∃ (AU : Over (U).toScheme) (_ : GrpObj AU) (BU : Over (U).toScheme) (_ : GrpObj BU) (φA : AU.left ⟶ A.left) (φB : BU.left ⟶ B.left), IsGrpPullback AU A (U).ι φA ∧ IsGrpPullback BU B (U).ι φB ∧ ∃ R : HomFixRep AU BU (L.pull φA) (M.pull φB), QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  first | (exact @GlobalTheory.HomFixLocal.exists_local_homFixRep) | (exact GlobalTheory.HomFixLocal.exists_local_homFixRep) | (intros; apply GlobalTheory.HomFixLocal.exists_local_homFixRep  <;> assumption)
end

