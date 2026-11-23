module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0835
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharacterApplyEqLevelFunctionSwap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.SeriesTie.Scale

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.MtLatConj

variable {D : D7}

theorem locC_conj {τ : ℂ ≃+* ℂ} {ν ν' : Twist D Circle} (h : ConjChar τ ν ν') (hν : ν.Good) (hν' : ν'.Good)
    (PP : Pl D.host.E) (u : (kP PP)ˣ) : τ ((ν.locC PP u : ℂˣ) : ℂ) = ((ν'.locC PP u : ℂˣ) : ℂ) := by
  classical
  unfold Twist.locC
  by_cases hP : PP ∈ ν.Q
  · have hP' : PP ∈ ν'.Q := by rw [h.1]; exact hP
    rw [if_pos hP, if_pos hP']
    exact (h.res hν hν' hP u).symm
  · have hP' : PP ∉ ν'.Q := by rw [h.1]; exact hP
    rw [if_neg hP, if_neg hP']
    simp

theorem levPOf_ext1_apply_eq_units_map_inv {r : ℕ} {Pg : Finset (Pl D.host.E)} (P : LevelP Pg r ℂ) {τ : ℂ ≃+* ℂ}
    (hP : ∀ p, τ ((P.chi p : ℂˣ) : ℂ) = ((P.chi p : ℂˣ) : ℂ)) (g : G0 Pg r) :
    τ ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) = ((Formalism.L2.DIV.ext1 P.H P.chi g : ℂˣ) : ℂ) := by
  unfold Formalism.L2.DIV.ext1
  split_ifs
  · exact hP _
  · simp

theorem levFn_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (x : GL (Fin S.rank) (Lev.EAf D)) :
    τ ((levFn B.F.βS (B.levS ψ) x : ℂˣ) : ℂ) = ((levFn B.F.βS (B.levS ψ') x : ℂˣ) : ℂ) := by
  simp only [levFn, Base.levS, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rw [hcc.1]
  congr 1
  congr 1
  · exact levPOf_ext1_apply_eq_units_map_inv B.G.P hf.2.1 _
  · refine Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => ?_
    exact hf.2.2 PP hPP _
  · refine Finset.prod_congr rfl fun PP _ => ?_
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, map_mul,
      locC_conj hf.conjChar hB.de hB.de, locC_conj hcc hψ hψ']

theorem mem_levJ_of {S T : HSp D} (B : Base S T) {ψ ψ' : Twist D Circle} (hQ : ψ'.Q = ψ.Q) {k : Bridge.Gf S}
    (hk : k ∈ B.levJ ψ') : k ∈ B.levJ ψ := by
  simp only [Base.levJ, Subgroup.mem_comap, Lev.toAfE, mem_lev, mem_parLev, Base.levS] at hk ⊢
  rw [hQ] at hk
  exact hk

set_option maxHeartbeats 800000 in
theorem levelCharacter_apply_eq_levelFunction_swap {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) (k : B.levJ ψ) :
    B.levLam ψ k = levFn B.F.βS (B.levS ψ) (Formalism.UG.bc (Lev.swapAE D) k.1.1) := by
  unfold Base.levLam Lev.levCharAfE
  rfl

theorem levLam_conj {S T : HSp D} {B : Base S T} (hB : B.Good) {τ : ℂ ≃+* ℂ} {ψ ψ' : Twist D Circle} (hψ : ψ.Good)
    (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ) (k : B.levJ ψ') :
    ((B.levLam ψ' k : ℂˣ) : ℂ) = τ ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) := by
  rw [levelCharacter_apply_eq_levelFunction_swap, levelCharacter_apply_eq_levelFunction_swap]
  exact (levFn_conj hB hψ hψ' hcc hf _).symm

variable {n : ℕ}

def cmapGL (τ : ℂ ≃+* ℂ) : GLR D n →* GLR D n :=
  MonoidHom.pi fun t => (Units.map (RingHom.mapMatrix (τ : ℂ →+* ℂ) : Matrix (Fin n) (Fin n) ℂ →+* _).toMonoidHom).comp
    (Pi.evalMonoidHom (fun _ : D.what₂.Tau => GL (Fin n) ℂ) t)

theorem cmapGL_val (τ : ℂ ≃+* ℂ) (y : GLR D n) (t : D.what₂.Tau) (a b : Fin n) :
    ((cmapGL τ y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b = τ (((y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) := rfl

theorem coefFn_conj (τ : ℂ ≃+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Pol ℂ D.what₂.Tau n) (y : GLR D n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map (τ : ℂ →+* ℂ) F) y = τ (coefFn (RingHom.id ℂ) lam F (cmapGL τ.symm y)) := by
  simp only [coefFn, map_mul]
  congr 1
  · simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀,
      GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    have e := RingHom.map_det (τ : ℂ →+* ℂ) (((cmapGL τ.symm y t : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
    refine Eq.trans ?_ e.symm
    congr 1
    ext a b
    simp [cmapGL_val]
  · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_map]
    have e := MvPolynomial.hom_eval₂ F (RingHom.id ℂ) (τ : ℂ →+* ℂ)
      (fun v : D.what₂.Tau × Fin n × Fin n => ((cmapGL τ.symm y v.1 : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2)
    refine Eq.trans ?_ e.symm
    congr 1
    funext v
    simp [cmapGL_val]

theorem cmapGL_embGL (τ : ℂ ≃+* ℂ) (hτ : ∀ (t : D.what₂.Tau) (e : D.host.E), τ (tauE D t e) = tauE D t e)
    (g : GL (Fin n) D.host.E) : cmapGL τ (embGL (tauE D) g) = embGL (tauE D) g := by
  funext t
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [cmapGL_val]
  exact hτ t _

theorem hasLaw_conj {i : Fin D.R.m} {B : Base (Vc D i) (Wc D i)} (hB : B.Good)
    {Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank} {κ : ℂ} (hκ0 : κ ≠ 0) (hval : ∀ x, Φ x ∈ B.valSpace)
    (hκ : ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) =
      κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank))
    {τ : ℂ ≃+* ℂ} (hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e)
    {ψ ψ' : Twist D Circle} (hψ : ψ.Good) (hψ' : ψ'.Good) (hcc : ConjChar τ ψ ψ') (hf : FixDat B τ)
    {x x' : Bridge.Gf (Vc D i) → VsV D i ℂ} (hxx : ∀ h, ConjVec i τ (x h) (x' h))
    (hlaw : B.HasLaw ψ (fun h => Φ (x h))) : B.HasLaw ψ' (fun h => Φ ((τ κ / κ) • x' h)) := by
  intro γ h k
  have hfn : ∀ (w : VsV D i ℂ) z, harmFn (Wc D i).rank B.w B.F.BS (Φ w) z = κ * coefLin (lamV D i) w z :=
    fun w z => congrFun (hκ w) z
  obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat (Vc D i) γ γE := by
    obtain ⟨y, -, hy⟩ := γ.2
    exact ⟨y, hy.symm⟩
  set u := realGL B.F.θ (Vc D i) γ with hu_def
  have hu : u = embGL (tauE D) γE := realGL_rat hB.frame.vac.2.inf hγ
  have hact : ∀ P z, harmFn (Wc D i).rank B.w B.F.BS (B.act γ P) z =
      harmFn (Wc D i).rank B.w B.F.BS P (u⁻¹ * z) := fun P z => harmFn_fockGL _ _ _ _ _
  have hfix : ∀ z, cmapGL τ.symm (u⁻¹ * z) = u⁻¹ * cmapGL τ.symm z := by
    intro z
    rw [map_mul, hu, ← map_inv, cmapGL_embGL τ.symm hτE]
  have hconj : ∀ w z, coefLin (lamV D i) (x' w) z = τ (coefLin (lamV D i) (x w) (cmapGL τ.symm z)) := fun w z => by
    change coefFn (RingHom.id ℂ) (lamV D i) (x' w : Pol ℂ D.what₂.Tau (Vc D i).rank) z =
      τ (coefFn (RingHom.id ℂ) (lamV D i) (x w : Pol ℂ D.what₂.Tau (Vc D i).rank) _)
    rw [hxx w]
    exact coefFn_conj τ _ _ z
  set g := Bridge.ratF (Vc D i) γ * h * (k : Bridge.Gf (Vc D i)) with hg
  set lam : ℂ := ((B.levLam ψ ⟨k.1, mem_levJ_of B hcc.1 k.2⟩ : ℂˣ) : ℂ) with hlam
  have hL : Φ (x g) = lam • B.act γ (Φ (x h)) := hlaw γ h ⟨k.1, mem_levJ_of B hcc.1 k.2⟩
  have E1 : ∀ z, coefLin (lamV D i) (x g) z = lam * coefLin (lamV D i) (x h) (u⁻¹ * z) := by
    intro z
    have e1 : harmFn (Wc D i).rank B.w B.F.BS (Φ (x g)) z =
        lam * harmFn (Wc D i).rank B.w B.F.BS (B.act γ (Φ (x h))) z := by
      rw [hL, map_smul]
      rfl
    rw [hact, hfn, hfn] at e1
    apply mul_left_cancel₀ hκ0
    rw [e1]
    ring
  have hl' : ((B.levLam ψ' k : ℂˣ) : ℂ) = τ lam := levLam_conj hB hψ hψ' hcc hf k
  show Φ ((τ κ / κ) • x' g) = ((B.levLam ψ' k : ℂˣ) : ℂ) • B.act γ (Φ ((τ κ / κ) • x' h))
  rw [hl']
  refine sub_eq_zero.1 (_root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ B.w B.F.BS hB.wt (GlobalTheory.CoefLatConj.pq_le hB) _
    (sub_mem (hval _) (Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (hval _)))) ?_)
  funext z
  have e2 : ∀ (P Q : PolF D (Wc D i).rank (Vc D i).rank) (a : ℂ), harmFn (Wc D i).rank B.w B.F.BS (P - a • Q) z =
      harmFn (Wc D i).rank B.w B.F.BS P z - a * harmFn (Wc D i).rank B.w B.F.BS Q z := fun P Q a => by
    rw [map_sub, map_smul]
    rfl
  rw [e2, hact, hfn, hfn, map_smul, map_smul]
  change κ * ((τ κ / κ) * coefLin (lamV D i) (x' g) z) - τ lam * (κ * ((τ κ / κ) * coefLin (lamV D i) (x' h) (u⁻¹ * z))) = 0
  rw [hconj, hconj, hfix, E1, map_mul]
  ring

theorem mtLat_conj : ∀ (D : D7) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → B.w.lam = lamV D i → ∀ (Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (κ : ℂ), κ ≠ 0 → (∀ x, Φ x ∈ B.valSpace) → (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (Φ x) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) → ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ), IsCoefRing σ emb O → ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → ∀ (ψ ψ' : Twist D Circle), ψ.Good → ψ'.Good → ConjChar τ ψ ψ' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = Φ x ∧ f' h = Φ ((τ κ / κ) • x')) → f ∈ B.mtLat σ emb O ψ → f' ∈ B.mtLat σ emb (O.map (τ : ℂ →+* ℂ)) ψ' := by
  intro D i B hB hlam Φ κ hκ0 hval hκ K _ _ σ emb O hc τ hτ ψ ψ' hψ hψ' hcc hf f f' hff hfm
  choose x x' hxx hfx hfx' using hff
  have hτE : ∀ (t : D.what₂.Tau) (e : D.host.E), τ.symm (tauE D t e) = tauE D t e := fun t e => by
    rw [← hc.emb t, RingHom.comp_apply, τ.symm_apply_eq, hτ]
  obtain ⟨hform, hlat⟩ := (Base.mem_mtLat B σ emb O).1 hfm
  have hlaw : B.HasLaw ψ (fun h => Φ (x h)) := by
    have e : f = fun h => Φ (x h) := funext hfx
    rw [← e]
    exact ((Base.mem_formsC B).1 hform).2
  have e' : f' = fun h => Φ ((τ κ / κ) • x' h) := funext hfx'
  refine (Base.mem_mtLat B σ emb (O.map (τ : ℂ →+* ℂ))).2 ⟨(Base.mem_formsC B).2 ⟨fun h => (hfx' h).symm ▸ hval _, ?_⟩, fun h => ?_⟩
  · rw [e']
    exact hasLaw_conj hB hκ0 hval hκ hτE hψ hψ' hcc hf hxx hlaw
  · rw [hfx' h]
    exact (GlobalTheory.CoefLatConj.conj_mem_iff Φ hlam hκ0 hval hκ σ emb O τ hτ h (hxx h)).1 (hfx h ▸ hlat h)

end GlobalTheory.MtLatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSetupOverExtendedDataIntegralFormsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move.TieUp

variable {D : D7} (r : Rest D)

theorem placeModel_up {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel D mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel (overD D r) mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeModel_dn {mm nn : ℕ} {ψ B hs e Λ c f₀ T} (h : @IsPlaceModel (overD D r) mm nn ψ B hs e Λ c f₀ T) :
    @IsPlaceModel D mm nn ((ψ)) ((B)) ((hs)) ((e)) ((Λ)) c ((f₀)) ((T)) :=
  @IsPlaceModel.mk (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (_) (trans := (by with_unfolding_all exact (h.trans :))) (modul := (by with_unfolding_all exact (h.modul :)))
    (vac := (by with_unfolding_all exact (h.vac :)))

theorem placeMap_up {S T : HSp D} (B : Base S T) (a : AE D) :
    (baseUp r B).F.placeMap ((a)) = (B.F.placeMap a) := by
  have hP : (fun L : (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) →ₗ[ℂ] (WO (D := overD D r) ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))) → ℂ) =>
      IsPlaceModel (baseUp r B).F.ψ (symplO ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :))))
        (heisO (baseUp r B).F.ψ ((by with_unfolding_all exact (S :))) ((by with_unfolding_all exact (T :)))) ((by with_unfolding_all exact (a :))) (baseUp r B).F.lat 1 (baseUp r B).F.f₀ L) =
      (by with_unfolding_all exact ((fun L : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) =>
        IsPlaceModel B.F.ψ (symplO S T) (heisO B.F.ψ S T) a B.F.lat 1 B.F.f₀ L) :)) :=
    funext fun L => propext ⟨fun h => (by with_unfolding_all exact ((placeModel_dn r h) :)), fun h => (by with_unfolding_all exact ((placeModel_up r h) :))⟩
  unfold Frame.placeMap
  exact (by with_unfolding_all exact ((congrArg Classical.epsilon hP) :))

theorem vec_up {S T : HSp D} (B : Base S T) (Q ω) :
    (baseUp r B).F.vec (baseUp r B).G (by with_unfolding_all exact (Q :))
      (by with_unfolding_all exact (ω :)) = (by with_unfolding_all exact (B.F.vec B.G Q ω :)) := by
  have e := placeMap_up r B (halfIdem B.G.Pg Q)
  show (baseUp r B).F.placeMap (by with_unfolding_all exact (halfIdem B.G.Pg Q :))
    (by with_unfolding_all exact (B.F.datumFn B.G Q ω :)) = _
  rw [e]
  with_unfolding_all exact rfl


open Classical in
theorem vecAt_up {S T : HSp D} (B : Base S T) (Q φ) :
    (baseUp r B).vecAt (by with_unfolding_all exact (Q :))
      (by with_unfolding_all exact (φ :)) = (by with_unfolding_all exact (B.vecAt Q φ :)) := by
  show (baseUp r B).F.vec (baseUp r B).G (by with_unfolding_all exact (B.de.Q ∪ Q :))
    (by with_unfolding_all exact (B.locFn Q φ :)) = _
  exact vec_up r B _ _

theorem series_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (Q φ h) :
    series (baseUp r B).F (by with_unfolding_all exact (ω :))
      ((baseUp r B).vecAt (by with_unfolding_all exact (Q :)) (by with_unfolding_all exact (φ :)))
      (by with_unfolding_all exact (h :)) = (by with_unfolding_all exact (series B.F ω (B.vecAt Q φ) h :)) := by
  rw [vecAt_up r B]
  with_unfolding_all exact rfl

theorem theta_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (h : GA D S) :
    (baseUp r B).theta ((ω)) ((h)) = (B.theta ω h) :=
  series_up r B ω ∅ (fun _ _ => 1) h

theorem vecFlat_up {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) :
    (baseUp r B).vecFlat (twistUp r ψ) = (B.vecFlat ψ) :=
  vecAt_up r B ψ.Q _

theorem gen_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) :
    (baseUp r B).gen ((ω)) (twistUp r ψ) = (B.gen ω ψ) := by
  unfold Base.gen
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem genSet_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) (h P) :
    (baseUp r B).genSet (by with_unfolding_all exact (ω :)) (twistUp r ψ)
      (by with_unfolding_all exact (h :)) (by with_unfolding_all exact (P :)) =
        (by with_unfolding_all exact (B.genSet ω ψ h P :)) := by
  unfold Base.genSet
  rw [gen_up]
  with_unfolding_all exact rfl

def univUp {C : Type} [AddCommGroup C] (u : UnivTwist D C) : UnivTwist (overD D r) C := ⟨(by with_unfolding_all exact (u.del :)), (by with_unfolding_all exact (u.kap :))⟩

theorem vecFam_up {S T : HSp D} (B : Base S T) {C : Type} (Q : Finset (Pl D.host.E))
    (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) :
    (baseUp r B).vecFam (C := C) ((by with_unfolding_all exact (Q :))) ((by with_unfolding_all exact (Φ :))) = (by with_unfolding_all exact ((B.vecFam (C := C) Q Φ) :)) :=
  funext fun a => vecAt_up r B Q _

theorem xiCoef_up {S T : HSp D} (B : Base S T) {C : Type} [AddCommGroup C] [Fintype C] (ω : PairRep S T) (u : UnivTwist D C)
    (Q : Finset (Pl D.host.E)) (Φ : ∀ PP : Pl D.host.E, C → Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℚ) (h : GA D S)
    (P : PolF D T.rank S.rank) :
    (baseUp r B).xiCoef ((ω)) (univUp r u) ((Q)) ((Φ)) ((h)) ((P)) = (B.xiCoef ω u Q Φ h P) := by
  unfold Base.xiCoef Base.xi
  rw [vecFam_up]
  exact (by with_unfolding_all exact (rfl :))

theorem classSum_up {S T : HSp D} (B : Base S T) (ω : PairRep S T) (ψ : Twist D Circle) {I : Type} [Fintype I] (h : I → GA D S) :
    (baseUp r B).classSum (I := I) ((by with_unfolding_all exact (ω :))) (twistUp r ψ) ((by with_unfolding_all exact (h :))) = (by with_unfolding_all exact ((B.classSum ω ψ h) :)) := by
  unfold Base.classSum
  rw [vecFlat_up]
  exact (by with_unfolding_all exact (rfl :))

theorem coefLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) : B.coefLat σ emb O = B.coefLat (embLL0 D) (labLL0 D) O := by
  obtain rfl : (embLL0 D).comp e.toRingHom = σ := RingHom.ext hσ
  have h : (fun τ => e.toRingHom.comp (emb τ)) = labLL0 D := funext fun τ => RingHom.ext fun x => (embLL0 D).injective
    ((DFunLike.congr_fun (hemb τ) x).trans (DFunLike.congr_fun (embLL0_labLL0 τ) x).symm)
  funext x
  rw [Base.coefLat, Base.coefLat, harmLat, harmLat, GlobalTheory.CoefLatIso.coefLatFn_ringEquiv, h]

theorem mtLat_of_equiv {S T : HSp D} (B : Base S T) {K : Type} [Field K] [NumberField K] (e : K ≃+* ↥D.LL0) (σ : K →+* ℂ)
    (emb : D.what₂.Tau → (D.host.E →+* K)) (hσ : ∀ x, embLL0 D (e x) = σ x) (hemb : ∀ τ, σ.comp (emb τ) = tauE D τ)
    (O : Subring ℂ) (t : Twist D Circle) : B.mtLat σ emb O t = B.mtLat (embLL0 D) (labLL0 D) O t := by
  rw [Base.mtLat, Base.mtLat, coefLat_of_equiv B e σ emb hσ hemb]

section Setup

variable (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)

theorem liftSetupOverExtendedData_theta_eq : (setupUp r ρ).theta ((i)) ((j)) b = (ρ.theta i j b) :=
  (by with_unfolding_all exact ((funext fun h => congrArg DFunLike.coe (theta_up r (ρ.B i j b) (ρ.om i j b 1) h)) :))

theorem liftSetupOverExtendedData_gens_eq : (setupUp r ρ).gens ((i)) ((j)) b = (ρ.gens i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ => funext fun h => funext fun P =>
    genSet_up r (ρ.B i j b) (ρ.om i j b 1) (ρ.tw i b k Q ψ) h P) :))

theorem liftSetupOverExtendedData_classSum_eq : (setupUp r ρ).sum ((i)) ((j)) b = (ρ.sum i j b) :=
  (by with_unfolding_all exact ((funext fun k => funext fun Q => funext fun ψ =>
    classSum_up r (ρ.B i j b) (ρ.om i j b (ρ.tw i b k Q ψ).chi) (ρ.tw i b k Q ψ) (ρ.rep i j b (ρ.tw i b k Q ψ))) :))

theorem liftSetupOverExtendedData_xi_eq : (setupUp r ρ).xi ((i)) ((j)) b (overD D r).nexp = (ρ.xi i j b D.nexp) :=
  (by with_unfolding_all exact ((funext fun Q => funext fun M => funext fun h => funext fun P =>
    xiCoef_up r (ρ.B i j b) (ρ.om i j b 1) (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc)
      (half (ρ.ch i) (admissibleConjugatePairPlaces D.ntw i Q M)) (Base.univFam (univOf D.nexp i (admissibleConjugatePairPlaces D.ntw i Q M) M ρ.rc) (ρ.β j)) h P) :))

variable {r} {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
include hc

theorem liftSetupOverExtendedData_lat_eq : (setupUp r ρ).lat ((i)) ((j)) b = (ρ.lat i j b) := by
  funext O x
  have := coefLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :))) O
  exact (by with_unfolding_all exact ((congrFun this (finPt _ x)) :))

theorem liftSetupOverExtendedData_integralForms_eq : (setupUp r ρ).mt ((i)) ((j)) b = (ρ.mt i j b) := by
  have H := mtLat_of_equiv (ρ.B i j b) e (embLL0 (overD D r)) ((by with_unfolding_all exact ((labLL0 (overD D r)) :))) hc.embLL0_eq
    ((by with_unfolding_all exact ((embLL0_labLL0 (D := overD D r)) :)))
  have H' := fun (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) =>
    H (ρ.eOk i b k).range (ρ.tw i b k Q ψ)
  funext k Q ψ
  exact (by with_unfolding_all exact ((H' k ((Q)) ((ψ))) : _))

theorem liftSetupOverExtendedData_isDatum_eq : (setupUp r ρ).IsDatum ((i)) ((j)) b = (ρ.IsDatum i j b) := by
  funext s x P
  have hl := liftSetupOverExtendedData_lat_eq ρ i j b hc
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · have m := d.mem
    rw [hl] at m
    exact (⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (m :))⟩ : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))))
  · have d' : ρ.IsDatum i j b ((by with_unfolding_all exact (s :))) ((by with_unfolding_all exact (x :))) ((by with_unfolding_all exact (P :))) := d
    refine ⟨(by with_unfolding_all exact (d'.split :)), (by with_unfolding_all exact (d'.off :)), (by with_unfolding_all exact (d'.fin :)), (by with_unfolding_all exact (d'.supp :)), ?_⟩
    rewrite [hl]
    exact (by with_unfolding_all exact (d'.mem :))

end Setup

section Cell

variable {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0} (hc : CopyTw D (overD D r) ι e)
  {ρ : Setup D.ntw} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}

def cellUp {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    CellTie hρ' (overD D r).nexp (i := (by with_unfolding_all exact (i :))) (j := (by with_unfolding_all exact (j :))) (b := b) ((by with_unfolding_all exact (rd :))) where
  supp := (by with_unfolding_all exact (t.supp :))
  cls := (by with_unfolding_all exact (t.cls :))
  coef := (by with_unfolding_all exact (t.coef :))
  rdV := (by with_unfolding_all exact (t.rdV :))
  U_eq := (by with_unfolding_all exact (t.U_eq :))
  psiU_eq := (by with_unfolding_all exact (t.psiU_eq :))
  dat := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.dat :))
  dat_onto := by rewrite [liftSetupOverExtendedData_isDatum_eq ρ i j b hc, liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.dat_onto :))
  lev_iff := (by with_unfolding_all exact (t.lev_iff :))
  th_eq := by rewrite [liftSetupOverExtendedData_theta_eq r ρ i j b]; exact (by with_unfolding_all exact (t.th_eq :))
  thPsi_iff := by rewrite [liftSetupOverExtendedData_gens_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thPsi_iff :))
  thU_eq := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_eq :))
  thU_off := by rewrite [liftSetupOverExtendedData_xi_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thU_off :))
  rdV_inj := (by with_unfolding_all exact (t.rdV_inj :))
  mtLat_iff := by rewrite [liftSetupOverExtendedData_integralForms_eq ρ i j b hc]; exact (by with_unfolding_all exact (t.mtLat_iff :))
  thP_eq := by rewrite [liftSetupOverExtendedData_classSum_eq r ρ i j b]; exact (by with_unfolding_all exact (t.thP_eq :))

theorem cellUp_rdV {hρ : ρ.Good} (hρ' : (setupUp r ρ).Good) {rd : Rd ρ D.nexp i j b} (t : CellTie hρ D.nexp rd) :
    HEq t.rdV (cellUp r hc hρ' t).rdV := HEq.rfl


end Cell

end GlobalTheory.TwInputs.Move.TieUp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MovedVacuumTranslateSumFlipScalar
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScal

open MeasureTheory

theorem nrm2_const_smul {D : D7} {m n : ℕ} (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (c : ℂ) (f : Mx D m n → ℂ) :
    nrm2 μ 𝓕 (c • f) = ‖c‖ ^ 2 * nrm2 μ 𝓕 f := by
  unfold nrm2
  rw [← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, norm_smul, mul_pow]

theorem moved_vacuum_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V) (x : (AE D)ˣ) (lam : ℂ) (Y : Finset (WO V W)), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → Y.card = flipIdx V W T m → om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ → lam = flipScal χW V W T m x := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z x lam Y hT hm hcop hTm hz hmt hx hY hYu hcard hom
  have hm0 : m ≠ 0 := by rintro rfl; exact Nat.not_odd_zero hm
  have hW := hP.1.weil
  have hf := hP.2.2.2.2.2.2.2.2
  obtain ⟨ℓ, hℓ0, hℓ⟩ := _root_.GlobalTheory.LevelSeries.exists_invariant_form_idemSum D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨r, hr, hrℓ⟩ := GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase D ψ V W χV χW om hW T eT m z x ℓ hT hm0 hmt hx hℓ
  have hth := hf.2.theta
  have h1 := hrℓ f₀ hth
  have hsum : ℓ (∑ y ∈ Y, heisO ψ V W y f₀) = (Y.card : ℂ) * ℓ f₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl fun y hy => hℓ y (hY y hy).1 f₀ hth, Finset.sum_const, nsmul_eq_mul]
  rw [hom, map_smul, hsum, smul_eq_mul] at h1
  have h2 : lam * Y.card = r * ((χW x : Circle) : ℂ)⁻¹ := mul_right_cancel₀ hℓ0 (by rw [← h1]; ring)
  obtain ⟨p, hp⟩ := hf.2.norm.1
  have hn := _root_.GlobalTheory.WeilUnitNorm.weil_norm_one_of_unit_norm D ψ V W χV χW om hW p.1 p.2 hp (z⁻¹, 1) f₀ hth (hf.2.norm.2 p hp)
  rw [hom, nrm2_const_smul, _root_.GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y (fun y hy => (hY y hy).1) hYu p.1 p.2
    hp] at hn
  have hχ : ‖((χW x : Circle) : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
  have h3 : ‖lam‖ * Y.card = r := by
    have := congrArg norm h2
    rwa [norm_mul, norm_mul, hχ, mul_one, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hr.le] at this
  have hN : (0 : ℝ) < Y.card := by
    rcases (Nat.eq_zero_or_pos Y.card) with h | h
    · rw [h, Nat.cast_zero, mul_zero] at h3; exact absurd h3 hr.ne
    · exact_mod_cast h
  have h4 : r = Real.sqrt (Y.card : ℝ) := by
    rw [← h3]
    have : ‖lam‖ ^ 2 = (Y.card : ℝ)⁻¹ := eq_inv_of_mul_eq_one_left hn
    rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hN.le (by positivity),
      show ‖lam‖ * (Y.card : ℝ) * (‖lam‖ * Y.card) = ‖lam‖ ^ 2 * Y.card * Y.card by ring, this,
      inv_mul_cancel₀ hN.ne', one_mul]
  have hNc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold flipScal
  rw [← hcard]
  have hs : Real.sqrt (Y.card : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN).ne'
  have h5 : lam = r * ((χW x : Circle) : ℂ)⁻¹ / Y.card := by rw [← h2]; field_simp
  rw [h5, h4]
  have hsq : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) * ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) = Y.card := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hN.le]; push_cast; rfl
  have hsc : ((Real.sqrt (Y.card : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp
  rw [← hsq]
  ring

end GlobalTheory.FlipScal

end
end

