module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMLevJ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.LevJRed

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {gp : Fin 2 → ℕ}

theorem mat_one (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) : G.mat j v h fr 1 = 1 := by
  unfold GLoc.mat
  rw [map_one, mul_one, inv_mul_cancel, Units.val_one]

theorem mat_mul (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    (fr : GL (Fin n) (v.adicCompletion F)) (x y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    G.mat j v h fr (x * y) = G.mat j v h fr x * G.mat j v h fr y := by
  unfold GLoc.mat
  rw [map_mul, ← Units.val_mul]
  congr 1
  group

theorem mat_int (G : GLoc F E σ gp) (j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp j : 𝓞 F) ∈ v.asIdeal)
    {J : Matrix (Fin n) (Fin n) E} {Lb : Submodule (𝓞 E) (Fin n → E)} (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : ∀ x : Fin n → v.adicCompletion F,
      (∃ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb, ∀ b, G.phi j v h (y b) = x b) ↔
        ∀ b, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x b ∈
          v.adicCompletionIntegers F)
    {x : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hx : x ∈ levelVL σ J v Lb) (a b : Fin n) :
    G.mat j v h fr x a b ∈ v.adicCompletionIntegers F := by
  classical
  set w : Fin n → v.adicCompletion F := (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single b 1 with hw
  have hinv : ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w = Pi.single b 1 := by
    rw [hw, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (hfr w).2 fun c => by
    rw [hinv]
    by_cases e : c = b
    · subst e
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne e]
      exact zero_mem _
  have hst : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) Lb) := hx.2
  have hxy : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
      latS (F := F) (v.adicCompletion F) (intV E v) Lb := (hst y).1 hy
  have hphi : ∀ c, G.phi j v h (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) c) =
      (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)).map (G.phi j v h)) *ᵥ w) c := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hyw]
  have key := (hfr _).1 ⟨_, hxy, hphi⟩ a
  convert key using 1
  unfold GLoc.mat
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul, Matrix.mulVec_single_one]
  rfl

end Gen

theorem redM_levJ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) 1) = 1 ∧ ∀ x ∈ F.levJ.Uloc v, ∀ y ∈ F.levJ.Uloc v, redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) (x * y)) = redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) * redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) y) := by
  intro B X I _ _ l Z u Ch0 chOf0 F _ j v hv
  have hint : ∀ x ∈ F.levJ.Uloc v, ∀ a b, F.gl.mat j v hv (F.glevJ.fr j v hv) x a b ∈
      v.adicCompletionIntegers (I.rec7 l Z).host.F := fun x hx =>
    mat_int F.gl j v hv (F.glevJ.fr j v hv) (F.glevJ.fr_lat j v hv) (F.levJ.Uloc_lev v hx)
  refine ⟨?_, fun x hx y hy => ?_⟩
  · rw [mat_one]
    exact ChartLevel.redM_one v
  · rw [mat_mul]
    exact ChartLevel.redM_mul v (hint x hx) (hint y hy)

end GlobalTheory.Mem.Col2.TC.LevJRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularOfValuationBoundedAtPoints
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.RegCrit

theorem isUnit_of_one_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (c : e.O)
    (hc : 1 ≤ e.w c) : IsUnit c := by
  have h0 : (c : AlgebraicClosure F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact absurd hc (by norm_num)
  have h1 : (c : AlgebraicClosure F)⁻¹ ∈ e.O := by
    rw [e.mem_O, map_inv₀]
    exact inv_le_one_of_one_le₀ hc
  exact IsUnit.of_mul_eq_one ⟨_, h1⟩ (Subtype.ext (mul_inv_cancel₀ h0))

end GlobalTheory.TrueGeo.RegCrit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SIsoReD
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.IsoRe

variable {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (h' : FinX (reY Z Y))

def eP (u u' : D.what₂.Word) : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') :=
  (rp_iso_pair D Z X Y h h' u u').choose


set_option maxHeartbeats 4000000 in
def sIsoRe : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')) where
  cd := (by with_unfolding_all exact ((Eq.refl (Formalism.L2.SG.PairVal.cdScaleOf D)) :))
  del := (by with_unfolding_all exact ((Eq.refl D.s.Del) :))
  letter := (by with_unfolding_all exact ((Eq.refl D.s.letter) :))
  eHH := (by with_unfolding_all exact ((eHHre Z X) :))
  eCu := (by with_unfolding_all exact ((eCure Z h h') :))
  Pu_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').1 :))
  volN := (by with_unfolding_all exact ((Eq.refl Y.volN) :))
  volH := (by with_unfolding_all exact ((Eq.refl Y.volH) :))
  eT := (by with_unfolding_all exact ((eRT Z Y) :))
  aTerm_eq := (by with_unfolding_all exact ((keep_pu_vol_aR D Z X Y h h').2.2 :))
  isId := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).1 :))
  inS := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.1 :))
  relevant := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.1 :))
  FeqF := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.1 :))
  Gterm := fun {u u'} t => Subtype.ext (a1 := (sOf h).Gterm t) (a2 := (by with_unfolding_all exact (((sOf h').Gterm (eRT Z Y u u' t)) :))) ((by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.1 :)))
  atP := fun p => (by with_unfolding_all exact ((Formalism.L2.S.LocIso.refl (Formalism.L2.S.locC D p)) :))
  ePl := (by with_unfolding_all exact ((Equiv.refl (Formalism.MainNotions.S.LocalSplitGroups.PlF D)) :))
  BBne := fun {u u'} t q => (by with_unfolding_all exact ((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.1 q) :))
  generic := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.1 :))
  eP := (by with_unfolding_all exact ((eP Z h h') :))
  pfst := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).1) :))
  psnd := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.1) :))
  s0 := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.1) :))
  scalarPair := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.1) :))
  pval := fun {u u'} p => (by with_unfolding_all exact ((((rp_iso_pair D Z X Y h h' u u').choose_spec p).2.2.2.2) :))
  ptOf := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.1 :))
  cTerm := fun {u u'} t => (by with_unfolding_all exact (((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 t).2.2.2.2.2.2.2.2.2 :))
  massPair := fun {u u'} p => (by with_unfolding_all exact (((((GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').1 ((p.1.1) : RT Y u u')).2.2.2.2.2.2.2.2.1).trans
      (congrArg Formalism.L2.SG.PairVal.massTerm ((rp_iso_pair D Z X Y h h' u u').choose_spec ((p) : RP Y u u')).1)) : _))
  meanCount := (by with_unfolding_all exact ((funext fun u => funext fun u' => funext fun w => (GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data D Z X Y u u').2 w :
      (fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) =
        fun (u u' : D.what₂.Word) w => Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w) :))

end GlobalTheory.Mem.SRe.IsoRe

namespace GlobalTheory.Mem.SRe


set_option maxHeartbeats 4000000 in
theorem sIso_reD : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)),
    ∃ e : SIso (sOf h) ((@sOf (reD D Z) (@reX D Z X) (@reY D Z X Y) h')), HEq e.eHH (eHHre Z X) ∧ ∀ u, HEq (e.eCu u) (eCure Z h h' u) :=
  fun _ Z X _ h h' => ⟨IsoRe.sIsoRe Z h h', (by with_unfolding_all exact ((HEq.refl (eHHre Z X)) :)),
    fun u => (by with_unfolding_all exact ((HEq.refl (eCure Z h h' u)) :))⟩

end GlobalTheory.Mem.SRe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabiliserMapHyperplaneEqConjClassMap
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.HAt.Stab

theorem co_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (g : S.V ≃ₗ[E] S.V) (x : S.V) :
    co S h (g x) = (reGL h E (Formalism.L2.Herm.toGLb S.frame g)).1 *ᵥ co S h x := by
  have e : lin S h (reGL h E (Formalism.L2.Herm.toGLb S.frame g)) = g := by
    subst h
    have e0 : ∀ k : GL (Fin S.rank) E, reGL rfl E k = k := fun k => by
      ext a b
      simp [reGL]
    show (Formalism.L2.Herm.toGLb S.frame).symm (reGL rfl E (reGL rfl E (Formalism.L2.Herm.toGLb S.frame g))) = g
    rw [e0, e0, MulEquiv.symm_apply_apply]
  rw [← co_lin, e]

theorem co_symm_apply {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {n : ℕ} (h : S.rank = n)
    (k : GL (Fin S.rank) E) (x : S.V) :
    co S h ((Formalism.L2.Herm.toGLb S.frame).symm k x) = (reGL h E k).1 *ᵥ co S h x := by
  rw [co_apply, MulEquiv.apply_symm_apply]

theorem eq_of_frMul {E K ι : Type} [Field E] [Field K] [Fintype ι] (τ : ι) (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ}
    (g M : GL (Fin n) E) (y : Col2.Fr emb σ n) (h : frMul emb σ M⁻¹ (frMul emb σ g y) = y) : g = M := by
  have h1 : (M⁻¹ : GL (Fin n) E).1.map (embAt σ emb τ) * (g.1.map (embAt σ emb τ) * y.1 τ) = y.1 τ :=
    congrFun (congrArg Subtype.val h) τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, ← Units.val_mul] at h1
  have hy : IsUnit (y.1 τ) := (Matrix.isUnit_iff_isUnit_det _).2 (y.2 τ)
  have h2 : (M⁻¹ * g : GL (Fin n) E).1.map (embAt σ emb τ) = 1 := hy.mul_right_cancel (by rw [h1, Matrix.one_mul])
  have h3 : (M⁻¹ * g : GL (Fin n) E).1 = 1 := by
    apply Matrix.map_injective (embAt σ emb τ).injective
    show _ = (1 : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h2
  have h4 : M⁻¹ * g = 1 := Units.ext h3
  exact (inv_mul_eq_one.1 h4).symm

theorem ext_vec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {x y : Fin N → E} (h1 : iniH hN x = iniH hN y)
    (h2 : x (Br.iL hN) = y (Br.iL hN)) : x = y := by
  funext j
  by_cases hj : j.1 < n
  · exact congrFun h1 ⟨j.1, hj⟩
  · have : j = Br.iL hN := Fin.ext (by have := j.2; show j.1 = n; omega)
    rw [this, h2]

theorem ga_eq_gam_mv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP), ((F u).til.ga c).1.1 = ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 := by
  intro B X I l Z H F hF u c
  classical
  have hemb : Formalism.L2.Forms.embT (I.rec7 l Z) = embAt B.embLL B.fields.emb := by
    funext τ
    ext y
    show B.host.φ₀ _ = _
    rw [← B.embE_φ₀]
    rfl
  let y : Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) := ⟨fun _ => 1, fun _ => by simp⟩
  let g : GL (Fin (B.R.N B.R.m)) B.fields.E := ((F u).til.ga c).1
  let φ : (I.stp u I.mu0 B.R.m).Cl → Col2.Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ := fun _ z => if z = y then 1 else 0
  have hY := (hF u).eY B.R.m le_rfl (Or.inr rfl)
  have h := (F u).evz φ c (frMul B.fields.emb B.embLL g y) y (by
    intro τ
    rw [hemb]
    exact (congrFun (hY _) τ).trans (congrArg (fun k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ => (g.1.map (embAt B.embLL B.fields.emb τ) * k : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) ℂ)) (congrFun (hY y) τ)).symm)
  rw [(hF u).eWz] at h
  have h' : B.embLL _ * φ ((I.perIn u I.mu0).tilC c) (frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y)) = _ * φ ((I.perIn u I.mu0).tilC c) y := h
  have hy : frMul B.fields.emb B.embLL ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c)))⁻¹ (frMul B.fields.emb B.embLL g y) = y := by
    by_contra hne
    simp only [φ, if_neg hne, if_pos, mul_zero, mul_one] at h'
    exact Units.ne_zero _ h'.symm
  exact congrArg Units.val (eq_of_frMul (show B.fields.Tau from (I.rec7 l Z).eTau.symm 1) _ _ _ _ _ hy)

theorem crdN_stabM : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u)) → CarH H F → ∀ (u : B.Word) (h1 : 1 ≤ (I.rec7 l Z).R.m) (c : ((I.rec7 l Z).mem u).C.cls (I.rec7 l Z).R.m) (s : ((I.rec7 l Z).mem u).C.stab (I.rec7 l Z).R.m c) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 c s y) = ((I.stp u I.mu0 B.R.m).gam c.1 s.1).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F hF hC u h1 c s y
  obtain ⟨k, hk⟩ := (hF u).ends B.R.m le_rfl (Or.inr rfl)
  have e1 := hk.stab c s
  have e2 := (hC.carM u).st_eq c s
  have e3 : ∀ (β β' : H.Ch u (I.rec7 l Z).R.m) (h : H.chOf u (I.rec7 l Z).R.m c = β) (h' : H.chOf u (I.rec7 l Z).R.m c = β'),
      ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β).stabI ⟨c, h⟩ s).1 = ((H.cls u (I.rec7 l Z).R.m h1 le_rfl β').stabI ⟨c, h'⟩ s).1 := by
    intro β β' h h'
    subst h
    subst h'
    rfl
  refine (co_symm_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y).trans ?_
  refine congrArg (fun k : GL (Fin (B.R.N B.R.m)) B.fields.E => k.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y) ?_
  rw [← e1]
  exact (congrArg _ (e3 _ _ rfl (chOf_m H u c))).trans e2.symm

theorem crdP_stabP : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u)) → CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (s : ((I.rec7 l Z).fm u).stabilizer₂ c) (x : (I.rec7 l Z).sp.X'.V), crdP (I.rec7 l Z) (Formalism.L2.Herm.stabPLinS (I.rec7 l Z) H A u c s x) = ((I.perIn u I.mu0).S'.gam c.1 s.1).1 *ᵥ crdP (I.rec7 l Z) x := by
  intro B X I l Z H F A hF hC u c s x
  have e1 := (hF u).what₂.stab c s
  have e2 := (hC.carP u).st_eq c s
  refine (co_symm_apply (I.rec7 l Z).sp.X' (rankP (I.rec7 l Z)) _ x).trans ?_
  exact congrArg (fun k : GL (Fin (B.R.N B.R.m - 1)) B.fields.E => k.1 *ᵥ crdP (I.rec7 l Z) x) (e2.symm.trans e1)

theorem crdN_tilG : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → ∀ (u : B.Word) (c : ((I.rec7 l Z).fm u).clsP) (y : ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m).V), crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 y) = ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
  intro B X I l Z H F A hC u c y
  rw [hC.ga u c]
  exact co_apply ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl) _ y

theorem gam_ext : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (b : (I.perIn u I.mu0).S'.β) (g : (I.perIn u I.mu0).S'.G b), (∀ y, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ iXc (I.rec7 l Z) y = iXc (I.rec7 l Z) (((I.perIn u I.mu0).S'.gam b g).1 *ᵥ y)) ∧ ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext b g)).1 *ᵥ TC.z0 X u = TC.z0 X u := by
  intro B X I hOk hP l Z u b g
  have hi := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).2.2.1
  have ini : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iniH (N_m_succ B.R) (iXc (I.rec7 l Z) y) = y := fun y => by
    funext j
    exact (hi y _).trans (dif_pos j.2)
  have las : ∀ y : Fin (B.R.N B.R.m - 1) → B.fields.E, iXc (I.rec7 l Z) y (Br.iL (N_m_succ B.R)) = 0 := fun y =>
    (hi y _).trans (dif_neg (lt_irrefl _))
  refine ⟨fun y => ext_vec (N_m_succ B.R) ?_ ?_, ext_vec (N_m_succ B.R) ?_ ?_⟩
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    exact (congrArg _ (ini _)).trans (ini _).symm
  · exact ((l.per u I.mu0).gam_last b g _).trans ((las _).trans (las _).symm)
  · refine ((l.per u I.mu0).gam_ini b g _).trans ?_
    have z : iniH (E := B.fields.E) (N_m_succ B.R) (TC.z0 X u) = 0 := by
      funext j
      exact if_neg (by have := j.2; show ¬ (j.1 + 1 = _); omega)
    exact (congrArg _ z).trans ((Matrix.mulVec_zero _).trans z.symm)
  · exact (l.per u I.mu0).gam_last b g _

theorem stabMap_tied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), CarT H F A → Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  intro B X I hOk hPins l Z H F hStd hCarH A hCarT u h1 c s
  have hF : ∀ u, I.StdF l Z u (F u) := fun u => (hStd u).1
  have hga := ga_eq_gam_mv I l Z H F hF u c
  have conj : ∀ v, ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam _ (((I.rec7 l Z).fm u).stabMap c s).1).1 *ᵥ v) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ
      (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) := by
    intro v
    show _ *ᵥ (((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 (((I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))⁻¹ * (I.perIn u I.mu0).ext c.1 s.1 *
          (I.stp u I.mu0 B.R.m).mv (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).tilPt c))).1 *ᵥ v) = _
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have key : ∀ y, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1 (Formalism.L2.Herm.stabMLinS (I.rec7 l Z) H u h1 _
      (((I.rec7 l Z).fm u).stabMap c s) (((A u).tilG c).1.symm y))) =
      ((I.stp u I.mu0 B.R.m).gam (I.perIn u I.mu0).b0 ((I.perIn u I.mu0).ext c.1 s.1)).1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
    intro y
    have hw : ((F u).til.ga c).1.1 *ᵥ crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl (((A u).tilG c).1.symm y) =
        crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl y := by
      rw [← crdN_tilG I l Z H F A hCarT u c, LinearEquiv.apply_symm_apply]
    rw [crdN_tilG I l Z H F A hCarT u c, crdN_stabM I l Z H F hF hCarH u h1, ← hw, hga]
    exact conj _
  have hiX : ∀ x, crdN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl ((I.rec7 l Z).sp.iX' x) = iXc (I.rec7 l Z) (crdP (I.rec7 l Z) x) := by
    intro x
    simp [iXc, crdN, crdP]
  have hext := gam_ext I hOk hPins l Z u c.1 s.1
  refine ⟨fun x => ?_, ?_⟩
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, hiX, hiX, hext.1, crdP_stabP I l Z H F A hF hCarT u c s x]
    rfl
  · apply (crdN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m le_rfl).injective
    rw [key, ← hCarT.z0 u]
    have hz : (F u).til.z0 = TC.z0 X u := funext fun j => (hF u).z0 j
    rw [hz, hext.2]

end GlobalTheory.Mem.Col2.HAt.Stab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroFormsIdentificationReferenceTupleEqSelf
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC.MuZeroForms

theorem law0_choose_mu0_eq_self : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (u : B.Word) (x : ((I.fm l u I.mu0).lat 0).V),
    (l0 u I.mu0).choose x = x := by
  intro B X I h l Z l0 u x
  apply (I.fm l u I.mu0).emb_inj 0
  rw [(l0 u I.mu0).choose_spec.2 x]
  show LinearEquiv.funCongrLeft ℂ _ (I.eCls0 l u I.mu0).symm ((I.fm l u I.mu0).emb 0 x) = _
  funext c
  rw [LinearEquiv.funCongrLeft_apply]
  show (I.fm l u I.mu0).emb 0 x ((I.eCls0 l u I.mu0).symm c) = _
  have hc : (I.eCls0 l u I.mu0).symm c = c :=
    (I.eCls0 l u I.mu0).symm_apply_eq.2 (_root_.GlobalTheory.Mem.Col2.TC.MuZeroCls.stepZeroClassEquiv_referenceTuple_eq_self I h l u c).symm
  rw [hc]

end GlobalTheory.Mem.Col2.TC.MuZeroForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroHermitianLevelUniformiserKillsValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (L : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u)), SameCar (rank_eq_first_level (I.rec7 l Z).R) L.Lb (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Lb L.Uloc (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.Uloc L.U (F.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U (fun c => (L.y c).1) (fun c => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).y c).1) (fun c s => (L.stabI c s).1) (fun c s => ((F.cls 0 (Nat.zero_le _) (Or.inl rfl)).stabI c s).1) → ∃ L' : ColLevel (I.rec7 l Z).R (I.rec7 l Z).host.F (I.rec7 l Z).host.E (I.rec7 l Z).sp (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).C ((I.rec7 l Z).mem u).A ((I.rec7 l Z).clsLat u), L'.Lb = L.Lb ∧ L'.Uloc = L.Uloc ∧ L'.U = L.U ∧ L'.y = L.y ∧ L'.stabI = L.stabI ∧ L'.splitG = L.splitG ∧ L'.frG = L.frG ∧ ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (h : ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ w.asIdeal) (a : intV (I.rec7 l Z).host.E w), (a : TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (w.adicCompletion (I.rec7 l Z).host.F)) = inclE (F := (I.rec7 l Z).host.F) (w.adicCompletion (I.rec7 l Z).host.F) ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) → ∀ m : L'.fM w h, a • m = 0 := by
  first | exact @GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | exact GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values | (intros; apply GlobalTheory.Mem.Col2.LevTwist.stepZeroHermitianLevel_uniformiser_kills_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedHeckeCharIdeleValueUniformiser
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeUnifVal

open Formalism.L2.Host

theorem localIdele_eq_locM {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    Neutral.B1.localIdele E v x = Units.map (Formalism.L2.NC.locM v) x := by
  rfl

theorem at_val_and_unr_iff : ∀ {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Neutral.B1.Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  intro E _ _ χ h hχ v
  have hloc : ∀ x : (v.adicCompletion E)ˣ, χ.loc v x = h.χ (Units.map (Formalism.L2.NC.locM v) x) := by
    intro x
    rw [hχ, ← localIdele_eq_locM]
    rfl
  have hiff : χ.UnrAt v ↔ h.Unr v := by
    constructor
    · intro hu u hu1
      rw [← hloc]
      exact hu u hu1
    · intro hu u hu1
      rw [hloc]
      exact hu u hu1
  refine ⟨fun hu => ⟨hiff.1 hu, fun ϖ hϖ => ?_⟩, hiff⟩
  have hs := Formalism.L2.Host.unif_spec v
  unfold Formalism.L2.Host.IsUnifAt at hs
  have hq : Formalism.L2.Host.IsUnitAt v (ϖ * (Formalism.L2.Host.atFin v (Formalism.L2.Host.unif v))⁻¹) := by
    unfold Formalism.L2.Host.IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hs, hϖ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]
  have h1 := hu _ hq
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [← hloc, h1]
  rfl

end GlobalTheory.HeckeUnifVal
end

