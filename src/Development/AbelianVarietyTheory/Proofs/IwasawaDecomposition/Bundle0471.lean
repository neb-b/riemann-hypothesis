module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardFormComparisonSymmetricLevelMember
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousActP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfLine
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardColumnComparisonsTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC


set_option maxHeartbeats 4000000 in
theorem colsTiedSym_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∃ C : ColsTiedSym (I.rec7 l Z), I.StdC l Z C ∧ ∀ u, I.StdLvC l Z u (C.forms u) := by
  intro B X I hOk hP l Z
  obtain ⟨Ch, chOf, F, hF, hfin, hm, hgl, hchi⟩ := _root_.GlobalTheory.Mem.FormSym.formsTiedSym_std I hOk hP l Z
  obtain ⟨lev00, lev, cls, vT, Fv, hH0⟩ := GlobalTheory.T.hermitianColumnChoices_of_formsLevelsClasses I hOk hP l Z Ch chOf F hfin hm (fun u => (hF u).1)
  choose lev0 hLb hUl hU hy hst hsp hfrG hpi using fun u => GlobalTheory.T.stepZeroHermitianLevel_uniformiser_kills_values_alt I hOk hP l Z u (F u) (hF u).1 (lev00 u) (hH0.car0 u)
  let H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z) :=
    { lev0 := lev0, Ch := Ch, ChFin := hfin, Ch_m := hm, chOf := chOf, lev := lev, cls := cls, vT := vT, Fv := Fv }
  have hH : CarH H F :=
    { eV := hH0.eV, fv := hH0.fv
      car0 := fun u => by
        show SameCar _ (lev0 u).Lb _ (lev0 u).Uloc _ (lev0 u).U _ (fun c => ((lev0 u).y c).1) _ (fun c s => ((lev0 u).stabI c s).1) _
        rw [hLb u, hUl u, hU u, hy u, hst u]; exact hH0.car0 u
      carC := hH0.carC, carM := hH0.carM
      sp := fun u => by show _ = (lev0 u).splitG; rw [hsp u]; exact hH0.sp u
      fr0 := fun u => by show ∀ i v h, _ = reGL _ _ ((lev0 u).frG i v h); rw [hfrG u]; exact hH0.fr0 u }
  obtain ⟨A, hT, hAd, hSt⟩ := _root_.GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime I hOk hP l Z H F hF hH
  obtain ⟨hCof, hBase, ⟨hFv⟩, X0, hX0⟩ := GlobalTheory.T.hermitianColumns_generators_baseLattices_functionals I hOk hP l Z H F A hF hH hT
    (fun u w h a ha m => hpi u w h a (by rw [ha, hT.piU u]) m)
  have hStd := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hP l Z).1
  have hpiG : ∀ u u', (X0 u).piG = (X0 u').piG := fun u u' => by rw [hX0 u, hX0 u']
  have hpiG' : ∀ u, (F u).gl.piG = (X0 u).piG := fun u => by rw [hX0 u]; exact ((hF u).1.gl).piG
  have hfr0 : ∀ u u', (F u).glev0.fr = (F u').glev0.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.fr0, (hF u').1.fr0]
  have hfrP : ∀ u u', (F u).glevP.fr = (F u').glevP.fr := fun u u' => by
    funext j v h
    rw [(hF u).1.frP, (hF u').1.frP]
  refine ⟨
    { herm :=
        { base := H, atT := A, levelZeroCompatibility := X0, ad := hAd, cof := hCof, piG := hpiG,
          stabMap := hSt, fvI := hFv, std := hStd, baseL := hBase }
      forms := F
      eV := hH.eV
      piU := hT.piU
      res := hT.res
      car0 := hH.car0
      carC := hH.carC
      carM := hH.carM
      carP := hT.carP
      lattice₂ := hT.lattice₂
      pr := hT.pr
      prk := hT.prk
      prC := hT.prC
      z0 := hT.z0
      ga := hT.ga
      sp := hH.sp
      piG := hpiG'
      fr0 := hH.fr0
      gl_const := hgl
      chi := hchi
      frame_level_zero_const := hfr0
      frP_const := hfrP }, fun u => (hF u).1, fun u => (hF u).2⟩

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqOverSameChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl.RowWt

theorem fockDeg_cast (D : D7) (h : DV.KapDef D) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ D.R.m) :
    ((fockDeg D n : ℤ) : ℚ) = ∑ τ, (∑ a : Fin (D.R.sigW n).1, |DV.aPlusQ D n τ a| +
      ∑ c : Fin (D.R.sigW n).2, |DV.aMinusQ D n τ c|) := by
  unfold fockDeg
  push_cast
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [(h n h1 h2 τ).1 a]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [(h n h1 h2 τ).2 c, abs_neg]

theorem fockDeg_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z Z' : w.Lt)
    (h : DV.KapDef (w.D Z)) (h' : DV.KapDef (w.D Z')) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ (w.D Z).R.m) :
    fockDeg (w.D Z) n = fockDeg (w.D Z') n := by
  have e := fockDeg_cast (w.D Z) h n h1 h2
  have e' := fockDeg_cast (w.D Z') h' n h1 h2
  exact_mod_cast e.trans e'.symm

theorem forcedContent_eq_over_same_choices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z Z' : w.Lt), DV.KapDef (w.D Z) →
    DV.KapDef (w.D Z') → F0K K.s (w.D Z) = F0K K.s (w.D Z') := by
  intro K B f T w Z Z' h h'
  funext y j
  have hT : FTypeG (w.D Z) (j.1 + 1) = FTypeG (w.D Z') (j.1 + 1) := by
    unfold FTypeG
    rw [fockDeg_eq w Z Z' h h' (j.1 + 1) (Nat.succ_pos _) j.2]
  unfold F0K FK
  rw [hT]
  rfl

end GlobalTheory.Mem.Top.Bl.RowWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvTrUnitaryOne
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CoefIso

theorem bcVV_rhoVr {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
    (σ : K →+* ℂ) (emb : ι → E →+* K) (lam : ι → DomWeight n) (g : GL (Fin n) E) (v : VV K lam) :
    GlobalTheory.CoefSpace.bcVV σ lam (rhoVr emb lam g v) =
      rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (GlobalTheory.CoefSpace.bcVV σ lam v) := by
  apply Subtype.ext
  show MvPolynomial.map σ (actP lam (invTrK (embGL emb g)) v.1) =
    actP lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) (MvPolynomial.map σ v.1)
  rw [GlobalTheory.CoefSpace.map_actP]
  congr 2

theorem invTr_unitary_one {n : ℕ} (U : GL (Fin n) ℂ) (hU : (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U = 1) :
    ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * (1 : Matrix (Fin n) (Fin n) ℂ) *
      ((inside₂ ℂ n U : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have hi : ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    calc ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
        = ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * U) * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
          rw [hU, Matrix.one_mul]
      _ = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
          rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  show (((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)ᴴ * 1 * ((U⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = 1
  have e : (((U : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ)ᴴ = (U : Matrix (Fin n) (Fin n) ℂ)ᵀ := by
    ext i j
    simp
  rw [hi, Matrix.mul_one, e, ← Matrix.transpose_mul, hU, Matrix.transpose_one]

theorem ratMat_unitary {D : D7} (V : HSp D) (hg : V.gram = 1) (γ : GQ V) (γE : GL (Fin V.rank) D.host.E)
    (h : Bridge.IsRatMat V γ γE) (φ : D.host.E →+* ℂ) :
    ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ *
      ((Formalism.UG.bc φ γE : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) = 1 := by
  obtain ⟨γ, ⟨g, hgU, hgm⟩⟩ := γ
  have e1 : Formalism.UG.bc (incA D) g = Formalism.UG.bc (incA D) γE := hgm.trans h
  have e2 : g = γE := Units.ext (Matrix.ext fun i j =>
    (Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F))
      (congrArg (fun u => (Units.val u) i j) e1))
  subst e2
  have hu : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram := hgU
  rw [hg, Matrix.mul_one] at hu
  have hc : ((g : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map φ)ᴴ =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E)).map φ := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Formalism.UG.cT, Matrix.transpose_apply]
    exact (D.sp.cm.cmUnram.2.1 φ _).symm
  rw [bc_coe, hc, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero _) (map_one _)]


set_option maxHeartbeats 1000000 in
theorem coef_iso : ∀ (D : D7) (V : HSp D) (n : ℕ), V.rank = n → V.gram = 1 → ∀ (c : CoefA V), c.Is → ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (emb : ι → (D.host.E →+* K)) (lam : ι → DomWeight n) (c0 : VV K lam →ₛₗ[σ] c.W), Nonempty (VVIdx lam) →
  (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ v, c0 (rhoVr emb lam g v) = c.coef.ρ γ (c0 v)) →
  (LinearIndependent ℂ fun i => c0 (bVV K lam i)) →
  ∃ (e : VV ℂ lam ≃ₗ[ℂ] c.W) (s : ℝ), 0 < s ∧ (∀ v, c0 v = (s : ℂ) • e (GlobalTheory.CoefSpace.bcVV σ lam v)) ∧
    (∀ x y, inner ℂ (e x) (e y) = pairK lam (fun _ => 1) x y) ∧
    ∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E) (g : GL (Fin n) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g →
      ∀ x, e (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.coef.ρ γ (e x) := by
  intro D V n hn hg c hc K ι _ _ _ σ emb lam c0 hne hint hli
  subst hn
  classical
  have hMat : ∀ γ : GQ V, ∃ γE, Bridge.IsRatMat V γ γE ∧ MatEq γE γE := fun γ => by
    obtain ⟨γE, h⟩ := GlobalTheory.Mem.StdUnique.exists_ratMat γ
    exact ⟨γE, h, rfl, fun i j i' j' hi hj => by rw [Fin.ext hi, Fin.ext hj]⟩
  have hmem : ∀ v, c0 v ∈ Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
    intro v
    have hv : v ∈ Submodule.span K (Set.range (bVV K lam)) := by rw [(bVV K lam).span_eq]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  obtain ⟨i₀⟩ := hne
  have htop : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤ := by
    refine (GlobalTheory.Mem.StdUnique.bot_or_top c hc _ fun γ hγ w hw => ?_).resolve_left fun h0 => ?_
    · obtain ⟨γE, h1, h2⟩ := hMat ⟨γ, hγ⟩
      have hle : (Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i))).map (c.ρ γ) ≤
          Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨i, rfl⟩
        rw [show c.ρ γ (c0 (bVV K lam i)) = c.coef.ρ ⟨γ, hγ⟩ (c0 (bVV K lam i)) from rfl,
          ← hint ⟨γ, hγ⟩ γE γE h1 h2]
        exact hmem _
      exact hle ⟨w, hw, rfl⟩
    · have := hmem (bVV K lam i₀)
      rw [h0, Submodule.mem_bot] at this
      exact hli.ne_zero i₀ this
  let b1 : Module.Basis (VVIdx lam) ℂ (VV ℂ lam) :=
    Module.Basis.mk (GlobalTheory.CoefSpace.bcVV_indep σ lam) (GlobalTheory.CoefSpace.bcVV_span σ lam).ge
  let b2 : Module.Basis (VVIdx lam) ℂ c.W := Module.Basis.mk hli htop.ge
  have hb1 : ∀ i, b1 i = GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  have hb2 : ∀ i, b2 i = c0 (bVV K lam i) := fun i => Module.Basis.mk_apply _ _ i
  obtain ⟨e0, he0b⟩ : ∃ e0 : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ i, e0 (b1 i) = b2 i :=
    ⟨b1.equiv b2 (Equiv.refl _), fun i => by simp⟩
  have he0 : ∀ v, e0 (GlobalTheory.CoefSpace.bcVV σ lam v) = c0 v := by
    intro v
    have : (e0.toLinearMap.comp (GlobalTheory.CoefSpace.bcVV σ lam) : VV K lam →ₛₗ[σ] c.W) = c0 :=
      (bVV K lam).ext fun i => by
        rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hb1, he0b, hb2]
    exact LinearMap.congr_fun this v
  have hR : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x,
      e0 (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x) = c.ρ γ (e0 x) := by
    intro γ γE g h1 h2 x
    have : e0.toLinearMap.comp (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g)) =
        (c.ρ γ).comp e0.toLinearMap := b1.ext fun i => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hb1, ← bcVV_rhoVr, LinearEquiv.coe_coe, he0, he0,
        hint γ γE g h1 h2]
      rfl
    exact LinearMap.congr_fun this x
  have hP : ∀ (γ : GQ V) (γE g : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE → MatEq γE g → ∀ x y : VV ℂ lam,
      pairK lam (fun _ => 1) (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) x)
        (rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) g) y) = pairK lam (fun _ => 1) x y := by
    intro γ γE g h1 h2
    obtain rfl : γE = g := Units.ext (Matrix.ext fun i j => h2.2 i j i j rfl rfl)
    exact pairInv ℂ ι V.rank lam (fun _ => 1) _ fun τ =>
      invTr_unitary_one (Formalism.UG.bc (σ.comp (emb τ)) γE) (ratMat_unitary V hg γ γE h1 _)
  have hgr : GlobalTheory.CoefSpace.gramOf (fun _ : ι => (1 : GL (Fin V.rank) ℂ)) = fun _ => 1 := by
    funext τ
    simp [GlobalTheory.CoefSpace.gramOf]
  let S : c.W →ₗ[ℂ] GlobalTheory.CoefSpace.HV lam (fun _ => (1 : GL (Fin V.rank) ℂ)) := e0.symm.toLinearMap
  have hS : ∀ w, S w = e0.symm w := fun _ => rfl
  let T : Module.End ℂ c.W := (LinearMap.adjoint S).comp S
  have hT : ∀ w w', inner ℂ w (T w') = pairK lam (fun _ => 1) (e0.symm w) (e0.symm w') := by
    intro w w'
    show inner ℂ w (LinearMap.adjoint S (S w')) = _
    rw [LinearMap.adjoint_inner_right, GlobalTheory.CoefSpace.inner_HV, hgr]
    rfl
  have hBinv : ∀ (γ : GQ V) a b, pairK lam (fun _ => 1) (e0.symm (c.ρ γ a)) (e0.symm (c.ρ γ b)) =
      pairK lam (fun _ => 1) (e0.symm a) (e0.symm b) := by
    intro γ a b
    obtain ⟨γE, h1, h2⟩ := hMat γ
    have key : ∀ a, e0.symm (c.ρ γ a) = rhoK lam (invTrK fun τ => Formalism.UG.bc (σ.comp (emb τ)) γE) (e0.symm a) :=
      fun a => by rw [LinearEquiv.symm_apply_eq, hR γ γE γE h1 h2, LinearEquiv.apply_symm_apply]
    rw [key, key, hP γ γE γE h1 h2]
  have hcomm : ∀ (γ : GQ V) x, T (c.ρ γ x) = c.ρ γ (T x) := by
    intro γ x
    refine ext_inner_left ℂ fun w => ?_
    have hinv : c.ρ γ (c.ρ (γ⁻¹ : GQ V) w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, map_one,
        Module.End.one_apply]
    calc inner ℂ w (T (c.ρ γ x)) = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (T (c.ρ γ x)) := by rw [hinv]
      _ = pairK lam (fun _ => 1) (e0.symm (c.ρ (γ⁻¹ : GQ V) w)) (e0.symm x) := by rw [hT, hBinv]
      _ = inner ℂ (c.ρ (γ⁻¹ : GQ V) w) (T x) := (hT _ _).symm
      _ = inner ℂ (c.ρ γ (c.ρ (γ⁻¹ : GQ V) w)) (c.ρ γ (T x)) := (hc.2.1 _ _ _).symm
      _ = inner ℂ w (c.ρ γ (T x)) := by rw [hinv]
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.RowCoord.scalar_of_comm_rat c hc T hcomm
  have hx₀ : GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀) ≠ 0 := by
    rw [← hb1]
    exact b1.ne_zero i₀
  have hpos := GlobalTheory.CoefSpace.pairK_pos lam (fun _ => 1) _ hx₀
  rw [hgr] at hpos
  have h1 := hT (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀)))
  have hsq : inner ℂ (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) (e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))) =
      ((‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  rw [hμ, inner_smul_right, LinearEquiv.symm_apply_apply, hsq] at h1
  rw [← h1] at hpos
  have hn : 0 < ‖e0 (GlobalTheory.CoefSpace.bcVV σ lam (bVV K lam i₀))‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (e0.map_ne_zero_iff.2 hx₀)) 2
  obtain ⟨hre, him⟩ := Complex.lt_def.1 hpos
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.zero_re, Complex.zero_im] at hre him
  have hm : 0 < μ.re := (pos_iff_pos_of_mul_pos hre).2 hn
  have hμr : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by
    rw [Complex.ofReal_im]
    exact ((mul_eq_zero.1 him.symm).resolve_right hn.ne').symm)
  have hr : 0 < Real.sqrt μ.re := Real.sqrt_pos.2 hm
  have hr0 : ((Real.sqrt μ.re : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ x, e x = ((Real.sqrt μ.re : ℝ) : ℂ) • e0 x :=
    ⟨e0.trans (LinearEquiv.smulOfNeZero ℂ c.W _ hr0), fun _ => rfl⟩
  refine ⟨e, (Real.sqrt μ.re)⁻¹, inv_pos.2 hr, fun v => ?_, fun x y => ?_, fun γ γE g h1 h2 x => ?_⟩
  · rw [he, he0, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hr.ne', Complex.ofReal_one, one_smul]
  · rw [he, he, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt hm.le, hμr, ← inner_smul_right, ← hμ, hT, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rw [he, he, hR γ γE g h1 h2]
    exact ((c.ρ γ).map_smul _ _).symm

end GlobalTheory.Mem.CoefIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelMemChartLevelIffReductionFixesTypePrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


open GlobalTheory.Mem.Col2.TypeRead in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.typeRead_core : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0), I.StdF l Z u F → (∀ j v h, F.glevJ.fr j v h = 1) → ∀ (h1 : 1 ≤ B.R.m - 1) (β0 : Ch0 (B.R.m - 1)), ∃ w : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → Fin (B.R.N (B.R.m - 1)) → kv (I.rec7 l Z).host.F v, ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), (∃ j, ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → ∀ x, x ∈ F.levJ.Uloc v → (rll_put ((I.rec7 l Z).R.N (B.R.m - 1)) v x ∈ (F.ch (B.R.m - 1) h1 (succ_pred_m B.R) β0).lev.U ↔ ∀ j (hv : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), redM (I.rec7 l Z).host.F v (F.gl.mat j v hv (F.glevJ.fr j v hv) x) *ᵥ w j v hv = w j v hv) := by
  intro B X I hI hP l Z u Ch0 chOf0 F hF hfr h1 β0
  classical
  obtain ⟨k, H⟩ := hF.mid (B.R.m - 1) h1 (succ_pred_m _)
  obtain ⟨c, rfl⟩ := H.onto β0
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨by unfold Ranks.N; have := B.R.m_add_three_le_k; omega⟩
  have hX := (base_fields_primes_ok B X).1
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨wOf, hwOf, hwP, -⟩ := GlobalTheory.Mem.TypePrimes.primes_over_places B.fields (B.primes X) B.sp.cm hPr
  have hres := fun (a : Fin 2) (v : HeightOneSpectrum (𝓞 B.host.F)) (h : (B.host.g a : 𝓞 B.host.F) ∈ v.asIdeal) =>
    GlobalTheory.SplitResidue.exists_residue_equiv B.host.F B.host.E v (wOf a v h).1 (F.gl.phi a v h)
    (B.fields.conjO ((B.primes X).piG a)) (fun t => congrArg Prod.fst (F.gl.sp_alg a v h t)) (by
      have := F.gl.sp_pi a v h
      rw [hF.gl.piG] at this
      exact this) (hwP a v h).1
  choose ρ e hρ hρe using hres
  let P0 : ∀ a v h, rowSG (B.primes X) I.sel (I.tup I.mu0) := fun a v h => ⟨(wOf a v h).1, Finset.mem_union_left _ (wOf a v h).2⟩
  refine ⟨fun a v h i => e a v h (cvec ((I.stp u I.mu0 (B.R.m - 1)).rep c) (P0 a v h) i), fun v hv x hx => ?_⟩

  obtain ⟨a, ha⟩ := hv
  have hgram : gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) = 1 :=
    ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hB := basePi_of_ok hX hPr u
  have hLb : F.levJ.Lb = baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) := by
    ext y
    rw [← F.levJ_Lb h1 (chOf0 _ c)]
    refine (H.lb _ y).trans (Iff.trans ?_ (rll_mem_baseLb _ _ y).symm)
    simp only [baseL, Set.mem_setOf_eq]
    have hl : (lastIdx (B.R.N (B.R.m - 1))).1 + 1 = B.R.N (B.R.m - 1) := by
      have := NeZero.pos (B.R.N (B.R.m - 1)); simp only [lastIdx]; omega
    constructor
    · intro h
      choose r hr1 hr2 using h
      exact ⟨r, fun i => (hr1 i).symm, (hB.dvd _).2 (hr2 _ hl)⟩
    · rintro ⟨r, hr1, hr2⟩ i
      refine ⟨r i, (hr1 i).symm, fun hi => ?_⟩
      obtain rfl : i = lastIdx (B.R.N (B.R.m - 1)) := Fin.ext (by omega)
      exact (hB.dvd _).1 hr2
  have hxL : x ∈ levelVL B.sp.cm.sig (1 : Matrix (Fin (B.R.N (B.R.m - 1))) (Fin (B.R.N (B.R.m - 1))) B.host.E) v
      (baseLb B.host.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u)) := by
    have := F.levJ.Uloc_lev v hx
    have hgram' : gramN (I.rec7 l Z) ((I.rec7 l Z).R.m - 1) (Nat.sub_le _ _) = 1 := hgram
    rw [hLb] at this
    rw [hgram'] at this
    exact this
  have hT : v ∉ plUnder B.host.F ((B.primes X).vT u) := fun hvT => rls_T_notUnder hPr u v
      ((mem_plUnder_iff_norm B.sp.cm (rls_vT_iff hX hPr u) ((B.primes X).T u) (hPr.piT_norm u) v).1 hvT)
      ⟨(wOf a v ha).1, (wOf a v ha).2, (hwOf a v ha _).2 rfl⟩
  have hJ := put_mem_J0 B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) v hT x hxL
  have hUA := congruence_le_adelic_unitary B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) hJ
  refine (mem_iff_read H c _ hUA).trans ?_

  obtain ⟨b, hb⟩ : ∃ b, (c.1 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1)).1 = some b :=
    Option.isSome_iff_exists.1 (c.1.2.2 (by omega))
  have hgrp : levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1 = (I.idx I.mu0).levG (B.R.m - 1) b := by
    simp only [levGAt, hb, Option.elim]
  have hred := fun a' (h' : (B.host.g a' : 𝓞 B.host.F) ∈ v.asIdeal) => red_put_at B.sp.cm _ _ (B.primes X).vGs F.gl a' v h' (wOf a' v h') (e a' v h')
    (fun z => ⟨hρ a' v h' z ▸ (ρ a' v h' z).2, (congrArg (IsLocalRing.residue _) (Subtype.ext (hρ a' v h' z).symm)).trans (hρe a' v h' z)⟩) x hJ
  have hm0 : (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ ∈
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp := by
    rw [hgrp]
    refine inv_mem (fun w _ => ?_)
    by_cases hw : w = wOf a v ha
    · subst hw
      apply GlobalTheory.Mem.LastGrp.mem_levG_last _ _ _ _ _ _ _ hX hPr hI.sel_ok (hI.idx_ok I.mu0) (hI.sharp I.mu0) (B.R.m - 1) hmj b
        (wOf a v ha) _ (e a v ha)
      obtain ⟨M, hM, hMe⟩ := (F.glevJ.mem a v ha x (F.levJ.Uloc_lev v hx)).1 hx
      rw [hfr a v ha] at hMe
      have e2 : Matrix.GeneralLinearGroup.map (e a v ha).toRingHom
          (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩ (wOf a v ha)) = M := by
        apply Units.ext
        refine Eq.trans ?_ ((hred a ha).trans hMe.symm)
        rfl
      rw [e2]
      exact hM
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ w (fun h => hw ((hwOf a v ha w).1 h))
      show _ ∈ ((I.idx I.mu0).levG (B.R.m - 1) b w).H
      erw [e1]
      exact one_mem _

  have hQ : QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K) = ∅ := by
    rw [I.trueColumn_tuple_trivial_eq_one]
    exact twistPrimes_trivialTuple_empty I.sel I.S
  have hvG : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), P.1 ∈ (B.primes X).vGs := fun P =>
    (Finset.mem_union.1 P.2).resolve_right fun h => by simp [hQ] at h
  have hdeg : ∀ P : rowSG (B.primes X) I.sel (I.tup I.mu0), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 := fun P =>
    GlobalTheory.UnfoldTwoSided.degOne_bad hX hPr hI.sel_ok P
  have hcos := fun P => GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues hmj ((I.stp u I.mu0 (B.R.m - 1)).rep c)
    ((I.stp u I.mu0 (B.R.m - 1)).act c.1 (1, ⟨_, hm0⟩, 1) ((I.stp u I.mu0 (B.R.m - 1)).rep c))
    (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hJ⟩)⁻¹ rfl (Set.image_id _) P (hvG P) (hdeg P)
  constructor
  · rintro ⟨hJ', hm', hc'⟩ j hv
    have hfix := (hcos (P0 j v hv)).1 (congrFun hc' _)
    have hfix' := (fix_inv_iff _ _).1 hfix
    have key := (fix_map_iff (e j v hv) _ _).2 hfix'
    rw [hfr j v hv]
    have hM : redM (I.rec7 l Z).host.F v (F.gl.mat j v hv 1 x) = _ := (hred j hv).symm
    rw [hM]
    exact key
  · intro hall
    refine ⟨hJ, hm0, funext fun P => (hcos P).2 ?_⟩
    refine (fix_inv_iff _ _).2 ?_
    by_cases hw : (⟨P.1, hvG P⟩ : (B.primes X).vGs) = wOf a v ha
    · have hP : P = P0 a v ha := Subtype.ext (show P.1 = (wOf a v ha).1 from congrArg Subtype.val hw)
      subst hP
      have h2 := hall a ha
      rw [hfr a v ha] at h2
      refine (fix_map_iff (e a v ha) _ _).1 ?_
      have hM : redM (I.rec7 l Z).host.F v (F.gl.mat a v ha 1 x) = _ := (hred a ha).symm
      rw [hM] at h2
      exact h2
    · have e1 := red_put_off B.sp.cm (B.R.N (B.R.m - 1)) _ (B.primes X).vGs v x hJ ⟨P.1, hvG P⟩
        (fun h => hw ((hwOf a v ha _).1 h))
      erw [e1]
      simp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PenultimateChartLocalGroupMemNearLevelSetStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.penultimateChart_localGroup_mem_nearLevelSet : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Q → ∀ β (x : (K β).lev.Uloc v), x.1 ∈ GlobalTheory.Mem.Col2.QChi.NearSet I l Z a v := by
  first | exact @GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart | exact GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart | (intros; apply GlobalTheory.Mem.Col2.QChi.mem_nearSet_chart <;> assumption)
end

