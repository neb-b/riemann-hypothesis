module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLinearModelLatticeVacuumBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0399
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcTheta

section Lift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {χS χT : (AE D)ˣ →* Circle}
  {om : Om S T}

theorem contAut_ker (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ} (hφ : IsContAut A φ)
    (hΞ : IsThetaFunO ψ S T Ξ) (h : GA D T) (u : WO L T) :
    IsContAut A fun a => φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((hW.om_cont Ξ hΞ _).comp
    ((o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ hW Ξ hΞ _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (a, 1)) h
    ((o.resS T).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem liftA_add_left (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ φ' : GA D A → ℂ}
    {Ξ : WO S T → ℂ} (hφ : IsContAut A φ) (hφ' : IsContAut A φ') (hΞ : IsThetaFunO ψ S T Ξ) :
    liftA o om vA (φ + φ') Ξ = liftA o om vA φ Ξ + liftA o om vA φ' Ξ := by
  funext h w
  simp only [liftA, Pi.add_apply, add_mul]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ' hΞ h _))

theorem liftA_add_right (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ}
    {Ξ Ξ' : WO S T → ℂ} (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (hΞ' : IsThetaFunO ψ S T Ξ') :
    liftA o om vA φ (Ξ + Ξ') = liftA o om vA φ Ξ + liftA o om vA φ Ξ' := by
  funext h w
  simp only [liftA, map_add (f := _), Pi.add_apply, mul_add]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ' h _))

theorem liftA_smul_left (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA (c • φ) Ξ = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem liftA_smul_right (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA φ (c • Ξ) = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem liftA_equiv (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ}
    (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (a : GA D A) :
    liftA o om vA (fun x => φ (x * a)) (om (o.emb (a, 1), 1) Ξ) = liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA]
  refine Eq.trans ?_ (Comm.integral_right vA (contAut_ker o hW hφ hΞ h w).1 a)
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end Lift

theorem exists_linear_of_rel {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (R : M → N → Prop) (hex : ∀ x ∈ P, ∃! y, R x y)
    (hlin : ∀ (c : ℂ) x y x' y', R x y → R x' y' → R (c • x + x') (c • y + y')) :
    ∃ G : M →ₗ[ℂ] N, (∀ x, ∃ x', R x' (G x)) ∧ ∀ x ∈ P, R x (G x) := by
  choose F hF hFu using fun x : P => hex x.1 x.2
  have hc : ∀ (c : ℂ) (x x' : P), F (c • x + x') = c • F x + F x' := fun c x x' =>
    (hFu (c • x + x') _ (hlin c _ _ _ _ (hF x) (hF x'))).symm
  have h0 : F 0 = 0 := by
    have := hc 1 0 0
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let F' : P →ₗ[ℂ] N :=
    { toFun := F
      map_add' := fun x y => by simpa using hc 1 x y
      map_smul' := fun c x => by simpa [h0] using hc c x 0 }
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  refine ⟨F' ∘ₗ P.linearProjOfIsCompl Q hQ, fun x => ⟨_, hF _⟩, fun x hx => ?_⟩
  have e : P.linearProjOfIsCompl Q hQ x = ⟨x, hx⟩ := Submodule.linearProjOfIsCompl_apply_left hQ ⟨x, hx⟩
  rw [LinearMap.comp_apply, e]
  exact hF ⟨x, hx⟩

theorem exists_theta : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ S A L T o ζ _ hA vA χS χT om hW α α₀ β hsum
  obtain ⟨lS, lT, hlS, -, hlin⟩ := _root_.GlobalTheory.SplitLinAt.linModelAt D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := _root_.GlobalTheory.FinPl.overBasic D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add (f := _)]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := (hlin n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ)).1 (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.Top

theorem exists_pairB_of_range_eq {ι : Type} [Fintype ι] {n : ℕ} (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1) {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ w ∈ Formalism.L2.DIV.VV ℂ lam, ∀ v, ℓ v = Formalism.L2.DIV.pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) w := by
  have key : ∀ P, Formalism.L2.Col.polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := by
    intro P
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o P
    rw [ho] at h
    exact h
  have hval : ∀ v, ∃ P ∈ Formalism.L2.DIV.VV ℂ lam, j v = fnOf G (shiftOf lam) 1 P := by
    intro v
    have hv : j v ∈ ValC G lam := hr ▸ LinearMap.mem_range_self j v
    obtain ⟨P, hP, hPv⟩ := Submodule.mem_map.mp hv
    rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV] at hP
    exact ⟨P, hP, hPv.symm⟩
  let φ : V →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ ι n :=
    { toFun := fun v => Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)
      map_add' := fun x y => by rw [map_add (f := _)]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_add (j x) (j y)
      map_smul' := fun c x => by rw [map_smul]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_smul c (j x) }
  have hφ : ∀ v, φ v = Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) := fun _ => rfl
  have hmem : ∀ v, φ v ∈ Formalism.L2.DIV.VV ℂ lam := by
    intro v
    obtain ⟨P, hP, e⟩ := hval v
    rw [hφ, e, key]
    exact hP
  let φ' : V →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam := φ.codRestrict _ hmem
  have hφ' : ∀ v, (φ' v : Formalism.L2.DIV.Pol ℂ ι n) = φ v := fun _ => rfl
  have inj : Function.Injective φ' := by
    intro v v' h
    have h' : φ v = φ v' := by rw [← hφ', ← hφ', h]
    obtain ⟨P, -, e⟩ := hval v
    obtain ⟨P', -, e'⟩ := hval v'
    rw [hφ, hφ, e, e', key, key] at h'
    apply hinj
    rw [e, e', h']
  have surj : Function.Surjective φ' := by
    intro x
    have hx : fnOf G (shiftOf lam) 1 x.1 ∈ LinearMap.range j := by
      rw [hr]
      refine Submodule.mem_map.mpr ⟨x.1, ?_, rfl⟩
      rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
      exact x.2
    obtain ⟨v, hv⟩ := hx
    refine ⟨v, Subtype.ext ?_⟩
    rw [hφ', hφ, hv, key]
  let e := LinearEquiv.ofBijective φ' ⟨inj, surj⟩
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  let ψ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam) := ℓ ∘ₗ e.symm.toLinearMap
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := by
    have := pairingBNondegenerate_holds ℂ ι n lam
    exact LinearMap.flip_nondegenerate.mpr this
  let w := (LinearMap.BilinForm.toDual _ hB).symm ψ
  have hw : ∀ x, ψ x = pairBK lam x w := by
    intro x
    have h1 : LinearMap.BilinForm.toDual _ hB w = ψ := LinearEquiv.apply_symm_apply _ _
    rw [← h1, LinearMap.BilinForm.toDual_def, LinearMap.flip_apply]
  refine ⟨w.1, w.2, fun v => ?_⟩
  have h2 : ℓ v = ψ (e v) := by simp [ψ]
  rw [h2, hw, pairBK_apply]
  rfl

end GlobalTheory.Core.Rk.Top

namespace GlobalTheory.Core.Rk.Top

theorem sgT_eq_perIn_sgT {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  unfold Formalism.L2.Forms.sgT PerIn.sgT Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext i
  have h1 : (((I.rec7 l Z).fm u).sg τ).w i = ((I.perIn u a).sg τ).w i := rfl
  have h2 : (I.rec7 l Z).R = B.R := rfl
  rw [h1, h2]
  have hd : 2 ∣ B.R.t + 1 := by
    obtain ⟨k, hk⟩ := B.R.t_odd
    exact ⟨k + 1, by omega⟩
  rw [Nat.mul_div_assoc _ hd]
  push_cast
  ring

theorem exists_pairB_of_isJ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  intro B X I l Z u a S MX j hJ ℓ
  have hr := hJ.range
  rw [sgT_eq_perIn_sgT I l Z u a] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  exact exists_pairB_of_range_eq _ _ _ _ e j hJ.inj hr ℓ

end GlobalTheory.Core.Rk.Top

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteLocalSupportExchangeDataTwistPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QSuppTwo

theorem prod_mul_inv_mem {G : Type} [Group G] (H : Subgroup G) : ∀ (n : ℕ) (f : Fin n → G) (i : Fin n),
    (∀ i', i' ≠ i → f i' ∈ H) → (∀ y ∈ H, f i * y = y * f i) → (List.ofFn f).prod * (f i)⁻¹ ∈ H := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro hf0 hc0
      have hP : (List.ofFn fun k : Fin n => f k.succ).prod ∈ H := by
        apply Subgroup.list_prod_mem
        intro x hx
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
        exact hf0 _ (Fin.succ_ne_zero k)
      rw [List.ofFn_succ, List.prod_cons, hc0 _ hP, mul_assoc, mul_inv_cancel, mul_one]
      exact hP
    · intro hfk hck
      rw [List.ofFn_succ, List.prod_cons, mul_assoc]
      exact mul_mem (hfk 0 (Fin.succ_ne_zero k).symm)
        (ih (fun k => f k.succ) k (fun k' hk' => hfk _ (fun e => hk' (Fin.succ_injective _ e))) hck)

theorem mem_support_conv {G : Type} [Monoid G] : ∀ (n : ℕ) (f : Fin n → (G →₀ ℂ)) (g : G),
    g ∈ (conv (List.ofFn f)).support → ∃ x : Fin n → G, (∀ i, x i ∈ (f i).support) ∧ g = (List.ofFn x).prod := by
  classical
  intro n
  induction n with
  | zero =>
    intro f g hg
    simp only [List.ofFn_zero, conv, List.foldr_nil] at hg
    have := Finsupp.support_single_subset hg
    rw [Finset.mem_singleton] at this
    exact ⟨Fin.elim0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    intro f g hg
    rw [List.ofFn_succ] at hg
    simp only [conv, List.foldr_cons] at hg
    have h1 := Finsupp.support_sum hg
    rw [Finset.mem_biUnion] at h1
    obtain ⟨g₀, hg₀, h2⟩ := h1
    have h3 := Finsupp.support_sum h2
    rw [Finset.mem_biUnion] at h3
    obtain ⟨g', hg', h4⟩ := h3
    have h5 := Finsupp.support_single_subset h4
    rw [Finset.mem_singleton] at h5
    obtain ⟨x, hx, hxe⟩ := ih (fun k => f k.succ) g' hg'
    refine ⟨Fin.cons g₀ x, fun i => Fin.cases hg₀ (fun k => hx k) i, ?_⟩
    rw [List.ofFn_succ, List.prod_cons, h5, hxe]
    simp

end GlobalTheory.QSuppTwo

open GlobalTheory.QSuppTwo in
theorem GlobalTheory.QSuppTwo.main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ A : ∀ i, Finset (GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k), ∀ α, ∀ g ∈ (w.ε j α).support, ∃ a : ∀ i, GL ((F.Q i).X j ⊕ Fin (2 * σ + 2 + 1)) (F.Q i).k, ∀ i, a i ∈ A i ∧ g * ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) (a i))⁻¹ ∈ GlobalTheory.FinPl.grpOff (c.V j) (· = (F.Q i).q.v) := by
  classical
  intro D c v t w F hF j σ h
  have hd : ∀ i, j + (2 * σ + 2) = (F.Q i).s := fun i => by have := (F.Q i).hs; omega
  choose e he using fun i (α' : (F.Q i).Ch j) => (F.Q i).εL_at j (σ + 1) h (2 * σ + 2) (hd i) α'
  refine ⟨fun i => Finset.univ.biUnion fun α' => (e i α').support, ?_⟩
  intro α g hg
  rw [hF.ε j (σ + 1) h α] at hg
  have hg' := Finsupp.support_smul hg
  obtain ⟨x, hx, rfl⟩ := mem_support_conv _ _ g hg'
  have hpt : ∀ i, ∃ a ∈ (e i (F.eqv j α i)).support,
      (F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega) a = x i := by
    intro i
    have := hx i
    rw [(he i (F.eqv j α i)).2] at this
    have := Finsupp.mapDomain_support this
    rw [Finset.mem_image] at this
    exact this
  choose a ha hax using hpt
  refine ⟨a, fun i => ⟨Finset.mem_biUnion.2 ⟨F.eqv j α i, Finset.mem_univ _, ha i⟩, ?_⟩⟩
  have I := fun i => GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D (F.Q i).k (F.Q i).q (c.V j) _ ((F.Q i).FY j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega))
    ((F.Q i).gl j (2 * σ + 2 + 1) (by have := (F.Q i).hs; omega)) ((F.Q i).gl_loc j _ _)
  rw [hax i]
  apply prod_mul_inv_mem _ _ x i
  · intro i' hi'
    rw [← hax i']
    have hr : (F.Q i').gl j (2 * σ + 2 + 1) (by have := (F.Q i').hs; omega) (a i') ∈ GlobalTheory.FinPl.grpAt (c.V j) (· = (F.Q i').q.v) := by
      rw [← (I i').2.1]; exact ⟨_, rfl⟩
    exact (_root_.GlobalTheory.FinPl.SetCut.grp_split D (c.V j) ∅).2.2.2.2.2.2.1 _ _ (fun p hp hn => hi' (hF.inj (hp.symm.trans hn))) hr
  · intro y hy
    rw [← hax i]
    exact (I i).2.2.2.1 (a i) y hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleOfSupportedRankOneUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem exists_normOneAt_of_rank_one (D : D7) (L : HSp D) (v : GlobalTheory.FinPl.Pl D) (γ : GA D L) (hr : L.rank = 1)
    (hγ : γ ∈ grpAt L (· = v)) :
    ∃ c : AE D, NormOneAt v c ∧ NormOneAt v (cA D c) ∧
      Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
  haveI hs : Subsingleton (Fin L.rank) := ⟨fun a b => Fin.ext (by have := a.2; have := b.2; omega)⟩
  let i₀ : Fin L.rank := ⟨0, by omega⟩
  set c : AE D := Formalism.L2.Theta.mt L γ i₀ i₀ with hc
  have hmat : Formalism.L2.Theta.mt L γ = c • (1 : Matrix (Fin L.rank) (Fin L.rank) (AE D)) := by
    ext i j
    rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
    simp [hc]
  have hid : c - 1 ∈ idAt D (· = v) := by
    have h := (GlobalTheory.IwaPlace.mem_congGrp_iff L _ γ).1 hγ i₀ i₀
    simpa [hc] using h

  have hu := congrFun (congrFun (GlobalTheory.MixModel.mt_unitary L γ) i₀) i₀
  simp only [Matrix.mul_apply, Fintype.sum_subsingleton _ i₀, GlobalTheory.MixModel.adj, GlobalTheory.MixModel.gA,
    GlobalTheory.MixModel.rat, Matrix.map_apply, Matrix.transpose_apply] at hu
  have hg : HSpace.gram L i₀ i₀ ≠ 0 := by
    have := GlobalTheory.MixModel.gram_isUnit_det L
    rw [Matrix.det_eq_elem_of_subsingleton _ i₀] at this
    exact this.ne_zero
  have hgu : IsUnit (incA D (HSpace.gram L i₀ i₀)) := (Ne.isUnit hg).map _
  have h1 : cA D c * c = 1 := by
    rw [← hc] at hu
    have : (cA D c * c) * incA D (HSpace.gram L i₀ i₀) = 1 * incA D (HSpace.gram L i₀ i₀) := by
      rw [one_mul]
      calc (cA D c * c) * incA D (HSpace.gram L i₀ i₀)
          = cA D c * (incA D (HSpace.gram L i₀ i₀) * c) := by ring
        _ = incA D (HSpace.gram L i₀ i₀) := hu
    exact hgu.mul_right_cancel this
  have h2 : c * cA D c = 1 := by rw [mul_comm]; exact h1
  refine ⟨c, ⟨h2, hid⟩, ⟨?_, ?_⟩, hmat⟩
  · rw [← map_mul, h2, map_one]
  · have : cA D c - 1 = -(cA D c) * (c - 1) := by
      linear_combination h1
    rw [this]
    exact Ideal.mul_mem_left _ _ hid

end GlobalTheory.Core.Mi.LatMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticeChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SDLatY

theorem exists_selfDual_latY : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j, j < D.R.m → ∃ L : GlobalTheory.FinPl.Lat (Yc D j), IsSelfDualC (Yc D j) L := by
  intro D L hT Gi Gl Kc Yd cX ex W hp j hj
  have hC : W.Q.Rl.Char3 W.Q.F := hp.bot.hyp.2.2.2.1
  exact ⟨(pk W).ΛY j, GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D (Yc D j) ((pk W).βY j) ((pk W).ΛY j) _ (hC.lev.βY j hj)⟩

end GlobalTheory.SDLatY
end

