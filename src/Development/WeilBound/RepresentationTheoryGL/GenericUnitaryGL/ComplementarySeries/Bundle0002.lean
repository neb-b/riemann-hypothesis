module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.JacquetModuleThetaTwist
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace PositivityTheory.RgGu.NR.JmTh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := k) d) := by
  intro m
  let P := Equiv.piCongrLeft (fun b => GL (Fin (d b)) k) (Fin.revPerm : Equiv.Perm (Fin h))
  refine ⟨fun b => thetaW k (d b) (P m b), ?_⟩
  funext a
  show thetaW k _ (thetaW k _ (P m (Fin.revPerm a))) = m a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
  exact Equiv.piCongrLeft_apply_apply (fun b => GL (Fin (d b)) k) Fin.revPerm m a

theorem mem_unipRad_iff' {h N : ℕ} {d : Fin h → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N} {g : GL (Fin N) k} :
    g ∈ unipRad k e ↔ ∃ hg : g ∈ parab k e, leviProj k e ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, hp⟩
  · rintro ⟨hg, h1⟩
    exact ⟨⟨g, hg⟩, h1, rfl⟩

theorem thetaL_eq_one {h : ℕ} (d : Fin h → ℕ) (m : Levi k fun a => Fin (d a)) (hm : thetaL d m = 1) : m = 1 := by
  have key : ∀ b, m (Fin.rev b) = 1 := fun b => by
    have h2 : thetaW k (d (Fin.rev b)) (m (Fin.rev b)) = 1 := congrFun hm b
    have := congrArg (thetaW k (d (Fin.rev b))) h2
    rwa [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW, map_one] at this
  funext a
  obtain ⟨b, rfl⟩ := Fin.revPerm.surjective a
  exact key b

theorem thetaW_mem_unipRad_iff {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (g : GL (Fin N) k) :
    thetaW k N g ∈ unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd') ↔ g ∈ unipRad k (stdBlocks d hd) := by
  rw [mem_unipRad_iff', mem_unipRad_iff']
  constructor
  · rintro ⟨h1, h2⟩
    have hg : g ∈ parab k (stdBlocks d hd) := (thetaW_mem_parab_iff d hd hd' g).1 h1
    refine ⟨hg, thetaL_eq_one d _ ?_⟩
    rw [← leviProj_thetaW d hd hd' ⟨g, hg⟩]
    exact h2
  · rintro ⟨h1, h2⟩
    refine ⟨(thetaW_mem_parab_iff d hd hd' g).2 h1, ?_⟩
    have := leviProj_thetaW (A := k) d hd hd' ⟨g, h1⟩
    rw [h2, map_one] at this
    exact this

theorem twKer_theta {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    twKer (π.comp (thetaW k N)) (unipRad k (stdBlocks d hd)) 1 =
      twKer π (unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd')) 1 := by
  unfold twKer
  congr 1
  ext w
  constructor
  · rintro ⟨n, v, rfl⟩
    refine ⟨⟨thetaW k N n, (thetaW_mem_unipRad_iff (k := k) d hd hd' n).2 n.2⟩, v, ?_⟩
    simp
  · rintro ⟨n, v, rfl⟩
    have hn : thetaW k N (n : GL (Fin N) k) ∈ unipRad k (stdBlocks d hd) := by
      rw [← thetaW_mem_unipRad_iff d hd hd', GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
      exact n.2
    refine ⟨⟨_, hn⟩, v, ?_⟩
    simp [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]

theorem leviProj_thetaW_leviEmb {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (m : Levi k fun a => Fin (d a)) :
    ∃ u ∈ unipRad k (stdBlocks (fun a => d (Fin.rev a)) hd'),
      thetaW k N (leviEmb k (stdBlocks d hd) m) = u * leviEmb k (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d m) := by
  set e := stdBlocks d hd
  set e' := stdBlocks (fun a => d (Fin.rev a)) hd'
  have hx : thetaW k N (leviEmb k e m) ∈ parab k e' := (thetaW_mem_parab_iff d hd hd' _).2 (leviEmb_mem_parab k e m)
  have hy : leviEmb k e' (thetaL d m) ∈ parab k e' := leviEmb_mem_parab k e' _
  refine ⟨thetaW k N (leviEmb k e m) * (leviEmb k e' (thetaL d m))⁻¹, ?_, by group⟩
  rw [mem_unipRad_iff']
  refine ⟨(parab k e').mul_mem hx ((parab k e').inv_mem hy), ?_⟩
  have e1 : leviProj k e' ⟨_, hx⟩ = thetaL d m := by
    rw [leviProj_thetaW d hd hd' ⟨leviEmb k e m, leviEmb_mem_parab k e m⟩, leviProj_leviEmb]
  have e2 : leviProj k e' ⟨_, hy⟩ = thetaL d m := leviProj_leviEmb k e' _
  have : (⟨_, (parab k e').mul_mem hx ((parab k e').inv_mem hy)⟩ : parab k e') = ⟨_, hx⟩ * (⟨_, hy⟩)⁻¹ := rfl
  rw [this, map_mul, map_inv, e1, e2, mul_inv_cancel]

def jacTheta {h N : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    (jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d)) :=
  .mk (Submodule.quotEquivOfEq _ _ (twKer_theta d hd hd' π)) fun m => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    obtain ⟨u, hu, hm⟩ := leviProj_thetaW_leviEmb (k := k) d hd hd' m
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearEquiv.coe_coe, MonoidHom.comp_apply, jac, jacU,
      twist_apply, LinearMap.smul_apply, jacquet_mk, LinearEquiv.map_smul, Submodule.quotEquivOfEq_mk,
      deltaHalf_thetaL, MonoidHom.inv_apply]
    congr 1
    rw [hm, map_mul, Module.End.mul_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    refine Submodule.subset_span ⟨⟨u, hu⟩, π (leviEmb k (stdBlocks (fun a => d (Fin.rev a)) hd') (thetaL d m)) v, ?_⟩
    simp

theorem jm_congr {h N : ℕ} {y z : Fin h → IrrGL (k := k)} (hyz : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N)
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) : jm y hy π = jm z hz π := by
  subst hyz
  rfl

theorem jacquet_module_theta_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hGK : GKLocal k) {h N : ℕ} (x : Fin h → IrrGL (k := k))
    (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) :
    jm x hd (π.comp (thetaW k N)) = jm (dualRev hA x) (sum_dualRev hA x hd) π := by
  have hd' : ∑ a, (x (Fin.rev a)).1 = N := sum_dualRev hA x hd
  have T1 := piTensorRevEquiv (fun a => (x a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK x a) (revPi fun a => GL (Fin (x a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (x a).1) fun a => (dualRev hA x a).rep)
  have T := (T1.trans T2).trans T3
  unfold jm
  rw [jhMult_congr_right _ (jacTheta (fun a => (x a).1) hd hd' π), jhMult_congr_left T]
  exact GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective (thetaL fun a => (x a).1) (thetaL_surjective _) _ _

end PositivityTheory.RgGu.NR.JmTh

namespace PositivityTheory.RgGu.NR

open JmTh

theorem jmTheta (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.JmTheta k := by
  intro N V _ _ π _ _ a b hd hd'
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  have hGK : GKLocal k := _root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  rw [jacquet_module_theta_twist hA hGK ![a, b] hd π]
  refine jm_congr ?_ _ _ π
  rw [dualRev_eq hA]
  funext i
  fin_cases i <;> rfl

end PositivityTheory.RgGu.NR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SomeRed
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace SomeRed

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem intw {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toLinearEquiv (π g v) = σ g (E.toLinearEquiv v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw' {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (v : V) :
    E.toIntertwiningMap.toLinearMap (π g v) = σ g (E.toIntertwiningMap.toLinearMap v) :=
  Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g v

theorem intw_symm {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (g : G) (w : W) :
    E.toLinearEquiv.symm (σ g w) = π g (E.toLinearEquiv.symm w) := by
  apply E.toLinearEquiv.injective
  rw [intw E, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem smooth_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsSmooth π) : IsSmooth σ := by
  intro w
  have e : {g : G | σ g w = w} = {g : G | π g (E.toLinearEquiv.symm w) = E.toLinearEquiv.symm w} := by
    ext g
    simp only [Set.mem_setOf_eq]
    rw [← intw_symm E]
    exact ⟨fun h => by rw [h], fun h => E.toLinearEquiv.symm.injective h⟩
  rw [e]
  exact h _

theorem admissible_of_equiv [TopologicalSpace G] {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ)
    (h : IsAdmissible π) : IsAdmissible σ := by
  refine ⟨smooth_of_equiv E h.1, fun K hK hc => ?_⟩
  haveI := h.2 K hK hc
  have hle : fixed σ K ≤ (fixed π K).map E.toLinearEquiv.toLinearMap := by
    intro w hw
    refine ⟨E.toLinearEquiv.symm w, ?_, E.toLinearEquiv.apply_symm_apply w⟩
    intro x
    have hx := hw x
    show π (x : G) (E.toLinearEquiv.symm w) = _
    rw [← intw_symm E]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hx ⊢
    rw [hx]
  exact Submodule.finiteDimensional_of_le hle

theorem sesq_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : HasSesq σ) :
    HasSesq π := by
  obtain ⟨B, hB, hi⟩ := h
  refine ⟨(B.comp E.toLinearEquiv.toLinearMap).compl₂ E.toLinearEquiv.toLinearMap, ?_, fun g v w => ?_⟩
  · intro h0
    apply hB
    ext v w
    have := LinearMap.congr_fun (LinearMap.congr_fun h0 (E.toLinearEquiv.symm v)) (E.toLinearEquiv.symm w)
    have e1 : E.toIntertwiningMap.toLinearMap (E.toLinearEquiv.symm v) = v := E.toLinearEquiv.apply_symm_apply v
    have e2 : E.toIntertwiningMap.toLinearMap (E.toLinearEquiv.symm w) = w := E.toLinearEquiv.apply_symm_apply w
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.zero_apply] at this ⊢
    rw [e1, e2] at this
    exact this
  · simp only [LinearMap.compl₂_apply, LinearMap.comp_apply]
    rw [intw' E, intw' E, hi]

theorem unit_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : IsUnitarisable π) :
    IsUnitarisable σ :=
  GlobalTheory.GenericUnitary.isUnitarisable_of_equiv E h

theorem irr_of_equiv {π : Representation ℂ G V} {σ : Representation ℂ G W} (E : π.Equiv σ) (h : π.IsIrreducible) :
    σ.IsIrreducible :=
  GlobalTheory.Parabolic.isIrreducible_of_equiv E h

theorem unit_twist {ρ : Representation ℂ G V} (h : IsUnitarisable ρ) (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    IsUnitarisable (twist ρ χ) := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  show B ((χ g : ℂ) • ρ g v) ((χ g : ℂ) • ρ g w) = B v w
  rw [B.map_smul, LinearMap.smul_apply, (B _).map_smulₛₗ, h3, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj', hχ g]
  simp

end SomeRed

open SomeRed

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem chi_apply (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    (chi k d s g : ℂ) = ((nabs k (Matrix.GeneralLinearGroup.det (g 0)) : ℝ) : ℂ) ^ (-(s : ℂ)) *
      ((nabs k (Matrix.GeneralLinearGroup.det (g 1)) : ℝ) : ℂ) ^ (s : ℂ) := by
  simp [chi, val_absPow]

theorem norm_chi (d : ℕ) (s : ℝ) (g : Levi k fun _ : Fin 2 => Fin d) :
    ‖(chi k d s g : ℂ)‖ = nabs k (Matrix.GeneralLinearGroup.det (g 0)) ^ (-s) *
      nabs k (Matrix.GeneralLinearGroup.det (g 1)) ^ s := by
  rw [chi_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _),
    Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k _)]
  simp

set_option maxHeartbeats 2000000 in
theorem someRed_of (h1 : Complementary) (h2 : Compact k) (h3 : Bound k) (h4 : Herm k) (h5 : ProdModel k) :
    SomeRed k := by
  intro x hx hu
  by_contra hcon
  push_neg at hcon
  set d := x.1 with hdd
  have hd2 : ∀ s : ℝ, ∑ a, (![x.nu (-(s : ℂ)), x.nu (s : ℂ)] a).1 = x.1 + x.1 := fun s => by
    simp [Fin.sum_univ_two, IrrGL.nu, IrrGL.tw]
  have hirr : ∀ s : ℝ, 0 ≤ s → (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)).IsIrreducible := by
    intro s hs
    obtain ⟨N, hd, hi⟩ := hcon s hs
    have e : N = x.1 + x.1 := hd.symm.trans (hd2 s)
    subst e
    exact hi
  let τ := piTensor fun _ : Fin 2 => x.rep
  obtain ⟨K₀, F, hKo, hKc, hF, hFe⟩ := h2 d _ τ
  have hE : ∀ s : ℝ, (F s).Equiv (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s =>
    (hFe s).some.trans (h5 x s (hd2 s)).some.symm
  have hsm : ∀ s : ℝ, IsSmooth (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s => isSmooth_prodIrr _ _
  have hadm : ∀ s : ℝ, 0 ≤ s → IsAdmissible (prodIrr ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] (hd2 s)) := fun s hs =>
    GlobalTheory.CompanionTheory.BZCuspPair.irrAdm k _ _ _ (hsm s) (hirr s hs)
  have hxu : IsUnitarisable τ := GlobalTheory.SmGL.UnitInd.isUnitarisable_piTensor fun _ => hu
  have hU0 : IsUnitarisable (F 0) := by
    refine unit_of_equiv (hFe 0).some.symm (GlobalTheory.SmGL.UnitInd.isUnitarisable_parInd _ (unit_twist hxu _ fun g => ?_))
    rw [norm_chi]
    simp
  have hUs := h1 _ _ K₀ hKo hKc F hF (fun s hs => ⟨admissible_of_equiv (hE s).symm (hadm s hs),
    smooth_of_equiv (hE s).symm (hsm s), irr_of_equiv (hE s).symm (hirr s hs),
    sesq_of_equiv (hE s) (h4 x hu s _ (hd2 s) (hirr s hs))⟩) hU0

  have hd0 : 0 < d := hx.1
  set s : ℝ := (d : ℝ) with hs
  have hs0 : 0 ≤ s := by positivity
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar x.2.rep.smooth x.2.rep.irr
  obtain ⟨t, -, ht⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hω1 : ‖(ω t : ℂ)‖ = 1 := by
    obtain ⟨B, b1, b2, b3⟩ := hu
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
    obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
    have e := b3 (Matrix.GeneralLinearGroup.scalar (Fin x.1) t) v v
    rw [hω t v, B.map_smul, LinearMap.smul_apply, (B _).map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.mul_conj'] at e
    have hp := b2 v hv
    have hne : B v v ≠ 0 := fun h0 => by rw [h0] at hp; simp at hp
    have e2 : ((‖(ω t : ℂ)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hne (e.trans (one_mul _).symm)
      exact_mod_cast this
    have e3 : ‖(ω t : ℂ)‖ ^ 2 = 1 := by exact_mod_cast e2
    have hn := norm_nonneg (ω t : ℂ)
    nlinarith
  let g : Levi k fun _ : Fin 2 => Fin d := ![Matrix.GeneralLinearGroup.scalar (Fin d) t, 1]
  let c : ℂ := (chi k d s g : ℂ) * (ω t : ℂ)
  have hτ : ∀ w, τ g w = (ω t : ℂ) • w := by
    intro w
    induction w using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      have hfun : (fun a : Fin 2 => x.rep (g a) (f a)) = Function.update f 0 ((ω t : ℂ) • f 0) := by
        funext a
        fin_cases a
        · simp [g]
          exact hω t (f 0)
        · simp [g]
      rw [map_smul, piTensor_tprod, hfun, MultilinearMap.map_update_smul, Function.update_eq_self, smul_comm]
      rfl
    | add a b ha hb => rw [map_add (f := _), ha, hb, smul_add]
  have hc : ∀ w, twist τ (chi k d s) g w = c • w := fun w => by
    show (chi k d s g : ℂ) • τ g w = c • w
    rw [hτ, smul_smul]
  have hW : Nontrivial (PiTensorProduct ℂ fun _ : Fin 2 => x.2.rep.V) := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    have hi := irr_of_equiv (hFe s).some (irr_of_equiv (hE s).symm (hirr s hs0))
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
    obtain ⟨f, f', hff⟩ := exists_pair_ne (IndSp (blk2 d) (twist τ (chi k d s)))
    exact hff (Subtype.ext (Subtype.ext (funext fun _ => Subsingleton.elim _ _)))
  have hb := h3 d _ (twist τ (chi k d s))
    (isSmooth_twist (isSmooth_piTensor fun _ => x.2.rep.smooth)
      (((isSmoothChar_absPow (-(s : ℂ))).detChar.comp _ (continuous_apply 0)).mul
        ((isSmoothChar_absPow (s : ℂ)).detChar.comp _ (continuous_apply 1))))
    (admissible_of_equiv ((hE s).symm.trans (hFe s).some) (hadm s hs0))
    (unit_of_equiv (hFe s).some (hUs s hs0)) t c ht.le hc
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin d) t) = t ^ d := by
    ext
    simp [Matrix.GeneralLinearGroup.scalar]
  have hnp : ∀ m : ℕ, nabs k (t ^ m) = nabs k t ^ m := fun m => by simp [nabs]
  have hn1 : nabs k (1 : kˣ) = 1 := by simp [nabs]
  have htp : 0 < nabs k t := nabs_pos' k t
  have hnc : ‖c‖ = nabs k t ^ (-((d : ℝ) * s)) := by
    simp only [c, norm_mul, hω1, mul_one, norm_chi]
    have e0 : g 0 = Matrix.GeneralLinearGroup.scalar (Fin d) t := rfl
    have e1 : g 1 = 1 := rfl
    rw [e0, e1, hdet, hnp, map_one, hn1, Real.one_rpow, mul_one, ← Real.rpow_natCast, ← Real.rpow_mul htp.le]
    ring_nf
  rw [hnc, ← Real.rpow_add htp] at hb
  have hlt : 1 < nabs k t ^ (-((d : ℝ) * s) + ((d * d : ℕ) : ℝ) / 2) := by
    refine Real.one_lt_rpow_of_pos_of_lt_one_of_neg htp ht ?_
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    rw [hs]
    push_cast
    nlinarith
  linarith

end PositivityTheory.RgGu.NR

end
end

