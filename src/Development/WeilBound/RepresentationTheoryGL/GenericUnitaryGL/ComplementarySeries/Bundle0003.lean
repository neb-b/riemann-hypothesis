module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0582
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0387
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.NontrivialOfIsIrreducible
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace PositivityTheory.RgGu.NR

namespace NuP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hi : π.IsIrreducible) : Nontrivial V := by
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

theorem dualCl_fst (x : IrrGL (k := k)) : (dualCl x).1 = x.1 := by
  unfold dualCl
  split <;> rfl

end NuP

set_option maxHeartbeats 4000000 in
open NuP in
theorem nuPair_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : GlobalTheory.BZSeg.DerivJac k) (h2 : GlobalTheory.BZSeg.JmTheta k) (h3 : DerFin k) : GlobalTheory.BZSeg.NuPair k := by
  intro N V _ _ ω hs hi hng
  have hA := GlobalTheory.CompanionTheory.BZCuspPair.irrAdm
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  have hg : ¬ IsGenericFor ψ ω := fun h => hng ⟨ψ, hc, hψ, h⟩
  have hnt : Nontrivial V := nontrivial_of_isIrreducible hi
  obtain ⟨n, hn0, hnN, hnt2, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc hψ N ω hs hnt hg
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - (n + 1) - 1, by omega⟩
  have hc' := continuous_inv_addChar ψ hc
  have hψ' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart ω.dual).subtype
  have hBa : ∀ a b, B a b = (b : Module.Dual ℂ V) a := fun _ _ => rfl
  have hB : ∀ g a b, B (ω g a) (contra ω g b) = B a b := by
    intro g a b
    simp only [hBa, contra_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := fun v hv =>
    GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv
  obtain ⟨B', hB', hn'⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc hψ n j ω (contra ω) hs (isSmooth_contra _) B hB hnd
    (GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc hψ n j ω hs hlow)
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt2
  have hfl := h3 ψ hc hψ (n + 1) j V ω hs hi
  obtain ⟨S, f, hf⟩ := _root_.GlobalTheory.CompanionTheory.IrrSub.exists_irrRep_injective k (n + 1) _ _ _ _ (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j hs) hD
    (IsSubquotient.refl _) hfl
  have := nontrivial_of_irr S
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : S.V)
  have hw1 : f w₀ ≠ 0 := fun h => hw₀ (hf (by rw [h, map_zero]))
  obtain ⟨w', hw'⟩ := hn' (f w₀) hw1
  obtain ⟨Q, hQ, hQcl⟩ := _root_.GlobalTheory.CompanionTheory.DualQuot.exists_subquotient_dual_nu k (n + 1) j _ S (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω))
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j (isSmooth_contra _)) (B'.comp f.toLinearMap)
    (fun g w v => by
      have := hB' g (f w) v
      simpa [f.isIntertwining] using this)
    (fun h0 => hw' (by simpa using LinearMap.congr_fun (LinearMap.congr_fun h0 w₀) w'))
  have hflω : HasFiniteLength ω := hasFiniteLength_of_isIrreducible hi
  obtain ⟨β, hd1, hβ, hj1⟩ := h1 ψ hc hψ n j V ω hs hflω S (IsSubquotient.of_injective f hf)
  have hic : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  obtain ⟨β'', hd2, hβ'', hj2⟩ := h1 ψ⁻¹ hc' hψ' n j _ (contra ω) (isSmooth_contra _)
    (hasFiniteLength_of_isIrreducible hic) Q hQ

  have hGK : Zc.Cos.GKLocal k := _root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  have hsθ : IsSmooth ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hs
  have hiθ : Representation.IsIrreducible
      ((ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))).comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW]
    exact hi
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) hsθ hiθ
  rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW] at E
  have hj3 : 1 ≤ jm ![(IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)), β''] hd2
      (ω.comp (Zc.Cos.thetaW k (n + 1 + j + 1))) := by
    rw [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv _ hd2 _ _ E]
    exact hj2
  set α : IrrGL (k := k) := (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) with hα
  set Q' : IrrGL (k := k) := (IrrGL.of Q.ρ Q.smooth Q.irr).nu (-(((j : ℂ) + 1) / 2)) with hQ'
  have hsum2 : ∀ (x y : IrrGL (k := k)), ∑ a, (![x, y] a).1 = x.1 + y.1 := fun x y => by
    simp [Fin.sum_univ_two]
  have hd3 : ∑ i, (![dualCl β'', dualCl Q'] i).1 = n + 1 + j + 1 := by
    rw [hsum2, dualCl_fst, dualCl_fst]
    rw [hsum2] at hd2
    omega
  have hj4 := hj3
  rw [h2 _ V ω hs hflω Q' β'' hd2 hd3] at hj4

  have hcls : dualCl Q' = α.nu 1 := by
    rw [hQ', hQcl, hα, IrrGL.nu_nu, IrrGL.nu_nu, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA]
    congr 1
    ring
  have key : ∀ u : IrrGL (k := k), u = α.nu 1 → ∀ hdu : ∑ i, (![dualCl β'', u] i).1 = n + 1 + j + 1,
      1 ≤ jm ![dualCl β'', u] hdu ω → ∃ hd' : ∑ a, (![dualCl β'', α.nu 1] a).1 = n + 1 + j + 1,
        1 ≤ jm ![dualCl β'', α.nu 1] hd' ω := by
    rintro u rfl hdu h
    exact ⟨hdu, h⟩
  obtain ⟨hd', hj5⟩ := key _ hcls hd3 hj4
  have hβ''1 : β''.1 = j + 1 := hβ''
  refine ⟨α, β, dualCl β'', hd1, hd', ?_, ?_, ?_, hj1, hj5⟩
  · show 0 < (IrrGL.of S.ρ S.smooth S.irr).1
    show 0 < n + 1
    omega
  · omega
  · rw [dualCl_fst, hβ''1, hβ]

end PositivityTheory.RgGu.NR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ThetaContra
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil Zc Zc.Cos

namespace PositivityTheory.RgGu.NR

namespace HermB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontriv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem congrProd {h N : ℕ} {x y : Fin h → IrrGL (k := k)} (e : x = y) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

def yy (x : IrrGL (k := k)) (s : ℝ) : Fin 2 → IrrGL (k := k) := ![x.nu (-(s : ℂ)), x.nu (s : ℂ)]

theorem eqv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (g : G) (v : V) :
    e (ρ g v) = σ g (e v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

theorem theta_contra (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (π.comp (thetaW k N))
    (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hs) (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hi)
  rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π] at E

theorem hasSesq_of {G V V₁ V₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (π : Representation ℂ G V)
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (hi : π.IsIrreducible) (e₁ : π.Equiv π₁)
    (hc : ConjEquiv π₁ π₂) (e₂ : π₂.Equiv (contra π)) : HasSesq π := by
  obtain ⟨φ0, hφb, hφi⟩ := hc
  let Φ : V →ₛₗ[starRingEnd ℂ] smoothPart π.dual :=
    (e₂.toLinearEquiv.toLinearMap.comp φ0).comp e₁.toLinearEquiv.toLinearMap
  have hΦ : ∀ v, Φ v = e₂ (φ0 (e₁ v)) := fun _ => rfl
  have hΦb : Function.Injective Φ := (e₂.toLinearEquiv.injective.comp hφb.1).comp e₁.toLinearEquiv.injective
  have hΦi : ∀ g v, Φ (π g v) = contra π g (Φ v) := fun g v => by rw [hΦ, hΦ, eqv e₁, hφi, eqv e₂]
  haveI := nontriv _ hi
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => (Φ w : Module.Dual ℂ V) v)
    (fun v v' w => map_add _ v v') (fun c v w => map_smul _ c v)
    (fun v w w' => by rw [map_add (f := _)]; rfl) (fun c v w => by rw [map_smulₛₗ]; rfl), ?_, ?_⟩
  · intro hB
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    refine hw (hΦb ((Subtype.ext (LinearMap.ext fun v => ?_)).trans (map_zero Φ).symm))
    exact LinearMap.congr_fun₂ hB v w
  · intro g v w
    show (Φ (π g w) : Module.Dual ℂ V) (π g v) = (Φ w : Module.Dual ℂ V) v
    rw [hΦi, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end HermB

set_option maxHeartbeats 2000000 in
open HermB in
theorem herm_ofB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : ConjProd k) (h2 : ConjDual k) : Herm k := by
  intro x hxu s N hd hirr
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := _root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal hA
  change HasSesq (prodIrr (yy x s) hd)
  change (prodIrr (yy x s) hd).IsIrreducible at hirr

  obtain ⟨E5⟩ := theta_contra hGK (prodIrr (yy x s) hd) (isSmooth_prodIrr _ _) hirr
  obtain ⟨hd', ⟨E4⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse (k := k) (h := 2) (N := N) hA hGK (yy x s) hd

  let c : Fin 2 → ℝ := ![-s, s]
  have hM : ∑ _a : Fin 2, x.1 = N := by
    rw [← hd, Fin.sum_univ_two, Fin.sum_univ_two]; rfl
  let χ : Fin 2 → kˣ →* ℂˣ := fun a => absPow k ((c a : ℝ) : ℂ)
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  let πs : Fin 2 → Representation ℂ (GL (Fin x.1) k) x.2.rep.V := fun a => twist x.rep (detChar (Fin x.1) (χ a))
  let σs : Fin 2 → Representation ℂ (GL (Fin x.1) k) (smoothPart x.rep.dual) :=
    fun a => twist (contra x.rep) (detChar (Fin x.1) (χ a))
  have hsπ : ∀ a, IsSmooth (πs a) := fun a => isSmooth_twist x.2.rep.smooth (hχ a).detChar
  have hiπ : ∀ a, (πs a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have hic : (contra x.rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  have hsσ : ∀ a, IsSmooth (σs a) := fun a => isSmooth_twist (isSmooth_contra _) (hχ a).detChar
  have hiσ : ∀ a, (σs a).IsIrreducible := fun a => isIrreducible_twist hic _
  have hcj := h1 2 N (fun _ => x.1) hM (fun _ => x.2.rep.V) (fun _ => smoothPart x.rep.dual) πs σs
    (fun a => h2 x.1 x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr hxu (c a))
  have E1 := prodIrrEquiv hM πs hsπ hiπ
  have E2 := prodIrrEquiv hM σs hsσ hiσ
  have e0 : ((-s : ℝ) : ℂ) = -(s : ℂ) := by push_cast; ring
  have keyπ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist x.rep (detChar (Fin x.1) t)) (isSmooth_twist x.2.rep.smooth ht.detChar)
        (isIrreducible_twist x.2.rep.irr _) = x.tw t ht := by
    intro t ht
    have := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr t ht
    rw [IrrGL.of_rep] at this
    exact this.symm
  have keyσ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist (contra x.rep) (detChar (Fin x.1) t)) (isSmooth_twist (isSmooth_contra _) ht.detChar)
        (isIrreducible_twist hic _) = (dualCl x).tw t ht := by
    intro t ht
    have := IrrGL.tw_of (contra x.rep) (isSmooth_contra _) hic t ht
    rw [← GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA x] at this
    exact this.symm
  have fπ : (fun a => IrrGL.of (πs a) (hsπ a) (hiπ a)) = yy x s := by
    funext a
    rw [keyπ _ (hχ a)]
    fin_cases a
    · show x.tw (absPow k ((-s : ℝ) : ℂ)) _ = x.nu (-(s : ℂ))
      simp only [IrrGL.nu, e0]
    · rfl
  have fσ : (fun a => IrrGL.of (σs a) (hsσ a) (hiσ a)) = fun a => dualCl (yy x s (Fin.rev a)) := by
    funext a
    rw [keyσ _ (hχ a)]
    fin_cases a
    · show (dualCl x).tw (absPow k ((-s : ℝ) : ℂ)) _ = dualCl (x.nu (s : ℂ))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (s : ℂ)]
      simp only [IrrGL.nu, e0]
    · show (dualCl x).tw (absPow k ((s : ℝ) : ℂ)) _ = dualCl (x.nu (-(s : ℂ)))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (-(s : ℂ)), neg_neg]
      rfl
  obtain ⟨E0⟩ := congrProd fπ.symm hd hM
  obtain ⟨E3⟩ := congrProd fσ hM hd'
  exact hasSesq_of _ _ _ hirr (E0.trans E1.symm) hcj ((E2.trans E3).trans (E4.symm.trans E5))

end PositivityTheory.RgGu.NR

end
end

