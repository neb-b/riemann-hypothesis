module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EigOfHasSat
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private theorem eig_of_hasSat {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w ρ B) {v : V} (hv : v ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL w (n := a))) (hv0 : v ≠ 0)
    (l : Module.Dual ℂ V) : UpperTheory.V.Af.Smo.Eig w B fun g => l (ρ g v) := by
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, mul_apply_eq_comp, GlobalTheory.LGrp.mem_fixed.1 hv k hk]
  · have he := (hB.2 v hv hv0).2.2.2 ϖ hϖ j hj
    let ev : V →+ ℂ :=
      { toFun := fun ψ => l (ρ y ψ)
        map_zero' := by simp
        map_add' := fun _ _ => by simp }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w a)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) ρ v)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans ((congrArg ev he).trans ?_))
    · simp [ev, map_mul]
    · simp [ev]

private theorem eigen_top {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ}
    [MeasurableSpace (GL (Fin a) (w.adicCompletion E))] [BorelSpace (GL (Fin a) (w.adicCompletion E))]
    (μ : Measure (GL (Fin a) (w.adicCompletion E))) [μ.IsHaarMeasure] (z : Fin a → ℂˣ)
    {f : GL (Fin a) (w.adicCompletion E) → ℂ} (hE : UpperTheory.V.Af.Smo.Eig w (Finset.univ.val.map z) f)
    (hf : ∀ g, ∀ k ∈ GroundTheory.Automorphic.GLnLocal.integralGL (w.adicCompletion E) a, f (g * k) = f g) :
    eigenSubalgebra μ z f hf = ⊤ := by
  obtain ⟨hKeq, hu, hq, -⟩ := UpperTheory.V.Af.Smo.sphDict E a w
  have hTj : UpperTheory.V.Af.Smo.TjSet := UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict
  have hT : ∀ r ≤ a, minusculeHecke μ r ∈ eigenSubalgebra μ z f hf := by
    intro r hr
    refine GlobalTheory.HenQ.ShellOp.minuscule_mem_of z hf hr fun g => ?_
    rw [hKeq, ← hTj E a w r hr, hE.eig _ hu r hr g, hq r hr,
      GlobalTheory.HenQ.ShellOp.esymm_eq, GlobalTheory.LFun.satEig]
  exact eigenSubalgebra_eq_top z hf hT (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hT a le_rfl))

end UpperTheory.Gal.Gen

open GroundTheory.Automorphic in
theorem UpperTheory.Gal.Gen.locOp_pf :
    UpperTheory.Gal.Gen.RepsEx → UpperTheory.Gal.Gen.Planch → UpperTheory.Gal.Gen.LocOp := by
  intro hR hP E _ _ w a
  classical
  borelize (GL (Fin a) (w.adicCompletion E))
  let μ : Measure (GL (Fin a) (w.adicCompletion E)) := Measure.haar
  obtain ⟨C0, hC0⟩ := hP (w.adicCompletion E) a μ
  have hKeq := (UpperTheory.V.Af.Smo.sphDict E a w).1
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = μ.real (GLnLocal.integralGL (w.adicCompletion E) a : Set (GL (Fin a) (w.adicCompletion E))) := ⟨_, rfl⟩
  refine ⟨m ^ 2 * C0, fun p hp => ?_⟩
  rw [← range_satakeTransform (μ := μ) (F := w.adicCompletion E) (n := a)] at hp
  obtain ⟨H, rfl⟩ := (AlgHom.mem_range _).1 hp
  obtain ⟨T, hT⟩ := hR (w.adicCompletion E) a μ H
  let h : GL (Fin a) (w.adicCompletion E) →₀ ℂ :=
    Finsupp.onFinset T (fun g => if g ∈ T then (m : ℂ) * (H : HeckeAlgebra μ) g else 0) (fun g hg => by
      by_contra hgT
      simp [hgT] at hg)
  have hsupp : h.support ⊆ T := Finsupp.support_onFinset_subset
  have hval : ∀ g ∈ T, h g = (m : ℂ) * (H : HeckeAlgebra μ) g := fun g hg => by
    simp [h, hg]
  refine ⟨h, fun g hg g' hg' hk => hT.1 g (hsupp hg) g' (hsupp hg') (hKeq ▸ hk), ?_, ?_⟩
  · calc ∑ g ∈ h.support, ‖h g‖ ^ 2 ≤ ∑ g ∈ T, ‖h g‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsupp fun _ _ _ => by positivity
      _ = m ^ 2 * ∑ g ∈ T, ‖(H : HeckeAlgebra μ) g‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [hval g hg, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ m ^ 2 * (C0 * ∫ θ : Fin a → UnitAddCircle, ‖evalAt (pt θ) (satakeTransform μ H)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hC0 H T hT) (by positivity)
      _ = _ := by ring
  · intro σ z hz v hv
    by_cases hv0 : v = 0
    · subst hv0
      simp [opOf]
    rw [← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_
    have hE := eig_of_hasSat w σ.ρ hz hv hv0 l
    have hf : ∀ g, ∀ k ∈ GLnLocal.integralGL (w.adicCompletion E) a, l (σ.ρ (g * k) v) = l (σ.ρ g v) := by
      rw [hKeq]
      exact hE.inv
    have h1 : H ∈ eigenSubalgebra μ z (fun g => l (σ.ρ g v)) hf := eigen_top w μ z hE hf ▸ Algebra.mem_top
    have h2 := h1 1
    simp only [one_mul, map_one, one_apply_eq_self] at h2
    have h3 := hT.2 (fun g => l (σ.ρ g v)) hf
    have h4 : l (opOf σ.ρ h v) = (m : ℂ) * ∑ g ∈ T, (H : HeckeAlgebra μ) g * l (σ.ρ g v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [opOf, Finsupp.sum_of_support_subset h hsupp _ (by simp), map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smul, hval g hg, smul_eq_mul, mul_assoc]
    rw [map_sub, map_smul, smul_eq_mul, h4, hm, ← h3, h2, sub_self]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaEig
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen GLnLocal

theorem UpperTheory.Gal.Gen.gammaEig_pf :
    UpperTheory.Gal.Gen.GammaEig := by
  intro F _ _ _ _ n _ _ μ _ z h g
  have hf : ∀ (g k : GL (Fin n) F), k ∈ integralGL F n →
      zonalSpherical μ z (g * k) = zonalSpherical μ z g :=
    fun g k hk => zonalSpherical_mul_right z g hk
  have hpos : (0 : ℝ) < μ.real ↑(integralGL F n) :=
    HeckeAlgebra.measureReal_compactOpen_pos μ (isCompact_integralGL F n) (isOpen_integralGL F n)
  have hne : (μ.real ↑(integralGL F n) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hpos.ne'
  have hmin : ∀ r, minusculeHecke μ r ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    intro r y
    rw [integral_minusculeHecke_mul hf y r, sum_zonalSpherical_gMat z r y]
    simp only [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have htop : eigenSubalgebra μ z (zonalSpherical μ z) hf = ⊤ :=
    eigenSubalgebra_eq_top z hf (fun r _ => hmin r)
      (GlobalTheory.HenQ.ShellOp.central_mem_of_top z hf (hmin n))
  have hmem : h ∈ eigenSubalgebra μ z (zonalSpherical μ z) hf := by
    rw [htop]
    exact Algebra.mem_top
  exact hmem g
end

