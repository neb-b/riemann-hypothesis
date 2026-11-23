module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ZigClosed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasSym
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.casSym :
    UpperTheory.V.Cj.H.CasSym := by
  intro E _ _ _ a ha μ _ _ n e c
  have hG := gardFacts E a ha μ
  have hC := (clFacts E a μ).1
  have hcomb : ∀ (s t : ℂ), ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (s • φ + t • ψ) = s • cl μ φ + t • cl μ ψ :=
    fun s t φ hφ ψ hψ => (hC φ ψ s t (hG φ hφ).2.1 (hG ψ hψ).2.1).2
  have hL : ∀ X, ∀ φ ∈ gard μ, lie E a X φ ∈ gard μ := fun X φ hφ => (hG φ hφ).2.2.2.1 X
  have hskew : ∀ X, ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ,
      inner ℂ (cl μ (lie E a X φ)) (cl μ ψ) = -inner ℂ (cl μ φ) (cl μ (lie E a X ψ)) := by
    intro X φ hφ ψ hψ
    have h := skew_lie_action_L2 E a μ X φ ψ (hG φ hφ).1 (hG ψ hψ).1 (hG φ hφ).2.1 (hG ψ hψ).2.1
      (hG _ (hL X φ hφ)).2.1 (hG _ (hL X ψ hψ)).2.1
    rw [cl_eq (hG φ hφ).2.1, cl_eq (hG ψ hψ).2.1, cl_eq (hG _ (hL X φ hφ)).2.1, cl_eq (hG _ (hL X ψ hψ)).2.1]
    exact eq_neg_of_add_eq_zero_left h
  let P : Module.End ℂ (Sm E a) → Prop := fun T => (∀ φ ∈ gard μ, T φ ∈ gard μ) ∧
    ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, inner ℂ (cl μ (T φ)) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (T ψ))
  have hP1 : P 1 := ⟨fun _ h => h, fun _ _ _ _ => rfl⟩
  have hPc : ∀ (s t : ℝ) (T S : Module.End ℂ (Sm E a)), P T → P S → P ((s : ℂ) • T + (t : ℂ) • S) := by
    intro s t T S hT hS
    refine ⟨fun φ hφ => ?_, fun φ hφ ψ hψ => ?_⟩
    · exact add_mem (Submodule.smul_mem _ _ (hT.1 φ hφ)) (Submodule.smul_mem _ _ (hS.1 φ hφ))
    · change inner ℂ (cl μ ((s : ℂ) • T φ + (t : ℂ) • S φ)) (cl μ ψ) =
        inner ℂ (cl μ φ) (cl μ ((s : ℂ) • T ψ + (t : ℂ) • S ψ))
      rw [hcomb _ _ _ (hT.1 φ hφ) _ (hS.1 φ hφ), hcomb _ _ _ (hT.1 ψ hψ) _ (hS.1 ψ hψ), inner_add_left,
        inner_add_right, inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal,
        Complex.conj_ofReal, hT.2 φ hφ ψ hψ, hS.2 φ hφ ψ hψ]
  have hP0 : P 0 := by
    have h := hPc 0 0 1 1 hP1 hP1
    simpa using h
  have hPa : ∀ T S, P T → P S → P (T + S) := fun T S hT hS => by
    have h := hPc 1 1 T S hT hS
    simpa using h
  have hPs : ∀ (t : ℝ) T S, P T → P S → P (T - (t : ℂ) • S) := fun t T S hT hS => by
    have h := hPc 1 (-t) T S hT hS
    rwa [Complex.ofReal_one, one_smul, Complex.ofReal_neg, neg_smul, ← sub_eq_add_neg] at h
  have hPsq : ∀ X, P (lie E a X * lie E a X) := fun X =>
    ⟨fun φ hφ => hL X _ (hL X φ hφ), fun φ hφ ψ hψ => by
      change inner ℂ (cl μ (lie E a X (lie E a X φ))) (cl μ ψ) = inner ℂ (cl μ φ) (cl μ (lie E a X (lie E a X ψ)))
      rw [hskew X _ (hL X φ hφ) ψ hψ, hskew X φ hφ _ (hL X ψ hψ), neg_neg]⟩
  have hsh : shift (lie E a) 0 = lie E a := by
    refine LinearMap.ext fun X => ?_
    rw [shift_apply, zero_mul, zero_smul, add_zero]
  have hcas : P (casA 0 c e) := by
    unfold casA
    rw [hsh]
    refine hPs c _ _ ?_ hP1
    unfold cas
    refine Finset.sum_induction _ P hPa hP0 fun j _ => ?_
    have h := hPs 1 _ _ (hPsq (toL (e j).1)) (hPsq (toL (Complex.I • (e j).1)))
    rwa [Complex.ofReal_one, one_smul] at h
  exact hcas.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ExactLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.exactLim :
    UpperTheory.V.Cj.H.ExactLim := by
  intro E _ _ _ a ha U hU Ξ q β ω hβ dβ hω dω hl hex
  obtain ⟨c, hc⟩ := (perEx E a U Ξ q).1 β hβ dβ
  obtain ⟨cn, hcn, ht⟩ := perLim E a U Ξ q ω hω dω hl
  refine (perKer E a ha U hU Ξ q β c hβ hc).1
    (hCobLim _ _ _ _ (fun γ s => ⟨_, _, fun f => rfl⟩) q c cn (fun k => ?_) ht)
  have h1 := (perEx E a U Ξ q).2.2 β (ω k) c (cn k) 1 (-1) hc (hcn k)
  have h2 := (levLin E a U Ξ q).1 β (ω k) 1 (-1) hβ (hω k)
  have e1 : (1 : ℂ) • β + (-1 : ℂ) • ω k = β - ω k := by
    ext X
    simp [sub_eq_add_neg]
  have e2 : (1 : ℂ) • c + (-1 : ℂ) • cn k = c - cn k := by
    rw [one_smul, neg_smul, one_smul, sub_eq_add_neg]
  rw [e1] at h1 h2
  rw [e2] at h1
  exact (perKer E a ha U hU Ξ q _ _ h2 h1).2 (hex k)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LevOfMulChi
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem open_fix {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_one_comm (X : Lie E a) (φ : Sm E a) :
    lie E a (oneL E a) (lie E a X φ) = lie E a X (lie E a (oneL E a) φ) := by
  have h := lie_comm (oneL E a) X
  have e : Matrix.of (oneL E a) * Matrix.of X = Matrix.of X * Matrix.of (oneL E a) :=
    (one_mul (Matrix.of X)).trans (mul_one (Matrix.of X)).symm
  rw [e, sub_self, sub_eq_zero] at h
  exact LinearMap.congr_fun h φ

private theorem lev_of_mulChi (χ : HChar E) (φ : Sm E a) (h : HasLev (mulChi a χ φ)) : HasLev φ := by
  have hl : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := h
  change IsOpen {k | finRep E a k φ = φ}
  refine open_fix (finRep E a) _ (hl.inter (isOpen_ker_chiDet (a := a) χ)) ⟨by simp, by simp⟩ ?_
  rintro k ⟨h1, h2⟩
  have h1' : rt E a (finGL E a k) (mulChi a χ φ) = mulChi a χ φ := h1
  have h2' : chiDet a χ (finGL E a k) = 1 := h2
  rw [rt_mulChi, h2'] at h1'
  change rt E a (finGL E a k) φ = φ
  apply (mulChi a χ).injective
  simpa using h1'

end

theorem UpperTheory.V.Cj.H.twSq :
    UpperTheory.V.Cj.H.TwSq := by
  intro E _ _ _ a ha μ _ _ r χ hχ φ hφ
  obtain ⟨⟨s, hs⟩, hχ⟩ := hχ
  have hG := gardFacts E a ha μ
  have hlie : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ X, mulChi a χ (lie E a X ψ) ∈ gard μ := fun ψ hψ X => by
    have h1 := (hG _ hψ).2.2.2.1 X
    rw [hχ, map_add (f := _), map_smul] at h1
    simpa using (gard μ).sub_mem h1 ((gard μ).smul_mem ((r * ell E a X : ℝ) : ℂ) hψ)
  have hleft : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → ∀ γ g,
      (mulChi a χ ψ).1 (ratGL E a γ * g) = (mulChi a χ ψ).1 g := fun ψ hψ γ g =>
    (hG _ hψ).2.1.1 _ (CuspidalL2GL.ratGL_mem_latticeGL γ) g
  have key : ∀ ψ : Sm E a, mulChi a χ ψ ∈ gard μ → lie E a (oneL E a) ψ = -(r : ℂ) • ψ → IsSqIntMod ψ := fun ψ hψ hr => by
    have h0 : lie E a (oneL E a) (mulChi a χ ψ) = (0 : ℂ) • mulChi a χ ψ := by
      rw [hχ, hr, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, zero_smul, map_zero]
    have h1 : IsSqInt (mulChi a χ ψ).1 :=
      (CuspidalL2GL.memL2_iff_isSqInt (μ := μ) (ContAut.continuous_of_isOpen_stab E a _ (hG _ hψ).1) (hleft ψ hψ) fun t g => by
        rw [aInv E a _ 0 h0 t g, zero_mul, Complex.exp_zero, one_mul]).1 (hG _ hψ).2.1
    refine ⟨s, χ, hs, ?_⟩
    have e : (fun g => ((chiDet a χ g : ℂˣ) : ℂ) * ψ.1 g) = (mulChi a χ ψ).1 := funext fun g => by
      rw [mulChi_apply, mul_comm]
    rw [e]
    exact h1
  refine ⟨hlie φ hφ, fun hr => ⟨fun γ g => ?_, lev_of_mulChi χ φ (hG _ hφ).1, hr, fun l => ?_⟩⟩
  · have h := hleft φ hφ γ g
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul] at h
    exact mul_right_cancel₀ (Units.ne_zero _) h
  · have h : mulChi a χ ((l.map (lie E a)).prod φ) ∈ gard μ ∧
        lie E a (oneL E a) ((l.map (lie E a)).prod φ) = -(r : ℂ) • (l.map (lie E a)).prod φ := by
      induction l with
      | nil => exact ⟨hφ, hr⟩
      | cons X l ih =>
        rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
        exact ⟨hlie _ ih.1 X, by rw [lie_one_comm, ih.2, map_smul]⟩
    exact key _ h.1 h.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LiftCv
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.liftCv :
    UpperTheory.V.Cj.H.LiftCv := by
  intro E _ _ _ a ha μ _ _ T hT T' hL ψ φ F hψ hφ
  obtain ⟨c1, c2, -, c4⟩ := clFacts E a μ
  have hφg : φ ∈ gard μ := Submodule.subset_span ⟨ψ, F, hψ, hφ⟩
  obtain ⟨g1, g2⟩ := hL φ hφg
  let φ' : Sm E a := ⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩
  have hφ'g : φ' ∈ gard μ := Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩
  have hc : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
  have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
    (hc.comp continuous_inv).integrable_of_hasCompactSupport
      (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
  have e : cl μ (T' φ) = cl μ φ' := by
    rw [g2, c4 ψ φ F hψ hφ, c4 ψ φ' (T F) hψ rfl]
    exact ropComm _ _ μ T hT _ hint F
  have hd : (1 : ℂ) • T' φ + (-1 : ℂ) • φ' ∈ gard μ :=
    add_mem (Submodule.smul_mem _ _ g1) (Submodule.smul_mem _ _ hφ'g)
  obtain ⟨d1, d2, -⟩ := gardFacts E a ha μ _ hd
  have h0 := c2 _ d1 d2 (by
    rw [(c1 _ _ 1 (-1) (gardFacts E a ha μ _ g1).2.1 (gardFacts E a ha μ _ hφ'g).2.1).2, e]
    simp)
  have h1 : T' φ = φ' := by
    rw [one_smul, neg_one_smul, add_neg_eq_zero] at h0
    exact h0
  rw [h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.OpLift
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem lift_of_inj {M H : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]
    (N : Submodule ℂ M) (c : N →ₗ[ℂ] H) (hc : Function.Injective c) (T : H →ₗ[ℂ] H)
    (hT : ∀ v : N, ∃ w : N, c w = T (c v)) :
    ∃ T' : M →ₗ[ℂ] M, ∀ v : N, ∃ h : T' v ∈ N, c ⟨T' v, h⟩ = T (c v) := by
  let l : N →ₗ[ℂ] N := (LinearEquiv.ofInjective c hc).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v)
  have hl : ∀ v, c (l v) = T (c v) := fun v => by
    have := (LinearEquiv.ofInjective c hc).apply_symm_apply
      (LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v) v)
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (N.subtype ∘ₗ l)
  refine ⟨g, fun v => ?_⟩
  have e : g v = (l v : M) := LinearMap.congr_fun hg v
  refine ⟨e ▸ (l v).2, ?_⟩
  rw [← hl v]
  congr 1
  exact Subtype.ext e

theorem UpperTheory.V.Cj.H.opLift :
    UpperTheory.V.Cj.H.OpLift := by
  intro E _ _ _ a ha μ _ _ T hT
  have hG := gardFacts E a ha μ
  obtain ⟨hlin, hinj, -, hrop⟩ := clFacts E a μ
  have hadd : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ + ψ) = cl μ φ + cl μ ψ := fun φ hφ ψ hψ => by
    have := (hlin φ ψ 1 1 (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul] using this
  have hsm : ∀ (s : ℂ), ∀ φ ∈ gard μ, cl μ (s • φ) = s • cl μ φ := fun s φ hφ => by
    have := (hlin φ φ s 0 (hG φ hφ).2.1 (hG φ hφ).2.1).2
    simpa only [zero_smul, add_zero] using this
  let c : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun v => cl μ v.1
      map_add' := fun v w => hadd v.1 v.2 w.1 w.2
      map_smul' := fun s v => hsm s v.1 v.2 }
  have hc : Function.Injective c := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    exact Subtype.ext (hinj v.1 (hG v.1 v.2).1 (hG v.1 v.2).2.1 hv)
  have key : ∀ φ ∈ gard μ, ∃ φ' ∈ gard μ, cl μ φ' = T (cl μ φ) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, e⟩ := h
      have hcont : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
      have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
        (hcont.comp continuous_inv).integrable_of_hasCompactSupport
          (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
      refine ⟨⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩, Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩, ?_⟩
      rw [hrop ψ φ F hψ e, hrop ψ _ (T F) hψ rfl]
      exact (ropComm _ _ μ T hT _ hint F).symm
    | zero =>
      have h0 : cl μ (0 : Sm E a) = 0 := map_zero c
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨x', hx', ex⟩ := ihx
      obtain ⟨y', hy', ey⟩ := ihy
      exact ⟨x' + y', Submodule.add_mem _ hx' hy', by
        rw [hadd x' hx' y' hy', hadd x hx y hy, ex, ey, map_add (f := _)]⟩
    | smul s x hx ihx =>
      obtain ⟨x', hx', ex⟩ := ihx
      exact ⟨s • x', Submodule.smul_mem _ s hx', by
        rw [hsm s x' hx', hsm s x hx, ex, map_smul]⟩
  obtain ⟨T', h⟩ := lift_of_inj (gard μ) c hc T.toLinearMap fun v => by
    obtain ⟨w, hw, e⟩ := key v.1 v.2
    exact ⟨⟨w, hw⟩, e⟩
  refine ⟨T', fun φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := h ⟨φ, hφ⟩
  exact ⟨h1, h2⟩
end

