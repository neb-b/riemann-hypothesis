module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.ArtinHenselCompletionNoetherian
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0053
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.LogIntegrableOnOfLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter

noncomputable section

variable {n d : ℕ}

theorem lift_eval_comp_projHom (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    {x : Fin n → ℂ} (hx : x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet J) :
    (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq).comp
        (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom =
      MvPolynomial.eval (A.mulVec x) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback]
  · intro i
    simp [GroundTheory.Heights₂.Heights.ComplexSets.projHom, GroundTheory.Heights₂.Heights.ComplexSets.pullback,
      GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem fibre_finite {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : GroundTheory.Heights₂.Heights.ComplexSets.IsFiniteProjection J A) (y : Fin d → ℂ) :
    (GroundTheory.Heights₂.Heights.ComplexSets.fibre J A y).Finite := by
  classical
  have hint : ∀ j : Fin n, (GroundTheory.Heights₂.Heights.ComplexSets.projHom J A).toRingHom.IsIntegralElem
      (Ideal.Quotient.mk J (X j)) := fun j => hA.finite.to_isIntegral _
  choose p hpm hp using hint
  refine (Set.Finite.pi (t := fun j => {z : ℂ | ((p j).map (MvPolynomial.eval y)).IsRoot z})
    fun j => Polynomial.finite_setOfPred_isRoot ((hpm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxy⟩ j -
  have h := congrArg (Ideal.Quotient.lift J (MvPolynomial.eval x) fun q hq => hx q hq) (hp j)
  rw [Polynomial.hom_eval₂, lift_eval_comp_projHom J A hx, hxy, map_zero] at h
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using h

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAdicCompletionRegular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem AdicCompletionRegular.proof : AdicCompletionRegular.Statement := by
  intro R _ hR M hM hreg
  let B := AdicCompletion M R
  have hfg : M.FG := Ideal.fg_of_isNoetherianRing M
  have : IsLocalRing B := adicCompletion_isLocalRing_of_isMaximal M hfg
  have : IsNoetherianRing B := GroundTheory.Arith.Etale.isNoetherianRing_adicCompletion R M
  have hmax : (M.map (algebraMap R B)).IsMaximal := AdicCompletion.isMaximal_map_of_le M M le_rfl hfg
  have hmB : M.map (algebraMap R B) = maximalIdeal B := IsLocalRing.eq_maximalIdeal hmax
  have hc : (M.map (algebraMap R B)).comap (algebraMap R B) = M :=
    (hM.eq_of_le (Ideal.comap_ne_top _ hmax.ne_top) Ideal.le_comap_map).symm
  have hunit : ∀ s : M.primeCompl, IsUnit (algebraMap R B s) := by
    intro s
    by_contra h
    have hs : algebraMap R B s ∈ maximalIdeal B := h
    rw [← hmB] at hs
    have hs' := Ideal.mem_comap.mpr hs
    rw [hc] at hs'
    exact s.2 hs'
  let _ : Algebra (Localization.AtPrime M) B :=
    (IsLocalization.lift (M := M.primeCompl) (S := Localization.AtPrime M) hunit).toAlgebra
  have : IsScalarTower R (Localization.AtPrime M) B :=
    IsScalarTower.of_algebraMap_eq fun r => (IsLocalization.lift_eq hunit r).symm
  have : Module.Flat (Localization.AtPrime M) B :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime M) M.primeCompl B).mpr inferInstance
  have hmap : (maximalIdeal (Localization.AtPrime M)).map (algebraMap (Localization.AtPrime M) B) =
      maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hmB]
  have : IsLocalHom (algebraMap (Localization.AtPrime M) B) := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have h1 : algebraMap (Localization.AtPrime M) B a ∈ maximalIdeal B :=
      hmap ▸ Ideal.mem_map_of_mem _ (show a ∈ maximalIdeal (Localization.AtPrime M) from h)
    exact h1 ha
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.of_flat_of_map_maximalIdeal hmap

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

theorem tendsto_nhds_of_analyticAt_eq {σ τ : Type} [Fintype σ] [Fintype τ] {h : (σ → ℂ) → (τ → ℂ)} {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : Tendsto h (𝓝 a) (𝓝 b) := by
  rw [← hab]; exact hh.continuousAt.tendsto

def germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : holGerms b →+* holGerms a where
  toFun φ := ⟨(φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab), by
      obtain ⟨f, hf, hφ⟩ := φ.2
      exact ⟨f ∘ h, hf.comp_of_eq hh hab, by rw [← hφ]; rfl⟩⟩
  map_one' := rfl
  map_mul' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ * ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) *
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_mul, ← hf, ← hg]; rfl
  map_zero' := rfl
  map_add' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ + ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) +
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_add, ← hf, ← hg]; rfl

theorem germPull_coe {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) (φ : holGerms b) (f : (τ → ℂ) → ℂ)
    (hφ : (f : Germ (𝓝 b) ℂ) = φ) : ((germPull h hh hab φ : holGerms a) : Germ (𝓝 a) ℂ) = ↑(f ∘ h) := by
  show (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) = _
  rw [← hφ]; rfl

theorem germPull_germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h₁ : (σ → ℂ) → (τ → ℂ))
    (h₂ : (τ → ℂ) → (σ → ℂ)) {a : σ → ℂ} {b : τ → ℂ} (hh₁ : AnalyticAt ℂ h₁ a) (hab : h₁ a = b)
    (hh₂ : AnalyticAt ℂ h₂ b) (hba : h₂ b = a) (h₁₂ : ∀ y, h₁ (h₂ y) = y) (φ : holGerms b) :
    germPull h₂ hh₂ hba (germPull h₁ hh₁ hab φ) = φ := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 := germPull_coe h₁ hh₁ hab φ f hφ
  rw [germPull_coe h₂ hh₂ hba _ (f ∘ h₁) e1.symm, ← hφ]
  congr 1
  funext y
  simp [h₁₂]

def germAffineEquiv {σ τ : Type} [Fintype σ] [Fintype τ] (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) :
    holGerms c ≃+* holGerms (0 : σ → ℂ) :=
  have h1 : AnalyticAt ℂ (fun z : σ → ℂ => e z + c) 0 := (e.analyticAt 0).add analyticAt_const
  have h1e : (fun z : σ → ℂ => e z + c) 0 = c := by simp
  have h2 : AnalyticAt ℂ (fun y : τ → ℂ => e.symm (y - c)) c :=
    (e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have h2e : (fun y : τ → ℂ => e.symm (y - c)) c = 0 := by simp
  RingEquiv.ofRingHom (germPull _ h1 h1e) (germPull _ h2 h2e)
    (RingHom.ext fun φ => germPull_germPull _ _ h2 h2e h1 h1e (fun z => by simp) φ)
    (RingHom.ext fun φ => germPull_germPull _ _ h1 h1e h2 h2e (fun y => by simp) φ)

theorem isNoetherianRing_holGerms_transfer {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) (h : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms c) :=
  isNoetherianRing_of_ringEquiv _ (germAffineEquiv e c).symm

theorem isField_holGerms_fin_zero : IsField (holGerms (0 : Fin 0 → ℂ)) := by
  refine ⟨⟨0, 1, fun h => ?_⟩, mul_comm, fun {φ} hφ => ?_⟩
  · exact one_ne_zero (congrArg Subtype.val h).symm
  · obtain ⟨f, hf, hfφ⟩ := φ.2
    have hall : ∀ x : Fin 0 → ℂ, f x = f 0 := fun x => by rw [Subsingleton.elim x 0]
    have h0 : f 0 ≠ 0 := by
      intro h0
      apply hφ
      apply Subtype.ext
      rw [← hfφ]
      exact Germ.coe_eq.2 (Eventually.of_forall fun x => by rw [hall x, h0])
    refine ⟨⟨↑(fun x => (f x)⁻¹), fun x => (f x)⁻¹, hf.inv h0, rfl⟩, ?_⟩
    apply Subtype.ext
    change (φ : Germ (𝓝 (0 : Fin 0 → ℂ)) ℂ) * ↑(fun x => (f x)⁻¹) = 1
    rw [← hfφ]
    exact Germ.coe_eq.2 (Eventually.of_forall fun x => by
      show f x * (f x)⁻¹ = 1
      rw [hall x]
      exact mul_inv_cancel₀ h0)

theorem isNoetherianRing_holGerms_option (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) (σ : Type) [Fintype σ]
    (hR : IsNoetherianRing (holGerms (0 : σ → ℂ))) :
    IsNoetherianRing (holGerms (0 : Option σ → ℂ)) := by
  classical
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · rw [hI]; exact Submodule.fg_bot
  obtain ⟨φ, hφI, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := by
    intro h
    apply hφ0
    apply Subtype.ext
    rw [← hfφ]
    exact Germ.coe_eq.2 h
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz

  let Pl : (Option σ → ℂ) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) (some i)).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let Tl : (Option σ → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp
      (A.symm : (Option σ → ℂ) →L[ℂ] (Option σ → ℂ))
  let ι : holGerms (0 : σ → ℂ) →+* holGerms (0 : Option σ → ℂ) := germPull Pl (Pl.analyticAt 0) (map_zero Pl)
  let τ : holGerms (0 : Option σ → ℂ) := ⟨↑(Tl : (Option σ → ℂ) → ℂ), Tl, Tl.analyticAt 0, rfl⟩
  let Φ : (Fin d → holGerms (0 : σ → ℂ)) → holGerms (0 : Option σ → ℂ) :=
    fun a => ∑ j : Fin d, ι (a j) * τ ^ (j : ℕ)
  have Φ_add : ∀ a b, Φ (a + b) = Φ a + Φ b := fun a b => by
    simp only [Φ, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have Φ_smul : ∀ (r : holGerms (0 : σ → ℂ)) a, Φ (r • a) = ι r * Φ a := fun r a => by
    simp only [Φ, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, Finset.mul_sum]
  have Φ_zero : Φ 0 = 0 := by simp [Φ]
  let N : Submodule (holGerms (0 : σ → ℂ)) (Fin d → holGerms (0 : σ → ℂ)) :=
    { carrier := {a | Φ a ∈ I}
      add_mem' := fun {a b} ha hb => by
        change Φ (a + b) ∈ I
        rw [Φ_add]; exact I.add_mem ha hb
      zero_mem' := by
        change Φ 0 ∈ I
        rw [Φ_zero]; exact I.zero_mem
      smul_mem' := fun r a ha => by
        change Φ (r • a) ∈ I
        rw [Φ_smul]; exact Ideal.mul_mem_left I _ ha }
  obtain ⟨s, hs⟩ : N.FG := IsNoetherian.noetherian N
  refine ⟨insert φ (s.image Φ), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro ψ hψ
    rw [Finset.coe_insert, Set.mem_insert_iff] at hψ
    rcases hψ with rfl | hψ
    · exact hφI
    · rw [Finset.coe_image] at hψ
      obtain ⟨a, ha, rfl⟩ := hψ
      have : a ∈ N := hs ▸ Submodule.subset_span ha
      exact this
  · intro ψ hψ
    obtain ⟨g, hg, hgψ⟩ := ψ.2
    have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)
    have hgA : AnalyticAt ℂ (g ∘ A) 0 := hg.comp_of_eq (A.analyticAt 0) (map_zero A)
    obtain ⟨q, a, hq, ha, hev⟩ := hD σ d (f ∘ A) (g ∘ A) hfA hgA hAd
    have hqB : AnalyticAt ℂ (q ∘ A.symm) 0 := hq.comp_of_eq (A.symm.analyticAt 0) (map_zero _)
    let Q : holGerms (0 : Option σ → ℂ) := ⟨↑(q ∘ A.symm), q ∘ A.symm, hqB, rfl⟩
    let a' : Fin d → holGerms (0 : σ → ℂ) := fun j => ⟨↑(a j), a j, ha j, rfl⟩
    have hev' : ∀ᶠ y in 𝓝 (0 : Option σ → ℂ),
        g y = q (A.symm y) * f y + ∑ j : Fin d, a j (Pl y) * Tl y ^ (j : ℕ) := by
      have hB : Tendsto A.symm (𝓝 0) (𝓝 0) := by
        simpa using A.symm.continuous.tendsto (0 : Option σ → ℂ)
      filter_upwards [hB.eventually hev] with y hy
      simpa [Pl, Tl] using hy
    have key : ψ = Q * φ + Φ a' := by
      apply Subtype.ext
      have hι : ∀ j, ((ι (a' j) : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) =
          ↑(a j ∘ Pl) := fun j => germPull_coe _ _ _ (a' j) (a j) rfl
      simp only [Φ, Subring.coe_add, Subring.coe_mul, ← hfφ, ← hgψ]
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [Subring.coe_mul, Subring.coe_pow, hι]
      change (↑g : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = Germ.coeRingHom _ (q ∘ A.symm) * Germ.coeRingHom _ f +
        ∑ j : Fin d, Germ.coeRingHom _ (a j ∘ Pl) * Germ.coeRingHom _ (Tl : (Option σ → ℂ) → ℂ) ^ (j : ℕ)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_mul, ← map_pow, ← map_sum, ← map_add (f := _)]
      refine Germ.coe_eq.2 ?_
      filter_upwards [hev'] with y hy
      simp [hy, Finset.sum_apply]
    have hΦ : Φ a' ∈ I := by
      have : Φ a' = ψ - Q * φ := by rw [key]; ring
      rw [this]; exact I.sub_mem hψ (Ideal.mul_mem_left I _ hφI)
    have ha'N : a' ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))) := by
      rw [hs]; exact hΦ
    have hgen : ∀ x ∈ Submodule.span (holGerms (0 : σ → ℂ)) (s : Set (Fin d → holGerms (0 : σ → ℂ))),
        Φ x ∈ Ideal.span (↑(insert φ (s.image Φ)) : Set (holGerms (0 : Option σ → ℂ))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Ideal.subset_span (by
          rw [Finset.coe_insert, Finset.coe_image]
          exact Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩)
      | zero => rw [Φ_zero]; exact Ideal.zero_mem _
      | add x y _ _ hx hy => rw [Φ_add]; exact Ideal.add_mem _ hx hy
      | smul r x _ hx => rw [Φ_smul]; exact Ideal.mul_mem_left _ _ hx
    have hspan := hgen a' ha'N
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) hspan

theorem AnalyticGermsNoetherian.proof (hD : WeierstrassDivision.Statement)
    (hG : GeneralLinearCoordinates.Statement) : AnalyticGermsNoetherian.Statement := by
  have hfin : ∀ n : ℕ, IsNoetherianRing (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := (isField_holGerms_fin_zero).toField
      infer_instance
    | succ n ih =>
      have h := isNoetherianRing_holGerms_option hD hG (Fin n) ih
      exact isNoetherianRing_holGerms_transfer
        (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv 0 h
  intro σ _ w
  exact isNoetherianRing_holGerms_transfer
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w (hfin _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticRootBranch
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

theorem AnalyticRootBranch.proof : AnalyticRootBranch.Statement := by
  intro d N a t₀ τ₀ ha hsep hroot
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (t₀, τ₀) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ 1 F (t₀, τ₀) := hFa.contDiffAt

  have hpe : ∀ s, p.eval s = F (t₀, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (t₀, s))
        (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ₀
        ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))
    have h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ₀).hasFDerivAt

  have hder : p.derivative.eval τ₀ ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀)
      (by rw [Polynomial.eval₂_id, hpe]; exact hroot)
    rwa [Polynomial.eval₂_id] at h
  have hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψt : ψ t₀ = τ₀ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψcd : ContDiffAt ℂ 1 ψ t₀ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := eventually_nhds_iff.mp
    ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))
  refine ⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩
  refine RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_
  exact ((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartIntSumOffHyperplane
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ChartIntSumOffHyperplane.proof (hFB : FibreBound.Statement)
    (hCN : ChartChangeSheetNull.Statement) : ChartIntSumOffHyperplane.Statement := by
  intro n d J A u m f F φ hJ hdim hA hu hf hint

  have hnull := hCN n d J J A A u u Set.univ Set.univ id id hJ hdim hJ hdim hu hu hA hA isOpen_univ
    isOpen_univ (Set.subset_univ _) (Set.subset_univ _) differentiableOn_id differentiableOn_id
    (fun x hx => hx) (fun x hx => hx) (fun x _ => rfl) (fun x _ => rfl)
  have hae : ∀ᵐ y ∂(volume : Measure (Fin d → ℂ)),
      chartDens J A f φ y = ∑ b, chartDens J A (F b) φ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    have hfin : (fibre J A y).Finite := (hFB n d J A hJ hdim hA y).2.1
    simp only [chartDens, sheetSum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · have hux : linEval u x ≠ 0 := by
        by_contra h0
        exact hy ⟨x, ⟨hx.1, hs, fun h => h.1 h0⟩, hx.2⟩
      rw [hf x hx.1 hux, Finset.sum_mul]
    · simp
  calc chartInt J A f φ = ∫ y, ∑ b, chartDens J A (F b) φ y := integral_congr_ae hae
    _ = ∑ b, chartInt J A (F b) φ := integral_finsetSum _ fun b _ => hint b

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConePolar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology

noncomputable section

theorem anForm_maDens_eq_geo_maDensity {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z :=
  rfl

theorem maDens_log_dualNorm_sheet {n e : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) (A : Matrix (Fin e) (Fin n) ℂ) (y : Fin e → ℂ) (x : Fin n → ℂ)
    (s : (Fin e → ℂ) → Fin n → ℂ) (hx : x ∈ fibre (J ⊔ Ideal.span {linForm ℓ - 1}) A y)
    (hs : IsSheetAt (J ⊔ Ideal.span {linForm ℓ - 1}) A x s) :
    ReciprocityTheory.AnForm.maDens (fun k => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) y =
      (e.factorial : ℝ) / Real.pi ^ e * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y /
        h.dualNorm x ^ (2 * (e + 1)) := by
  obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := hs
  obtain ⟨hxZ, rfl⟩ := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h1 : eval (0 : Fin n → ℂ) (linForm ℓ - 1) = 0 :=
      hxZ _ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_one, linForm, map_sum] at h1
    simp at h1
  have hdual : ∀ z, h.dualNorm z = ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ z)‖ := fun z => by
    simp [HermNorm.dualNorm, EuclideanSpace.norm_eq]
  have hv : ∀ᶠ y' in 𝓝 (A *ᵥ x), DifferentiableAt ℂ (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y' := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have hs' := (hdiff y' hy').differentiableAt (hU.mem_nhds hy')
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin (h.matᵀ)⁻¹)).differentiableAt.comp y' hs'
  have hne : (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') (A *ᵥ x) ≠ 0 := by
    intro h0
    have hpos := HermNorm.dualNorm_pos h hx0
    rw [hdual, ← hsx, show (h.matᵀ)⁻¹ *ᵥ s (A *ᵥ x) = 0 from h0] at hpos
    simp at hpos
  have key := ChartGramMA.proof e n _ _ hv hne
  have hF : (fun k : Fin e => (fun (_ : Fin e) x => Real.log (h.dualNorm x)) k ∘ s) =
      fun _ y' => Real.log ‖WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y')‖ := by
    funext k y'
    simp only [Function.comp_apply, hdual]
  rw [hF, anForm_maDens_eq_geo_maDensity, key, hsx, ← hdual]

end

end GroundTheory.Heights₂.Heights
end

