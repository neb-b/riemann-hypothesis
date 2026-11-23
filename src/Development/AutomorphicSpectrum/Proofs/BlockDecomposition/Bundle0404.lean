module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionCongrEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCongr

variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def mapFun (H : Subgroup G) {σ : Representation ℂ H W} {σ' : Representation ℂ H W'}
    (L : W ≃ₗ[ℂ] W') (hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w))
    (f : cIndSpace H σ) : cIndSpace H σ' :=
  have hind : (fun g => L (f.1.1.1 g)) ∈ indSpace H σ' := by
    intro h g
    have e : f.1.1.1 ((h : G) * g) = σ h (f.1.1.1 g) := f.1.1.2 h g
    show L (f.1.1.1 ((h : G) * g)) = σ' h (L (f.1.1.1 g))
    rw [e, hL]
  have hsm : (⟨fun g => L (f.1.1.1 g), hind⟩ : indSpace H σ') ∈ smoothPart (ind H σ') := by
    obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ f
    refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H σ') K hK _ fun x hx => ?_
    apply Subtype.ext
    funext g
    show L (f.1.1.1 (g * x)) = L (f.1.1.1 g)
    rw [hKi g x hx]
  have hc : (⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩ : smoothPart (ind H σ')) ∈ cIndSpace H σ' := by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show L (f.1.1.1 g) = 0
    rw [h0, map_zero]
  ⟨⟨⟨fun g => L (f.1.1.1 g), hind⟩, hsm⟩, hc⟩

theorem ext_fun {H : Subgroup G} {σ : Representation ℂ H W} {f f' : cIndSpace H σ}
    (h : ∀ g, f.1.1.1 g = f'.1.1.1 g) : f = f' :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem nonempty_equiv_cInd :
    ∀ {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (H : Subgroup G) (σ : Representation ℂ H W) (σ' : Representation ℂ H W'),
    σ.Equiv σ' → Nonempty ((cInd H σ).Equiv (cInd H σ')) := by
  intro G W W' _ _ _ _ _ _ _ H σ σ' e
  let L : W ≃ₗ[ℂ] W' := e.toLinearEquiv
  have hL : ∀ (h : H) (w : W), L (σ h w) = σ' h (L w) := fun h w =>
    LinearMap.congr_fun (e.isIntertwining' h) w
  have hL' : ∀ (h : H) (w : W'), L.symm (σ' h w) = σ h (L.symm w) := fun h w => by
    apply L.injective
    rw [L.apply_symm_apply, hL, L.apply_symm_apply]
  let T : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H σ' :=
    { toFun := mapFun H L hL
      map_add' := fun f f' => ext_fun fun g => map_add L (f.1.1.1 g) (f'.1.1.1 g)
      map_smul' := fun c f => ext_fun fun g => map_smul L c (f.1.1.1 g)
      invFun := mapFun H L.symm hL'
      left_inv := fun f => ext_fun fun g => L.symm_apply_apply (f.1.1.1 g)
      right_inv := fun f => ext_fun fun g => L.apply_symm_apply (f.1.1.1 g) }
  refine ⟨Representation.Equiv.mk T fun x => LinearMap.ext fun f => ext_fun fun g => ?_⟩
  rfl

end GlobalTheory.CompanionTheory.CIndCongr

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistEquiv
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwCInd

section SlopeTestRemainingChoices

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cIndSpace_ext {H : Subgroup G} {τ : Representation ℂ H W} {a b : cIndSpace H τ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem mul_mem_indSpace {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (fun g => ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g) ∈ indSpace H τ' := by
  intro h g
  have e : f.1.1.1 ((h : G) * g) = τ h (f.1.1.1 g) := f.1.1.2 h g
  beta_reduce
  rw [e, map_smul, hτ, map_mul, Units.val_mul, mul_smul, smul_comm]

theorem mul_mem_smoothPart {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    (⟨_, mul_mem_indSpace hτ f⟩ : indSpace H τ') ∈ smoothPart (ind H τ') := by
  obtain ⟨L, hL, hLi⟩ := cInd_right_inv H τ f
  refine GlobalTheory.CompanionTheory.BZMirOnto.isOpen_fixed_of_subgroup (ind H τ') (K ⊓ L) (hK.inter hL) _
    fun x hx => ?_
  apply Subtype.ext
  funext g
  show ((ψ (g * x) : ℂˣ) : ℂ) • f.1.1.1 (g * x) = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g
  rw [hLi g x hx.2, map_mul, hψ x hx.1, mul_one]

def mulC {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) :
    cIndSpace H τ' :=
  ⟨⟨⟨_, mul_mem_indSpace hτ f⟩, mul_mem_smoothPart hK hψ hτ f⟩, by
    obtain ⟨C, hC, hf⟩ := f.2
    refine ⟨C, hC, fun g hg => hf g fun h0 => hg ?_⟩
    show ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g = 0
    rw [show f.1.1.1 g = 0 from h0, smul_zero]⟩

theorem mulC_apply {H : Subgroup G} {τ τ' : Representation ℂ H W} {ψ : G →* ℂˣ}
    {K : Subgroup G} (hK : IsOpen (K : Set G)) (hψ : ∀ x ∈ K, ψ x = 1)
    (hτ : ∀ (h : H) (w : W), τ' h w = ((ψ h : ℂˣ) : ℂ) • τ h w) (f : cIndSpace H τ) (g : G) :
    (mulC hK hψ hτ f).1.1.1 g = ((ψ g : ℂˣ) : ℂ) • f.1.1.1 g := rfl

end SlopeTestRemainingChoices

theorem nonempty_twist_cInd_equiv : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (σ : Representation ℂ H W) (χ : G →* ℂˣ), IsOpen (χ.ker : Set G) →
    Nonempty ((twist (cInd H σ) χ).Equiv (cInd H (twist σ (χ.comp H.subtype)))) := by
  intro G W _ _ _ _ _ H σ χ hχ
  have h1 : ∀ x ∈ χ.ker, χ x = 1 := fun x hx => hx
  have h2 : ∀ x ∈ χ.ker, χ⁻¹ x = 1 := fun x hx => by
    rw [MonoidHom.inv_apply, show χ x = 1 from hx, inv_one]
  have t1 : ∀ (h : H) (w : W), twist σ (χ.comp H.subtype) h w = ((χ h : ℂˣ) : ℂ) • σ h w :=
    fun _ _ => rfl
  have t2 : ∀ (h : H) (w : W), σ h w =
      (((χ⁻¹) h : ℂˣ) : ℂ) • twist σ (χ.comp H.subtype) h w := fun h w => by
    rw [t1, smul_smul, ← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one,
      one_smul]
  have cancel : ∀ g, (((χ⁻¹) g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [← Units.val_mul, MonoidHom.inv_apply, inv_mul_cancel, Units.val_one]
  have cancel' : ∀ g, ((χ g : ℂˣ) : ℂ) * (((χ⁻¹) g : ℂˣ) : ℂ) = 1 := fun g => by
    rw [mul_comm, cancel]
  let e : cIndSpace H σ ≃ₗ[ℂ] cIndSpace H (twist σ (χ.comp H.subtype)) :=
    { toFun := mulC hχ h1 t1
      map_add' := fun a b => cIndSpace_ext fun g => smul_add _ (a.1.1.1 g) (b.1.1.1 g)
      map_smul' := fun c a => cIndSpace_ext fun g => smul_comm _ c (a.1.1.1 g)
      invFun := mulC hχ h2 t2
      left_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel, one_smul]
      right_inv := fun a => cIndSpace_ext fun g => by
        rw [mulC_apply, mulC_apply, smul_smul, cancel', one_smul] }
  refine ⟨Representation.Equiv.mk e fun y => LinearMap.ext fun f => cIndSpace_ext fun g => ?_⟩
  show ((χ g : ℂˣ) : ℂ) • (((χ y : ℂˣ) : ℂ) • f.1.1.1 (g * y)) =
    ((χ (g * y) : ℂˣ) : ℂ) • f.1.1.1 (g * y)
  rw [smul_smul, map_mul, Units.val_mul]

end GlobalTheory.CompanionTheory.TwCInd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralZeroVarsLtTop
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelCone

theorem cone_integral_zero_vars_lt_top :
    ∀ (F : Type) [Field F] [NumberField F] (n d : ℕ) (c : ℝ),
      ∫⁻ t in GlobalTheory.SiegelSet.cone 0 c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
        ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n d c
  have h : ∀ t : Fin 0 → ℝ, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) = 1 := by
    intro t
    simp [GlobalTheory.SiegelSet.modulus]
  simp_rw [h]
  rw [setLIntegral_const, one_mul]
  exact measure_lt_top _ _

end GlobalTheory.CompanionTheory.SiegelCone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugationInvariantValuationField
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.FieldVal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem injective_of_isField {K L : Type} [CommRing K] [Ring L] [Nontrivial L] (hK : IsField K)
    (f : K →+* L) : Function.Injective f := by
  refine (injective_iff_map_eq_zero f).2 fun y hy => ?_
  by_contra hne
  obtain ⟨z, hz⟩ := hK.mul_inv_cancel hne
  have : f (y * z) = 1 := by rw [hz, map_one]
  rw [map_mul, hy, zero_mul] at this
  exact zero_ne_one this

theorem absBar_finEmb_eq (hK : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  have h1 := minpoly.algHom_eq (finEmb F v τ) (injective_of_isField hK (finEmb F v τ).toRingHom) y
  have h2 := minpoly.algHom_eq (finEmb F v τ') (injective_of_isField hK (finEmb F v τ').toRingHom) y
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  unfold spectralNorm
  rw [h1, h2]

theorem absFin_eq (hK : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absFin F v y = absBar F v (finEmb F v τ y) := by
  refine le_antisymm ((absFin_le_iff F v).2 fun τ' => (absBar_finEmb_eq v hK τ' τ y).le) (le_absFin F v τ y)

theorem finEmb_sigR (σ : E →ₐ[F] E) (τ : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    finEmb F v τ (sigR (Fv F v) σ y) = finEmb F v (τ.comp σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem exists_valuation : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsField (Fv F v ⊗[F] E) →
    ∃ W : Valuation (Fv F v ⊗[F] E) ℝ≥0, (∀ a, W a = absFin F v a) ∧ ∀ a, W (sigR (Fv F v) σ a) = W a := by
  intro F E _ _ _ _ _ σ _ v hK
  let τ₀ : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(valBar F v).comap (finEmb F v τ₀).toRingHom, fun a => ?_, fun a => ?_⟩
  · exact (absFin_eq v hK τ₀ a).symm
  · change absBar F v (finEmb F v τ₀ (sigR (Fv F v) σ a)) = absBar F v (finEmb F v τ₀ a)
    rw [finEmb_sigR]
    exact absBar_finEmb_eq v hK _ _ a

end GlobalTheory.CompanionTheory.KFin.FieldVal

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLocallyConstant
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped Pointwise

namespace GlobalTheory.CompanionTheory.GL3BlockMatrixLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blk_zero_eq {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    blk h w m 0 = CtLevel.dgM h w m := by
  ext1
  rw [CtLevel.blk_val, CtLevel.dgM_val, CtLevel.dgMat, Matrix.mul_zero]

theorem continuous_dgM {a b n : ℕ} (h : a + b = n) (w : Pl E) :
    Continuous (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) := by
  have e : (CtLevel.dgM h w : GLw a w × GLw b w → GLw n w) = fun k =>
      ((CtLevel.dgM h w).comp (MonoidHom.inl (GLw a w) (GLw b w))) k.1 *
        ((CtLevel.dgM h w).comp (MonoidHom.inr (GLw a w) (GLw b w))) k.2 := by
    funext k
    simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, ← map_mul]
    simp
  rw [e]
  exact ((CtLevel.continuous_dgM_inl h w).comp continuous_fst).mul
    ((CtLevel.continuous_dgM_inr h w).comp continuous_snd)

theorem dgM_entries {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w) :
    (∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = k.1.val i j) ∧
      ∀ i j, (CtLevel.dgM h w k).val (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = k.2.val i j := by
  constructor <;> intro i j <;>
    rw [CtLevel.dgM_val, CtLevel.dgMat, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      Equiv.symm_apply_apply] <;> simp

theorem blocks_mem_KGL {a b n : ℕ} (h : a + b = n) (w : Pl E) (k : GLw a w × GLw b w)
    (hk : CtLevel.dgM h w k ∈ GlobalTheory.LFun.KGL w (n := n)) : k.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ k.2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.AdelicU.mem_GLint_iff.1 hk
  rw [← map_inv] at h2
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h1 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k).1] at this
  · have := h2 (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j))
    rwa [(dgM_entries h w k⁻¹).1] at this
  · have := h1 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k).2] at this
  · have := h2 (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j))
    rwa [(dgM_entries h w k⁻¹).2] at this

theorem constant_term_bi_invariant {a b n : ℕ} (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w))
    (hKK : K' ≤ GlobalTheory.LFun.KGL w (n := n)) (hN : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K')
    (f : GLw n w → ℂ) (hf : ∀ k₁ ∈ K', ∀ k₂ ∈ K', ∀ g, f (k₁ * g * k₂) = f g)
    (x y : GLw n w) (hx : x ∈ GlobalTheory.LFun.KGL w (n := n)) (hy : y ∈ GlobalTheory.LFun.KGL w (n := n))
    (k₁ k₂ : GLw a w × GLw b w) (hk₁ : k₁ ∈ leviOf h w K') (hk₂ : k₂ ∈ leviOf h w K')
    (m : GLw a w × GLw b w) : phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  have hd₁ : CtLevel.dgM h w k₁ ∈ K' := by
    have : blk h w k₁ 0 ∈ K' := hk₁
    rwa [blk_zero_eq] at this
  have hd₂ : CtLevel.dgM h w k₂ ∈ K' := by
    have : blk h w k₂ 0 ∈ K' := hk₂
    rwa [blk_zero_eq] at this
  obtain ⟨h11, h12⟩ := blocks_mem_KGL h w k₁ (hKK hd₁)
  obtain ⟨h21, h22⟩ := blocks_mem_KGL h w k₂ (hKK hd₂)
  have hab : absHalf w ((k₁ * m * k₂).1.val.det ^ b / (k₁ * m * k₂).2.val.det ^ a) =
      absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
    rw [(absHalf_blockDet_KGL_invariant E a b w (k₁ * m) k₂ h21 h22).2]
    exact (absHalf_blockDet_KGL_invariant E a b w m k₁ h11 h12).1
  have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
      f (x⁻¹ * blk h w (k₁ * m * k₂) (Multiplicative.toAdd X) * y)) =
      fun X => (fun Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
        (Multiplicative.ofAdd (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val)) := by
    funext X
    rw [(CtLevel.blk_mul_dgM E a b n h w (k₁ * m) k₂ _).2, (CtLevel.blk_mul_dgM E a b n h w m k₁ _).1]
    have hc₁ : x⁻¹ * CtLevel.dgM h w k₁ * x ∈ K' := by
      simpa using hN x⁻¹ (inv_mem hx) _ hd₁
    have hc₂ : y⁻¹ * CtLevel.dgM h w k₂ * y ∈ K' := by
      simpa using hN y⁻¹ (inv_mem hy) _ hd₂
    have e2 : x⁻¹ * (CtLevel.dgM h w k₁ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) *
        CtLevel.dgM h w k₂) * y =
        (x⁻¹ * CtLevel.dgM h w k₁ * x) *
          (x⁻¹ * blk h w m (k₂.1.val * Multiplicative.toAdd X * (k₂.2⁻¹).val) * y) *
          (y⁻¹ * CtLevel.dgM h w k₂ * y) := by group
    rw [e2, hf _ hc₁ _ hc₂]
    rfl
  unfold phi3
  rw [hab, e, HintInv.hint_intMat_mul_mul E a b w (fun Y => f (x⁻¹ * blk h w m (Multiplicative.toAdd Y) * y))
    k₂.1 k₂.2⁻¹ h21 (inv_mem h22)]

theorem constant_term_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (x y : GLw n w)
    (m : GLw a w × GLw b w) (hm : phi3 h w f x y m ≠ 0) :
    ∃ X, blk h w m X ∈ ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} := by
  obtain ⟨X, hX⟩ := CtLevel.exists_ne_zero_of_hint_ne_zero _ _ (right_ne_zero_of_mul hm)
  refine ⟨Multiplicative.toAdd X, ?_⟩
  have e : blk h w m (Multiplicative.toAdd X) =
      x * (x⁻¹ * blk h w m (Multiplicative.toAdd X) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul rfl (subset_tsupport _ hX)) rfl

theorem constant_term_compact_support {a b n : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ)
    (hf : HasCompactSupport f) (x y : GLw n w) : HasCompactSupport (phi3 h w f x y) := by
  set C : Set (GLw n w) := ({x} : Set (GLw n w)) * tsupport f * {y⁻¹} with hCdef
  have hC : IsCompact C := (isCompact_singleton.mul hf).mul isCompact_singleton
  let ψ : GLw n w → ((Matrix (Fin a) (Fin a) (w.adicCompletion E) × (Matrix (Fin a) (Fin a) (w.adicCompletion E))ᵐᵒᵖ) ×
      (Matrix (Fin b) (Fin b) (w.adicCompletion E) × (Matrix (Fin b) (Fin b) (w.adicCompletion E))ᵐᵒᵖ)) :=
    fun g => ((CtLevel.blkTL h g.val, MulOpposite.op (CtLevel.blkTL h (g⁻¹).val)),
      (CtLevel.blkBR h g.val, MulOpposite.op (CtLevel.blkBR h (g⁻¹).val)))
  have hψ : Continuous ψ := by
    refine ((((CtLevel.continuous_blkTL h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkTL h).comp Units.continuous_coe_inv))).prodMk
      (((CtLevel.continuous_blkBR h).comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp ((CtLevel.continuous_blkBR h).comp Units.continuous_coe_inv))))
  let ι : GLw a w × GLw b w → _ := Prod.map (Units.embedProduct (Matrix (Fin a) (Fin a) (w.adicCompletion E)))
    (Units.embedProduct (Matrix (Fin b) (Fin b) (w.adicCompletion E)))
  have hι : Topology.IsClosedEmbedding ι :=
    Units.isClosedEmbedding_embedProduct.prodMap Units.isClosedEmbedding_embedProduct
  have hιψ : ∀ m X, ι m = ψ (blk h w m X) := by
    intro m X
    simp only [ι, ψ, Prod.map, Units.embedProduct_apply, CtLevel.blk_inv, CtLevel.blkTL_blk, CtLevel.blkBR_blk,
      Prod.fst_inv, Prod.snd_inv]
  have hT : IsCompact (ψ '' C) := hC.image hψ
  refine HasCompactSupport.intro' (hι.isCompact_preimage hT) (hT.isClosed.preimage hι.continuous) ?_
  intro m hm
  by_contra hne
  obtain ⟨X, hX⟩ := constant_term_support h w f x y m hne
  exact hm ⟨blk h w m X, hX, (hιψ m X).symm⟩

theorem constant_term_locally_constant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w (n := n) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w (n := n)) → (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f : GLw n w → ℂ, IsHk K' f → ∀ x ∈ X, ∀ y ∈ X, IsLocallyConstant (phi3 h w f x y) ∧ HasCompactSupport (phi3 h w f x y) ∧ ∀ k₁ ∈ leviOf h w K', ∀ k₂ ∈ leviOf h w K', ∀ m, phi3 h w f x y (k₁ * m * k₂) = phi3 h w f x y m := by
  intro E _ _ _ n a b h w K' hKo hKK hN X hXK _ f hf x hx y hy
  have hbi := constant_term_bi_invariant h w K' hKK hN f hf.2.2.2 x y (hXK x hx) (hXK y hy)
  refine ⟨?_, constant_term_compact_support h w f hf.2.2.1 x y, fun k₁ h₁ k₂ h₂ m => hbi k₁ k₂ h₁ h₂ m⟩
  have hL : IsOpen (leviOf h w K') := by
    have e : leviOf h w K' = (CtLevel.dgM h w) ⁻¹' (K' : Set (GLw n w)) := by
      ext m
      simp only [leviOf, Set.mem_setOf_eq, Set.mem_preimage, blk_zero_eq, SetLike.mem_coe]
    rw [e]
    exact hKo.preimage (continuous_dgM h w)
  have h1 : (1 : GLw a w × GLw b w) ∈ leviOf h w K' := by
    show blk h w 1 0 ∈ K'
    rw [blk_zero_eq, map_one]
    exact K'.one_mem
  rw [IsLocallyConstant.iff_exists_open]
  intro m
  refine ⟨(fun m' => m⁻¹ * m') ⁻¹' leviOf h w K', hL.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simpa using h1
  · intro m' hm'
    have := hbi 1 (m⁻¹ * m') h1 hm' m
    simpa [mul_assoc] using this

end GlobalTheory.CompanionTheory.GL3BlockMatrixLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProj
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Cont

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_entry (n : ℕ) (a b : Fin (n + 1)) :
    Continuous fun y : Fin n → k => colMat k n y a b := by
  unfold colMat
  split_ifs
  · induction a using Fin.lastCases with
    | last => simp only [Fin.lastCases_last]; exact continuous_const
    | cast i => simp only [Fin.lastCases_castSucc]; exact continuous_apply i
  · exact continuous_const

theorem continuous_uM_val (n : ℕ) : Continuous fun y : Fin n → k =>
    (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  have h : (fun y : Fin n → k =>
      (((uM k n y : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) =
      fun y => 1 + colMat k n y := by
    funext y
    rfl
  rw [h]
  refine continuous_const.add (continuous_matrix fun a b => ?_)
  exact continuous_colMat_entry k n a b

theorem uM_inv (n : ℕ) (y : Fin n → k) : (uM k n y)⁻¹ = uM k n (-y) := by
  have h : uM k n (-y) * uM k n y = 1 := by
    rw [← uM_add, neg_add_cancel, uM_zero]
  exact (eq_inv_of_mul_eq_one_left h).symm

theorem continuous_uM (n : ℕ) : Continuous (uM k n) := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨continuous_uM_val k n, ?_⟩
  have h : ∀ y : Fin n → k, ((uM k n y : GL (Fin (n + 1)) k))⁻¹ =
      (uM k n (-y) : GL (Fin (n + 1)) k) := by
    intro y
    rw [← uM_inv k n y, Subgroup.coe_inv]
  simp only [Function.comp_apply, h]
  exact (continuous_uM_val k n).comp continuous_neg

end GlobalTheory.CompanionTheory.BZPsiPG.Cont

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem continuous_levi_uM_mirProj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
  intro k _ _ _ _ n
  exact ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, Cont.continuous_uM k n,
    GlobalTheory.CompanionTheory.BZMirFun.continuous_mirProj k n⟩

end GlobalTheory.CompanionTheory.BZPsiPG
end

