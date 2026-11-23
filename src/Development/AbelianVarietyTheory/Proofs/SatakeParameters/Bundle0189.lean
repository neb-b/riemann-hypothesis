module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Formalism.LocalToGlobal.IndefiniteReal.CongNatCastEqOneTmul
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.EmbExt

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]

def scalarLift (φ : E →+* Om l) : ℚ_[l] ⊗[ℚ] E →ₐ[ℚ_[l]] Om l :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[l] (Om l)) φ.toRatAlgHom (fun _ _ => Commute.all _ _)

theorem scalarLift_tmul (φ : E →+* Om l) (a : ℚ_[l]) (y : E) :
    scalarLift φ (a ⊗ₜ y) = algebraMap ℚ_[l] (Om l) a * φ y := by
  simp [scalarLift]

theorem exists_near (φ ψ : E →+* Om l) (t : ℚ_[l] ⊗[ℚ] E) :
    ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖scalarLift φ t - φ x‖ < ε ∧ ‖scalarLift ψ t - ψ x‖ < ε := by
  induction t using TensorProduct.inductionOn with
  | tmul a y =>
    intro ε hε
    have hM : 0 < ‖φ y‖ + ‖ψ y‖ + 1 := by positivity
    obtain ⟨q, hq⟩ := Padic.rat_dense l a (div_pos hε hM)
    refine ⟨(q : E) * y, ?_, ?_⟩
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖φ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (ψ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
    · rw [scalarLift_tmul, map_mul, map_ratCast, ← map_ratCast (algebraMap ℚ_[l] (Om l)) q, ← sub_mul,
        ← map_sub, norm_mul, PadicAlgCl.norm_extends]
      calc ‖a - (q : ℚ_[l])‖ * ‖ψ y‖ ≤ ‖a - (q : ℚ_[l])‖ * (‖φ y‖ + ‖ψ y‖ + 1) := by
            gcongr; linarith [norm_nonneg (φ y)]
        _ < ε / (‖φ y‖ + ‖ψ y‖ + 1) * (‖φ y‖ + ‖ψ y‖ + 1) := by gcongr
        _ = ε := div_mul_cancel₀ _ hM.ne'
  | add t₁ t₂ h₁ h₂ =>
    intro ε hε
    obtain ⟨x₁, a₁, b₁⟩ := h₁ (ε / 2) (half_pos hε)
    obtain ⟨x₂, a₂, b₂⟩ := h₂ (ε / 2) (half_pos hε)
    refine ⟨x₁ + x₂, ?_, ?_⟩
    · have e : scalarLift φ (t₁ + t₂) - φ (x₁ + x₂) = (scalarLift φ t₁ - φ x₁) + (scalarLift φ t₂ - φ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift φ t₁ - φ x₁) (scalarLift φ t₂ - φ x₂)]
    · have e : scalarLift ψ (t₁ + t₂) - ψ (x₁ + x₂) = (scalarLift ψ t₁ - ψ x₁) + (scalarLift ψ t₂ - ψ x₂) := by
        rw [map_add (f := _), map_add (f := _)]; ring
      rw [e]; linarith [norm_add_le (scalarLift ψ t₁ - ψ x₁) (scalarLift ψ t₂ - ψ x₂)]

theorem norm_scalarLift_le (φ ψ : E →+* Om l) (h : ∀ x, ‖φ x‖ = ‖ψ x‖) (t : ℚ_[l] ⊗[ℚ] E) :
    ‖scalarLift ψ t‖ ≤ ‖scalarLift φ t‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨x, h₁, h₂⟩ := exists_near φ ψ t (ε / 2) (half_pos hε)
  have e1 : ‖scalarLift ψ t‖ ≤ ‖scalarLift ψ t - ψ x‖ + ‖ψ x‖ := by
    simpa using norm_add_le (scalarLift ψ t - ψ x) (ψ x)
  have e2 : ‖φ x‖ ≤ ‖φ x - scalarLift φ t‖ + ‖scalarLift φ t‖ := by
    simpa using norm_add_le (φ x - scalarLift φ t) (scalarLift φ t)
  rw [norm_sub_rev] at e2
  rw [← h x] at e1
  linarith

theorem norm_eq_of_same_place (τ φ : E →+* Om l) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∈ placesOver E l)
    (hτ : ∀ x : 𝓞 E, ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal) (hφ : ∀ x : 𝓞 E, ‖φ (x : E)‖ < 1 ↔ x ∈ w.asIdeal)
    (x : E) : ‖τ x‖ = ‖φ x‖ := by
  have e1 := PI.CompDegEF.isEquiv_adicAbv_normAbv τ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer τ x, hτ x⟩)
  have e2 := PI.CompDegEF.isEquiv_adicAbv_normAbv φ w hw
    (fun x => ⟨PI.CompDegEF.norm_le_one_of_integer φ x, hφ x⟩)
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 (e1.symm.trans e2)
  have hl := congrFun hce ((l : ℕ) : E)
  simp only [PI.CompDegEF.normAbv_apply, map_natCast] at hl
  have hpos := PI.CompDegEF.norm_natCast_pos l
  have hlt := PI.CompDegEF.norm_natCast_lt_one l
  have hL : Real.log ‖((l : ℕ) : Om l)‖ ≠ 0 := (Real.log_neg hpos hlt).ne
  have hc1 : c = 1 := by
    have := congrArg Real.log hl
    rw [Real.log_rpow hpos] at this
    exact (mul_eq_right₀ hL).1 this
  have hx := congrFun hce x
  simp only [PI.CompDegEF.normAbv_apply, hc1, Real.rpow_one] at hx
  exact hx

theorem main : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (w : PlE D.host) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw → ∀ τ : D.host.E →+* Qbar l, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → ∀ LL' : FinExt l, Bw.LL.1 ≤ LL'.1 → ∃ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1, GlobalTheory.Pst.IsInduced Bw τ τ' := by
  intro D l _ w O _ _ _ Bw hj τ hτ LL' hLL
  let jE : D.host.E →+* Om l := Bw.j.comp (algebraMap D.host.E D.nd.Om)
  have hA := D.nd.plOm.2 w
  have hw := hj.mem_placesOver hA
  have hjE : ∀ x : 𝓞 D.host.E, ‖jE (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := fun x =>
    (hj.valuation_lt_one_iff _).symm.trans (hA x)
  have iso := norm_eq_of_same_place τ jE w hw hτ hjE
  have hker : ∀ t ∈ RingHom.ker (scalarLift jE), scalarLift τ t = 0 := fun t ht =>
    norm_eq_zero.1 (le_antisymm ((norm_scalarLift_le jE τ (fun x => (iso x).symm) t).trans
      (by rw [RingHom.mem_ker.1 ht, norm_zero])) (norm_nonneg _))
  have hrange : (scalarLift jE).range ≤ Bw.Kw.1.toSubalgebra := by
    rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      change scalarLift jE (a ⊗ₜ y) ∈ _
      rw [scalarLift_tmul]
      exact mul_mem (Bw.Kw.1.algebraMap_mem a) (Bw.j_E y)
    | add t₁ t₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have hfin : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule (scalarLift jE).range) := by
    have : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule Bw.Kw.1.toSubalgebra) := Bw.Kw.2
    exact Submodule.finiteDimensional_of_le (Subalgebra.toSubmodule.monotone hrange)
  have hclosed : IsClosed ((scalarLift jE).range : Set (Om l)) :=
    Submodule.isClosed_of_finiteDimensional (Subalgebra.toSubmodule (scalarLift jE).range)
  have hle : Bw.Kw.1.toSubalgebra ≤ (scalarLift jE).range := by
    intro y hy
    refine closure_minimal ?_ hclosed (Bw.j_dense hy)
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, by change scalarLift jE (1 ⊗ₜ x) = jE x; rw [scalarLift_tmul, map_one, one_mul]⟩
  let σ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l :=
    ((Ideal.Quotient.liftₐ (RingHom.ker (scalarLift jE)) (scalarLift τ) hker).comp
      (Ideal.quotientKerEquivRange (scalarLift jE)).symm.toAlgHom).comp (Subalgebra.inclusion hle)
  refine ⟨σ.codRestrict LL'.1.toSubalgebra (fun y => hLL (Bw.LL_split σ y)), fun x => ?_⟩
  have key : (Ideal.quotientKerEquivRange (scalarLift jE)).symm
      (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩) = Ideal.Quotient.mk _ (1 ⊗ₜ x) := by
    rw [AlgEquiv.symm_apply_eq]
    apply Subtype.ext
    change jE x = scalarLift jE (1 ⊗ₜ x)
    rw [scalarLift_tmul, map_one, one_mul]
  change τ x = σ ⟨jE x, Bw.j_E x⟩
  change τ x = Ideal.Quotient.liftₐ _ (scalarLift τ) hker ((Ideal.quotientKerEquivRange (scalarLift jE)).symm
    (Subalgebra.inclusion hle ⟨jE x, Bw.j_E x⟩))
  rw [key, Ideal.Quotient.liftₐ_apply]
  change τ x = scalarLift τ (1 ⊗ₜ x)
  rw [scalarLift_tmul, map_one, one_mul]

end GlobalTheory.EmbExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupport
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.CuspidalSupportZero

theorem exists_isCuspSupport_zero (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (π : Irr k 0) :
    ∃ (s : ℕ) (d : Fin s → ℕ) (σ : ∀ a, Irr k (d a)), IsCuspSupport π.π d (fun a => (σ a).π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let d : Fin 0 → ℕ := fun a => a.elim0
  let σ : ∀ a, Irr k (d a) := fun a => a.elim0
  refine ⟨0, d, σ, π.irr, fun a => a.elim0, ?_⟩
  let e : (Σ a, Fin (d a)) ≃ Fin 0 := Equiv.equivOfIsEmpty _ _
  refine ⟨e, ?_⟩
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := k) e (fun a => (σ a).π)
  have hirr := π.irr

  obtain ⟨v₀, hv₀⟩ : ∃ v : π.V, v ≠ 0 := by
    by_contra h
    push_neg at h
    apply (bot_ne_top : (⊥ : Subrepresentation π.π) ≠ ⊤)
    ext v
    simp [h v]
  let L : Subrepresentation π.π := ⟨ℂ ∙ v₀, fun g v hv => by
    rw [Subsingleton.elim g 1, map_one]; exact hv⟩
  have hL : L = ⊤ := by
    rcases eq_bot_or_eq_top L with h | h
    · exfalso
      have : v₀ ∈ L.toSubmodule := Submodule.mem_span_singleton_self v₀
      rw [h] at this
      exact hv₀ ((Submodule.mem_bot ℂ).1 this)
    · exact h
  let f : (multiProd e fun a => (σ a).π).IntertwiningMap π.π :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π.V v₀) ∘ₗ φ.toLinearEquiv.toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]; rfl }
  refine IsSubquotient.of_surjective f fun v => ?_
  have hv : v ∈ L.toSubmodule := by rw [hL]; trivial
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  refine ⟨φ.toLinearEquiv.symm c, ?_⟩
  show (LinearMap.toSpanSingleton ℂ π.V v₀) (φ.toLinearEquiv (φ.toLinearEquiv.symm c)) = c • v₀
  erw [LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.CuspidalSupportZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeeperCongruenceConjIntoCongruence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjCong

theorem exists_cong_conj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (g : GAf L n), 0 < N → ∃ M : ℕ, 0 < M ∧ ∀ κ, NG.Cong L n (N * M) κ → NG.Cong L n N (g⁻¹ * κ * g) := by
  intro L _ _ _ n N g hN
  obtain ⟨M, hM, h⟩ := Formalism.IndefR.principalLevelFrame.congConj_holds L n g N hN
  exact ⟨M, hM, fun κ hκ => h κ (NG.Cong.of_mul_right L n hκ)⟩

end GlobalTheory.ConjCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEigenvector
section
namespace GlobalTheory.ExistsEigenvector

theorem exists_eigenvector {G V W ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [Fintype ι] {ρ : Representation ℂ G V}
    (hρ : GlobalTheory.PRep.IsSmooth ρ) {K : Subgroup G} (hK : IsCompact (K : Set G)) {U : Set G} (hU : IsOpen U)
    (h1 : (1 : G) ∈ U) (θ : G → ℂ) (hθ : ∀ g ∈ U, g ∈ K → θ g = 1)
    (hmul : ∀ a ∈ K, ∀ b ∈ K, θ (a * b) = θ a * θ b) (T : ι → V →ₗ[ℂ] W) (y : ι → V)
    (hne : ∑ i, T i (y i) ≠ 0) (heq : ∀ k ∈ K, ∑ i, T i (ρ k (y i)) = θ k • ∑ i, T i (y i)) :
    ∃ v : V, v ≠ 0 ∧ ∀ h ∈ K, ρ h v = θ h • v := by
  classical
  have hone : θ 1 = 1 := hθ 1 h1 K.one_mem
  have hθne : ∀ a ∈ K, θ a ≠ 0 := fun a ha h0 => by
    have := hmul a ha a⁻¹ (K.inv_mem ha)
    rw [mul_inv_cancel, hone, h0, zero_mul] at this
    exact one_ne_zero this
  let H : Subgroup K :=
    { carrier := {k | θ k = 1 ∧ ∀ i, ρ k (y i) = y i}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, fun i => ?_⟩
        · rw [Subgroup.coe_mul, hmul _ a.2 _ b.2, ha, hb, one_mul]
        · rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb', ha']
      one_mem' := ⟨hone, fun i => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨?_, fun i => ?_⟩
        · have := hmul _ a.2 _ (K.inv_mem a.2)
          rw [mul_inv_cancel, hone, ha, one_mul] at this
          exact this.symm
        · conv_lhs => rw [← ha' i]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
  have hHo : IsOpen (H : Set K) := by
    have ho : IsOpen ((fun k : K => (k : G)) ⁻¹' (U ∩ ⋂ i, {g : G | ρ g (y i) = y i})) :=
      (hU.inter (isOpen_iInter_of_finite fun i => hρ (y i))).preimage continuous_subtype_val
    refine H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨h1, by simp⟩) ?_)
    rintro k ⟨hk, hk'⟩
    exact ⟨hθ _ hk k.2, fun i => Set.mem_iInter.1 hk' i⟩
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  haveI : Finite (K ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _
  let f : K → ι → V := fun k i => (θ k)⁻¹ • ρ k (y i)
  have hf : ∀ a b : K, QuotientGroup.leftRel H a b → f a = f b := by
    intro a b hab
    obtain ⟨h, h'⟩ : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.1 hab
    have e : (b : G) = a * ((a⁻¹ * b : K) : G) := by simp
    funext i
    simp only [f]
    rw [e, hmul _ a.2 _ (a⁻¹ * b).2, h, mul_one, map_mul, Module.End.mul_apply, h']
  let F : K ⧸ H → ι → V := fun q => Quotient.liftOn' q f hf
  have hF : ∀ (h : K) (q : K ⧸ H) (i : ι), ρ h (F q i) = θ h • F (h • q) i := by
    intro h q i
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ρ h ((θ k)⁻¹ • ρ k (y i)) = θ h • ((θ (h * k))⁻¹ • ρ (h * k) (y i))
      rw [hmul _ h.2 _ k.2, map_mul, Module.End.mul_apply, map_smul, smul_smul, mul_inv,
        mul_inv_cancel_left₀ (hθne _ h.2)]
  have hT : ∀ q : K ⧸ H, ∑ i, T i (F q i) = ∑ i, T i (y i) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      change ∑ i, T i ((θ k)⁻¹ • ρ k (y i)) = _
      simp only [map_smul]
      rw [← Finset.smul_sum, heq _ k.2, smul_smul, inv_mul_cancel₀ (hθne _ k.2), one_smul]
  have hex : ∃ i, ∑ q, F q i ≠ 0 := by
    by_contra hc
    have hc' : ∀ i, ∑ q, F q i = 0 := fun i => not_not.1 fun h => hc ⟨i, h⟩
    have h0 : ∑ i, T i (∑ q, F q i) = 0 := by simp [hc']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum] at h0
    rw [Finset.sum_comm] at h0
    simp only [hT] at h0
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 h0)
    · exact hne h0
  obtain ⟨i, hi⟩ := hex
  refine ⟨_, hi, fun h hh => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl fun q _ => hF ⟨h, hh⟩ q i]
  exact Equiv.sum_comp (MulAction.toPerm (⟨h, hh⟩ : K)) (fun q : K ⧸ H => θ h • F q i)

end GlobalTheory.ExistsEigenvector
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsEmbeddingParIndOfJacquetNontrivial
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory

theorem injective_of_jacquet_surjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (π : Irr k n) {s : ℕ} {d : Fin s → ℕ}
    (e : (Σ a, Fin (d a)) ≃ Fin n) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) Y} (hirr : τ.IsIrreducible)
    (q : (jac e π.π).IntertwiningMap τ) (hq : Function.Surjective q) :
    ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := (Model.evalOne_bijective e π.smooth τ).2 q
  refine ⟨φ, (injective_iff_map_eq_zero _).2 fun v hv => ?_⟩
  have hK : φ.ker ≠ ⊤ := by
    intro hK
    haveI := Model.nontrivial_of_isIrreducible hirr
    obtain ⟨y, hy⟩ := exists_ne (0 : Y)
    obtain ⟨x, rfl⟩ := hq y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    apply hy
    have hw : φ w = 0 := (show w ∈ φ.ker from hK ▸ trivial)
    have h1 : q (Submodule.Quotient.mk w) = (φ w).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk w)) hφ).symm
    rw [h1, hw]
    rfl
  have hv' : v ∈ φ.ker := hv
  haveI := π.irr
  rw [(eq_bot_or_eq_top φ.ker).resolve_right hK] at hv'
  exact hv'

theorem exists_embedding_parInd_of_jacquet_nontrivial : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n) (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), ¬ Subsingleton (Jacquet π.π (unipRad k e)) → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (Levi k fun a => Fin (d a)) Y), τ.IsIrreducible ∧ IsSmooth τ ∧ IsSubquotient τ (jac e π.π) ∧ ∃ φ : π.π.IntertwiningMap (parInd e τ), Function.Injective φ := by
  intro hBZ k _ _ _ _ n π s d e hJ
  have hfl : HasFiniteLength (jac e π.π) :=
    (hBZ k).2.1 (Fin s) (Fin n) (fun a => Fin (d a)) e π.V π.π π.smooth
      (hasFiniteLength_of_isIrreducible π.irr)
  haveI : WellFoundedGT (Subrepresentation (jac e π.π)) :=
    ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have hne : (⊥ : Subrepresentation (jac e π.π)) ≠ ⊤ := by
    intro h
    apply hJ
    constructor
    intro x y
    have hx : x ∈ (⊥ : Subrepresentation (jac e π.π)) := h ▸ trivial
    have hy : y ∈ (⊥ : Subrepresentation (jac e π.π)) := h ▸ trivial
    exact (hx : x = 0).trans (hy : y = 0).symm
  obtain ⟨M, hM, -⟩ :=
    (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (jac e π.π))).resolve_left hne
  let q : (jac e π.π).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (jac e π.π)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (jac e π.π) := .of_surjective q hq
  refine ⟨_, _, _, subQuot ⊤ M, hirr, hsq.isSmooth (isSmooth_jac e π.smooth), hsq, ?_⟩
  exact injective_of_jacquet_surjective π e hirr q hq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceOfEmb

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

variable {E : Type} [Field E] [NumberField E] {C : Type} [NormedField C] [IsUltrametricDist C]

theorem norm_map_le_one (τ : E →+* C) (x : 𝓞 E) : ‖τ (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((x.isIntegral_coe).map (τ.toIntAlgHom))

def ballIdeal (τ : E →+* C) : Ideal (𝓞 E) where
  carrier := {x | ‖τ (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change ‖τ (a : E)‖ < 1 at ha
    change ‖τ (b : E)‖ < 1 at hb
    change ‖τ ((a : E) + (b : E))‖ < 1
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    change ‖τ (x : E)‖ < 1 at hx
    change ‖τ ((c : E) * (x : E))‖ < 1
    rw [map_mul, norm_mul]
    calc ‖τ (c : E)‖ * ‖τ (x : E)‖ ≤ 1 * ‖τ (x : E)‖ :=
          mul_le_mul_of_nonneg_right (norm_map_le_one τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact hx

theorem mem_ballIdeal (τ : E →+* C) (x : 𝓞 E) : x ∈ ballIdeal τ ↔ ‖τ (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (τ : E →+* C) : (ballIdeal τ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ballIdeal]; simp
  · intro a b hab
    change ‖τ ((a : E) * (b : E))‖ < 1 at hab
    rw [map_mul, norm_mul] at hab
    by_contra h
    push_neg at h
    rw [mem_ballIdeal, mem_ballIdeal] at h
    have ha : ‖τ (a : E)‖ = 1 := le_antisymm (norm_map_le_one τ a) (not_lt.1 h.1)
    have hb : ‖τ (b : E)‖ = 1 := le_antisymm (norm_map_le_one τ b) (not_lt.1 h.2)
    rw [ha, hb] at hab; norm_num at hab

end GlobalTheory.PlaceOfEmb

open GlobalTheory.PlaceOfEmb in
theorem GlobalTheory.PlaceOfEmb.exists_place_of_emb : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (τ : D.host.E →+* Qbar l), ∃ w : PlE D.host, w ∈ placesOver D.host.E l ∧ ∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal := by
  intro D l _ τ
  have hl : ((l : 𝓞 D.host.E)) ∈ ballIdeal τ := by
    rw [mem_ballIdeal]
    simp only [map_natCast]
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hne : ballIdeal τ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hl
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hl
  refine ⟨⟨ballIdeal τ, ballIdeal_isPrime τ, hne⟩, hl, fun x => Iff.rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitPlaceConj

theorem isSplitPl_w : ∀ (D : D7) (s : SplitPlace D.host.E), IsSplitPl D.host s.w := by
  intro D s
  have hc : ∀ z : D.host.E, IsCMField.complexConj D.host.E z = D.host.conj z := by
    intro z
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep D.host.E s
  let c : 𝓞 D.host.E →+* 𝓞 D.host.E :=
    RingOfIntegers.mapRingHom (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E)
  have hce : ((c e : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (e : D.host.E) := rfl
  refine ⟨c e, (s.split_mem_ideal _).2 (by rw [hce]; exact he'), fun y hy hm => ?_⟩
  have hye : (y : D.host.E) = (e : D.host.E) := by
    rw [hy, hce, ← hc, IsCMField.complexConj_apply_apply]
  have h1 := (s.split_mem_ideal y).1 hm
  rw [hye, he] at h1
  exact lt_irrefl _ h1

end GlobalTheory.SplitPlaceConj
end
end

