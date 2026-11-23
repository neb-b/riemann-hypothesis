module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertUnitaryCosetSymmetryHeckeEven
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.InertSym

theorem cosets_eq {G : Type} [Group G] (K : Subgroup G) {g g' : G} {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : g' = a * g * b) (c : G ⧸ K) :
    (∃ k ∈ K, c = ((k * g' : G) : G ⧸ K)) ↔ (∃ k ∈ K, c = ((k * g : G) : G ⧸ K)) := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, mul_mem hk ha, ?_⟩
    rw [e, show k * (a * g * b) = (k * a * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, mul_mem hk (inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = (k * g) * b by group, QuotientGroup.mk_mul_of_mem _ hb]

theorem cosetSym_of_inv {G : Type} [Group G] (K : Subgroup G)
    (h : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, g⁻¹ = a * g * b) : CosetSym K := by
  intro g
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (Nat.card_congr (Equiv.subtypeEquivRight fun c => cosets_eq K ha hb e c)).symm

theorem inv_mem_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) (g : GU σ n) :
    ∃ a ∈ KU σ n, ∃ b ∈ KU σ n, g⁻¹ = a * g * b := by
  have hint : ∀ i j, Formalism.UG.antiJ L n i j ∈ Formalism.UG.intL L := by
    intro i j; unfold Formalism.UG.antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := Formalism.UG.P.cartan_exists_glint (Formalism.UG.intL L) _ _
    (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := (GlobalTheory.UnitarySwap.inv_mem_doubleCoset_and_comm).1 L ϖ σ q n J hU hJ (by
    intro i j
    rw [hJe]
    simp only [Formalism.UG.antiJ, add_comm i.val j.val]
    split_ifs <;> simp) (g : GL (Fin n) L) (by rw [hJe]; exact g.2)
  rw [hJe] at hk₁ hk₂
  exact ⟨⟨k₁, hk₁.1⟩, hk₁, ⟨k₂, hk₂.1⟩, hk₂, Subtype.ext e⟩

end GlobalTheory.ChainOnto.InertSym

namespace GlobalTheory.ChainOnto

theorem inert_cosetSym_heckeEven : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ n : ℕ, IsCommensurated (KU σ n) ∧ CosetSym (KU σ n) ∧ ∀ φ ∈ Hecke ℂ (KU σ n), ∀ g, φ g⁻¹ = φ g := by
  intro L _ _ _ ϖ σ q hU n
  refine ⟨Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n, InertSym.cosetSym_of_inv _ (InertSym.inv_mem_KU hU n), ?_⟩
  intro φ hφ g
  obtain ⟨a, ha, b, hb, e⟩ := InertSym.inv_mem_KU hU n g
  rw [e]
  exact hφ.1 ⟨a, ha⟩ ⟨b, hb⟩ g

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralGLCommensuratedDoubleCosetCardInvSymm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.CosetSymGL

abbrev Cos {G : Type} [Group G] (K : Subgroup G) (g : G) : Type :=
  {c : G ⧸ K // ∃ k ∈ K, c = ((k * g : G) : G ⧸ K)}

theorem card_cos_eq_of_mem {G : Type} [Group G] {K : Subgroup G} {g h a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (e : h = a * g * b) : Nat.card (Cos K h) = Nat.card (Cos K g) := by
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a, K.mul_mem hk ha, ?_⟩
    rw [e, ← mul_assoc, ← mul_assoc, QuotientGroup.mk_mul_of_mem _ hb]
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k * a⁻¹, K.mul_mem hk (K.inv_mem ha), ?_⟩
    rw [e, show k * a⁻¹ * (a * g * b) = k * g * b by group, QuotientGroup.mk_mul_of_mem _ hb]

def quotEquiv {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) : G ⧸ K ≃ G ⧸ K :=
  Quotient.congr θ.toEquiv fun a b => by
    change QuotientGroup.leftRel K a b ↔ QuotientGroup.leftRel K (θ a) (θ b)
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, ← map_inv, ← map_mul, hθ]

theorem quotEquiv_mk {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (x : G) :
    quotEquiv K θ hθ (x : G ⧸ K) = ((θ x : G) : G ⧸ K) := rfl

theorem card_cos_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K) (g : G) :
    Nat.card (Cos K g) = Nat.card (Cos K (θ g)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (quotEquiv K θ hθ) fun c => ?_)
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨θ k, (hθ k).2 hk, by rw [quotEquiv_mk, map_mul]⟩
  · rintro ⟨k, hk, e⟩
    refine ⟨θ.symm k, (hθ _).1 (by simpa using hk), (quotEquiv K θ hθ).injective ?_⟩
    rw [e, quotEquiv_mk, map_mul, MulEquiv.apply_symm_apply]

theorem cosetSym_of_aut {G : Type} [Group G] (K : Subgroup G) (θ : G ≃* G) (hθ : ∀ x, θ x ∈ K ↔ x ∈ K)
    (h : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g⁻¹ * b) : CosetSym K := fun g => by
  obtain ⟨a, ha, b, hb, e⟩ := h g
  exact (card_cos_aut K θ hθ g).trans (card_cos_eq_of_mem ha hb e)

end GlobalTheory.ChainOnto.CosetSymGL

namespace GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.LFun.ConjPlace in
theorem invT_of_symm {L : Type} [Field L] {n : ℕ} (d : GL (Fin n) L)
    (hd : (d : Matrix (Fin n) (Fin n) L)ᵀ = (d : Matrix (Fin n) (Fin n) L)) : invT (RingEquiv.refl L) n d = d⁻¹ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [invT_val, RingEquiv.refl_apply, Matrix.coe_units_inv]
  conv_lhs => rw [← hd]
  rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply]

open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_iff {L : Type} [Field L] {n : ℕ} (O : Subring L) (g : GL (Fin n) L) :
    invT (RingEquiv.refl L) n g ∈ Formalism.UG.GLint (Fin n) O ↔ g ∈ Formalism.UG.GLint (Fin n) O :=
  (mem_iff_invT (RingEquiv.refl L) (O := O) (O' := O) (fun _ => Iff.rfl) g).symm


open GlobalTheory.LFun.ConjPlace in
theorem invT_mem_doset (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (g : GL (Fin n) (w.adicCompletion E)) : ∃ a ∈ KGL w (n := n), ∃ b ∈ KGL w (n := n),
      invT (RingEquiv.refl _) n g = a * g⁻¹ * b := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV (E := E) w
  have hϖO : ϖ ∈ Formalism.UG.Ov E w := by
    change Valued.v ϖ ≤ 1
    unfold Formalism.UG.IsUnifV at hϖ
    rw [hϖ]
    exact (WithZero.exp_le_exp.mpr (by norm_num : (-1:ℤ) ≤ 0)).trans (le_of_eq WithZero.exp_zero)
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, hg⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  set d : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hd
  have hdv : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hd, Units.val_mul, Units.val_mul, hg, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc,
      Units.mul_inv, mul_one]
  have hsym : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E))ᵀ = (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    rw [hdv, Formalism.UG.diagPow, Matrix.diagonal_transpose]
  have hgd : g = k₁ * d * k₂ := by rw [hd]; group
  set θ := invT (RingEquiv.refl (w.adicCompletion E)) n
  refine ⟨θ k₁ * k₂, (KGL w (n := n)).mul_mem ((invT_mem_iff _ _).2 hk₁) hk₂,
    k₁ * θ k₂, (KGL w (n := n)).mul_mem hk₁ ((invT_mem_iff _ _).2 hk₂), ?_⟩
  have hθd : θ d = d⁻¹ := invT_of_symm d hsym
  rw [hgd, map_mul, map_mul, hθd, hd]
  group

end GlobalTheory.ChainOnto.CosetSymGL


open GlobalTheory.ChainOnto.CosetSymGL GlobalTheory.LFun.ConjPlace in
theorem GlobalTheory.ChainOnto.kGL_commensurated_cosetSym : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), IsCommensurated (KGL w (n := n)) ∧ CosetSym (KGL w (n := n)) := fun E _ _ w n =>
  ⟨Formalism.UG.Final.GLintComm E w n, cosetSym_of_aut _ (invT (RingEquiv.refl _) n) (fun x => invT_mem_iff _ x)
    (invT_mem_doset E w n)⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralHeisenbergInvariantFormsProportional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto


open Classical in
theorem heisInv_forms_proportional : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ l e : M →ₗ[ℂ] ℂ, (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, l (ρ u m) = l m) → (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, e (ρ u m) = e m) → ∀ m, e m * l s = l m * e s := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s h l e hl he m
  have hH := h.isHeis

  have key : ∀ (f : M →ₗ[ℂ] ℂ), (∀ u ∈ intMat L (Fin n') (Fin n), ∀ m, f (ρ u m) = f m) →
      ∀ x : Matrix (Fin n') (Fin n) L, f (ρ x s) = if x ∈ intMat L (Fin n') (Fin n) then f s else 0 := by
    intro f hf x
    split_ifs with hx
    · rw [h.fixes x hx]
    · have : ∃ i j, x i j ∉ Formalism.UG.intL L := by
        by_contra hc
        push_neg at hc
        exact hx hc
      obtain ⟨i, j, hij⟩ := this
      obtain ⟨u, hu, hne⟩ := GlobalTheory.SphTheta.exists_pairing_single_ne h.1.unr h.v_two h.1.delta.1 h.1.psi_ne x hij
      have hu' : Matrix.single i.rev j.rev u ∈ intMat L (Fin n') (Fin n) := by
        intro i' j'
        rw [Matrix.single_apply]
        split_ifs
        exacts [hu, zero_mem _]
      have hc := hH.comm (Matrix.single i.rev j.rev u) x s
      rw [h.fixes _ hu'] at hc
      have h1 := hf _ hu' (ρ x s)
      rw [hc, map_smul, smul_eq_mul, hH.swap] at h1
      have hz : (GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ ≠ 1 := by
        intro h'; exact hne (inv_eq_one.1 h')
      have : ((GlobalTheory.SphTheta.pairing σ δ ψ x (Matrix.single i.rev j.rev u))⁻¹ - 1) * f (ρ x s) = 0 := by
        rw [sub_mul, one_mul, h1, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hz)
  have hall : (l s) • e = (e s) • l := by
    refine LinearMap.ext_on_range h.2.2.2 fun x => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, key e he x, key l hl x]
    split_ifs <;> ring
  have := LinearMap.congr_fun hall m
  simp only [LinearMap.smul_apply, smul_eq_mul] at this
  rw [mul_comm, this, mul_comm]

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralNormSqMatrixCoefficientNeZeroDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory

theorem integral_normSq_coef_ne_zero : ∀ (D : D7) (V : HSp D), V.SigOK → V.IsPosDef → ∀ (c : CoefA V), c.Is → ∀ w : c.W, w ≠ 0 → ∀ mR : Measure (GinfC V), mR.IsHaarMeasure → ∫ b : GinfC V, ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 ∂mR ≠ 0 := by
  intro D V hS hp c hc w hw mR hR
  have : CompactSpace (GinfC V) :=
    isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hp τ))
  set f : GinfC V → ℝ := fun b => ‖⟪w, c.ρ (b : GA D V) w⟫_ℂ‖ ^ 2 with hfdef
  have hcont : Continuous f := by
    have h1 : Continuous fun b : GinfC V => c.ρ (b : GA D V) w := (hc.2.2.1 w).comp continuous_subtype_val
    exact ((continuous_const.inner h1).norm).pow 2
  have hnn : 0 ≤ f := fun b => by positivity
  have hint : Integrable f mR := hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have h1 : f 1 ≠ 0 := by
    simp only [hfdef, OneMemClass.coe_one, map_one, Module.End.one_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.2 (inner_self_ne_zero.2 hw))
  have hpos : 0 < ∫ b, f b ∂mR := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    exact hcont.isOpen_support.measure_pos mR ⟨1, h1⟩
  exact hpos.ne'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactFiniteAdelicSubgroupIntegralOpenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ K : Subgroup (GA D V), K ≤ GfC V → (∀ k ∈ K, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v) → (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ K) → IsCompact (K : Set (GA D V)) := by
  first | exact @GlobalTheory.ChainOnto.isCompact_of_integral_open | exact GlobalTheory.ChainOnto.isCompact_of_integral_open | (intros; apply GlobalTheory.ChainOnto.isCompact_of_integral_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceNonsplitPlaceStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ v : FinPl D, ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
  first | exact @GlobalTheory.InertIwasawa.hasIwasawa_inert | exact GlobalTheory.InertIwasawa.hasIwasawa_inert | (intros; apply GlobalTheory.InertIwasawa.hasIwasawa_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicColumnsRingIsoComplex
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

open Matrix Formalism.UG

namespace GlobalTheory.Core.Rk.IwArch

section IsoCol

variable {A : Type} [CommRing A]

theorem map_cT_rect (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) {m p : Type}
    (M : Matrix m p A) : (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

theorem exists_compact_keep_cols {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f)
    (hσ : ∀ x, f (σ x) = star (f x)) {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool)
    (hb : cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1))
    (X : Matrix (Fin n) (Fin r) A) (hX : cT σ X * J * X = 0) (g : GL (Fin n) A) (hg : g ∈ UJ σ J) :
    ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧
      ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β := by
  set F := RingEquiv.ofBijective f hf
  have hfF : ∀ z : ℂ, f (F.symm z) = z := fun z => F.apply_symm_apply z
  have hfinj : ∀ {p q : Type} (M N : Matrix p q A), M.map f = N.map f → M = N := fun M N h =>
    Matrix.ext fun i j => hf.1 (congrFun (congrFun h i) j)
  set D : Matrix (Fin n) (Fin n) A := Matrix.diagonal fun i => if ε i then 1 else -1 with hD
  have hJm : D.map f = Formalism.REAL.Jm ε := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases he : ε i <;> simp [D, Formalism.REAL.Jm, he]
    · simp [D, Formalism.REAL.Jm, h]

  set h0 := b⁻¹ * g * b with hh0def
  have hh0 : h0 ∈ UJ σ D := hb ▸ conj_mem_UJ σ b hg
  have hh0' : Formalism.REAL.inUJ ε (h0.1.map f) := by
    have e : cT σ h0.1 * D * h0.1 = D := hh0
    have := congrArg (fun M => M.map f) e
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm] at this
    exact this
  let g' : Formalism.REAL.UJ ε := ⟨bc f h0, hh0'⟩

  set Y := (b⁻¹).1 * X with hYdef
  set X' := Y.map f with hX'def
  have hY : cT σ Y * D * Y = 0 := by
    rw [← hb, hYdef, cT_mul]
    calc cT σ X * cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * ((b⁻¹).1 * X)
        = cT σ X * (cT σ (b⁻¹).1 * (cT σ b.1 * J * b.1) * (b⁻¹).1) * X := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [cT_inv_cancel, hX]
  have hiso0 : X'ᴴ * Formalism.REAL.Jm ε * X' = 0 := by
    have := congrArg (fun M => M.map f) hY
    simp only [Matrix.map_mul, map_cT_rect σ f hσ, hJm, Matrix.map_zero _ (map_zero f)] at this
    exact this
  set W := LinearMap.range X'.mulVecLin with hWdef
  let Wf : Fin 2 → Submodule ℂ (Fin n → ℂ) := ![⊥, W]
  have hflag : GlobalTheory.FlagMeas.IsIsoFlag ε (a := 1) (fun _ => Module.finrank ℂ W) Wf := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [Wf]
    · intro i
      fin_cases i
      show Module.finrank ℂ W = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + Module.finrank ℂ W
      rw [finrank_bot, zero_add]
    · intro x hx y hy
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      simp only [Matrix.mulVecLin_apply]
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        ← Matrix.mul_assoc, hiso0, Matrix.vecMul_zero, zero_dotProduct]
  obtain ⟨k0, hk0, hk0W⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact hflag g'
  have hkeep : ∀ y ∈ W, Formalism.MainNotions.S.uMat (g' * k0⁻¹) *ᵥ y ∈ W := fun y hy => hk0W 1 y hy

  let k1 : GL (Fin n) A := bc (F.symm : ℂ →+* A) (k0 : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have hbc : ∀ u : (Matrix (Fin n) (Fin n) ℂ)ˣ, (bc (F.symm : ℂ →+* A) u).1.map f = u.1 := by
    intro u; ext i j; simp [bc, hfF]
  have hk1f : k1.1.map f = Formalism.MainNotions.S.uMat k0 := hbc _
  have hk1if : (k1⁻¹).1.map f = Formalism.MainNotions.S.uMat k0⁻¹ := by
    have : k1⁻¹ = bc (F.symm : ℂ →+* A) ((k0⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
      simp [k1, map_inv]
    rw [this]; exact hbc _
  have hk1D : k1 ∈ UJ σ D := by
    show cT σ k1.1 * D * k1.1 = D
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, hJm]
    exact k0.2
  have hk1one : k1 ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) := by
    show cT σ k1.1 * 1 * k1.1 = 1
    apply hfinj
    rw [Matrix.map_mul, Matrix.map_mul, map_cT_rect σ f hσ, hk1f, Matrix.map_one _ (map_zero f) (map_one f),
      Matrix.mul_one]
    exact hk0
  refine ⟨b * k1 * b⁻¹, ?_, ?_, ?_⟩
  · have hk1' : k1 ∈ UJ σ (cT σ b.1 * J * b.1) := by rw [hb]; exact hk1D
    have := conj_mem_UJ σ b⁻¹ hk1'
    rw [cT_inv_cancel, inv_inv] at this
    exact this
  · convert hk1one using 1
    group

  set H := (h0 * k1⁻¹).1 with hHdef
  have hHf : H.map f = Formalism.MainNotions.S.uMat (g' * k0⁻¹) := by
    rw [hHdef, Units.val_mul, Matrix.map_mul, hk1if]
    rfl
  have hcol : ∀ c : Fin r, ∃ w : Fin r → ℂ, X' *ᵥ w = H.map f *ᵥ (X' *ᵥ Pi.single c 1) := by
    intro c
    have hm := hkeep _ (LinearMap.mem_range_self X'.mulVecLin (Pi.single c 1))
    rw [← hHf] at hm
    obtain ⟨w, hw⟩ := hm
    exact ⟨w, hw⟩
  choose w hw using hcol
  let β' : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i c => w c i
  have hHX : H.map f * X' = X' * β' := by
    ext i c
    have h1 := congrFun (hw c) i
    have e1 : (H.map f * X') i c = (H.map f *ᵥ (X' *ᵥ Pi.single c 1)) i := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one]; rfl
    have e2 : (X' * β') i c = (X' *ᵥ w c) i := by
      rw [Matrix.mul_apply, Matrix.mulVec, dotProduct]; rfl
    rw [e1, e2, h1]
  refine ⟨β'.map F.symm, ?_⟩
  have hβf : (β'.map F.symm).map f = β' := by ext i j; simp [hfF]
  have hHY : H * Y = Y * β'.map F.symm := by
    have e1 : (H * Y).map f = H.map f * X' := Matrix.map_mul
    have e2 : (Y * β'.map F.symm).map f = X' * β' := by rw [Matrix.map_mul, hβf]
    apply hfinj
    rw [e1, e2]
    exact hHX
  have hgk : g * (b * k1 * b⁻¹)⁻¹ = b * (h0 * k1⁻¹) * b⁻¹ := by
    rw [hh0def]; group
  rw [hgk, Units.val_mul, Units.val_mul]
  calc b.1 * H * (b⁻¹).1 * X = b.1 * (H * Y) := by rw [hYdef]; simp only [Matrix.mul_assoc]
    _ = b.1 * ((b⁻¹).1 * X * β'.map F.symm) := by rw [hHY]
    _ = X * β'.map F.symm := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem iw_iso_cols : ∀ {A : Type} [CommRing A] {n r : ℕ} (σ : A →+* A) (f : A →+* ℂ), Function.Bijective f → (∀ x, f (σ x) = star (f x)) → ∀ {J : Matrix (Fin n) (Fin n) A} (b : GL (Fin n) A) (ε : Fin n → Bool), Formalism.UG.cT σ b.1 * J * b.1 = (Matrix.diagonal fun i => if ε i then 1 else -1) → ∀ (X : Matrix (Fin n) (Fin r) A), Formalism.UG.cT σ X * J * X = 0 → ∀ g : GL (Fin n) A, g ∈ UJ σ J → ∃ k ∈ UJ σ J, b⁻¹ * k * b ∈ UJ σ (1 : Matrix (Fin n) (Fin n) A) ∧ ∃ β : Matrix (Fin r) (Fin r) A, (g * k⁻¹).1 * X = X * β  := by
  intro A _ n r σ f hf hσ J b ε hb X hX g hg
  exact exists_compact_keep_cols σ f hf hσ b ε hb X hX g hg

end IsoCol

end GlobalTheory.Core.Rk.IwArch
end

