module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0168
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0171

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HomConjEquivMemHomAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory

theorem latSum_transport_equiv {E : Type} [Field E] [NumberField E] {H H₂ M : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] [AddCommMonoid M] (e : H ≃ₗ[𝓞 E] H₂) (A B : Submodule (𝓞 E) H)
    (A₂ B₂ : Submodule (𝓞 E) H₂) (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (hB : ∀ x, e x ∈ B₂ ↔ x ∈ B) (G : H → M) (F₂ : H₂ → M)
    (hG : ∀ x x', x - x' ∈ B → G x = G x') (hF : ∀ x, F₂ (e x) = G x) : latSum A₂ B₂ F₂ = latSum A B G := by
  have hAm : A.map (e : H →ₗ[𝓞 E] H₂) = A₂ := by
    ext y
    rw [Submodule.mem_map_equiv, ← hA, e.apply_symm_apply]
  let eA : ↥A ≃ₗ[𝓞 E] ↥A₂ := e.ofSubmodules A A₂ hAm
  have heA : ∀ x : A, ((eA x : A₂) : H₂) = e x := fun x => rfl
  have hBm : (B.comap A.subtype).map (eA : ↥A →ₗ[𝓞 E] ↥A₂) = B₂.comap A₂.subtype := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.subtype_apply, ← hB, ← heA, eA.apply_symm_apply]
  let q := Submodule.Quotient.equiv (B.comap A.subtype) (B₂.comap A₂.subtype) eA hBm
  unfold latSum
  rw [← finsum_comp_equiv q.toEquiv]
  refine finsum_congr fun z => ?_
  set r := Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z with hr
  set r₂ := Function.surjInv (Submodule.Quotient.mk_surjective (B₂.comap A₂.subtype)) (q.toEquiv z) with hr₂
  have h1 : Submodule.Quotient.mk r = z := Function.surjInv_eq _ z
  have h2 : Submodule.Quotient.mk r₂ = q z := Function.surjInv_eq _ _
  have h3 : q z = Submodule.Quotient.mk (eA r) := by
    rw [← h1]; rfl
  rw [h3, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, heA] at h2
  have h4 : (r₂ : H₂) = e (e.symm r₂) := (e.apply_symm_apply _).symm
  rw [h4, hF]
  apply hG
  rw [← hB, map_sub, ← h4]
  exact h2

noncomputable def homConjEquiv {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b) : HomE E a b ≃ₗ[𝓞 E] HomE E a b where
  toFun x := γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap
  invFun x := γ'.symm.toLinearMap ∘ₗ x ∘ₗ γ.toLinearMap
  map_add' x y := by simp [LinearMap.comp_add, LinearMap.add_comp]
  map_smul' r x := by
    ext y i
    simp [equiv_osmul]
  left_inv x := by ext y i; simp
  right_inv x := by ext y i; simp

theorem homConjEquiv_mem_homAt {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    (S : Finset (HeightOneSpectrum (𝓞 E))) (γ : Sp E a ≃ₗ[E] Sp E a) (γ' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    homConjEquiv γ γ' x ∈ homAt S (gmap γ N) (gmap γ' N') ↔ x ∈ homAt S N N' := by
  show (γ'.toLinearMap ∘ₗ x ∘ₗ γ.symm.toLinearMap) ∈ homAt S (gmap γ N) (gmap γ' N') ↔ _
  constructor
  · intro h P hP y hy
    have h1 := h P hP (γ y) ((mem_localization_gmap P γ N _).2 (by simpa using hy))
    have h2 := (mem_localization_gmap P γ' N' _).1 h1
    simpa using h2
  · intro h P hP y hy
    have h1 := h P hP (γ.symm y) ((mem_localization_gmap P γ N _).1 hy)
    exact (mem_localization_gmap P γ' N' _).2 (by simpa using h1)

theorem mem_divLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ divLat c A₂ ↔ x ∈ divLat c A := by
  show ((c : 𝓞 E) • e x) ∈ A₂ ↔ ((c : 𝓞 E) • x) ∈ A
  rw [← map_smul, hA]

theorem mem_mulLat_equiv_iff {E : Type} [Field E] [NumberField E] {H H₂ : Type} [AddCommGroup H] [Module (𝓞 E) H]
    [AddCommGroup H₂] [Module (𝓞 E) H₂] (e : H ≃ₗ[𝓞 E] H₂) (A : Submodule (𝓞 E) H) (A₂ : Submodule (𝓞 E) H₂)
    (hA : ∀ x, e x ∈ A₂ ↔ x ∈ A) (c : ℕ) (x : H) : e x ∈ mulLat c A₂ ↔ x ∈ mulLat c A := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e.symm y, (hA _).1 (by rw [e.apply_symm_apply]; exact hy), ?_⟩
    apply e.injective
    rw [← hxy]
    show e ((c : 𝓞 E) • e.symm y) = (c : 𝓞 E) • y
    rw [map_smul, e.apply_symm_apply]
  · rintro ⟨y, hy, hxy⟩
    refine ⟨e y, (hA _).2 hy, ?_⟩
    rw [← hxy]
    show (c : 𝓞 E) • e y = e ((c : 𝓞 E) • y)
    rw [map_smul]

theorem kerOf_gmap_frames : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (Sa : Finset (HeightOneSpectrum (𝓞 E))) (D cA cB : ℕ) (rho : UF E a →* Module.End K V) (rho' : UF E b →* Module.End K V') (sS sT : SB → E → K), ThDist.Ok th Sa D rho rho' sS sT → ∀ (γ : UF E a) (γ' : UF E b) (N : Submodule (𝓞 E) (Sp E a)) (fr : Frs E a SB) (N' : Submodule (𝓞 E) (Sp E b)) (fr' : Frs E b SB) (κ : GLQ E a SB) (κ' : GLQ E b SB) (Ξ Ξ₂ : HomE E a b → K) (c : K), IsSdLat N → IsSdLat N' → (∀ x z, z ∈ mulLat cB (homAt Sa N N') → Ξ (x + z) = Ξ x) → (∀ x : HomE E a b, Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) * ∏ P : SB, (sS P ((LinearEquiv.det (κ P).1 : Eˣ) : E) * sT P ((LinearEquiv.det (κ' P).1 : Eˣ) : E)) = c * Ξ x) → kerOf th Sa cA cB (gmap γ.1 N) (fun P => γ.1 * (fr P * (κ P).1)) (gmap γ'.1 N') (fun P => γ'.1 * (fr' P * (κ' P).1)) Ξ₂ = c • ((rho' γ') ∘ₗ kerOf th Sa cA cB N fr N' fr' Ξ ∘ₗ (rho γ⁻¹)) := by
  intro E K _ _ _ _ a b SB V V' _ _ _ _ th Sa D cA cB rho rho' sS sT hok γ γ' N fr N' fr' κ κ' Ξ Ξ₂ c hN hN' hΞ hΞ₂
  have hm : ∀ (g : UF E a), rho g ∘ₗ rho g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  have hm' : ∀ (g : UF E b), rho' g ∘ₗ rho' g⁻¹ = LinearMap.id := fun g => by
    rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl
  let φ : (V →ₗ[K] V') ≃+ (V →ₗ[K] V') :=
    { toFun := fun L => rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹
      invFun := fun L => rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ
      left_inv := fun L => by
        have h1 := hm γ⁻¹
        have h2 := hm' γ'⁻¹
        rw [inv_inv] at h1 h2
        show rho' γ'⁻¹ ∘ₗ (rho' γ' ∘ₗ L ∘ₗ rho γ⁻¹) ∘ₗ rho γ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, h1, ← LinearMap.comp_assoc, h2]; simp
      right_inv := fun L => by
        show rho' γ' ∘ₗ (rho' γ'⁻¹ ∘ₗ L ∘ₗ rho γ) ∘ₗ rho γ⁻¹ = L
        rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hm, ← LinearMap.comp_assoc, hm']; simp
      map_add' := fun L L' => by simp [LinearMap.comp_add, LinearMap.add_comp] }
  have hH := homConjEquiv_mem_homAt Sa γ.1 γ'.1 N N'
  unfold kerOf
  rw [latSum_transport_equiv (homConjEquiv γ.1 γ'.1) (divLat cA (homAt Sa N N')) (mulLat cB (homAt Sa N N')) _ _
    (mem_divLat_equiv_iff _ _ _ hH cA) (mem_mulLat_equiv_iff _ _ _ hH cB)
    (fun x => c • φ (Ξ x • th N fr N' fr' cB x))]
  · show _ = c • φ _
    unfold latSum
    rw [φ.map_finsum, smul_finsum]
  · intro x x' hx
    have h1 : Ξ x = Ξ x' := by
      have := hΞ x' (x - x') hx
      rwa [add_sub_cancel] at this
    rw [h1, hok.cong N fr N' fr' cB x x' hN hN' hx]
  · intro x
    show Ξ₂ (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) • th _ _ _ _ cB (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap)
      = c • (rho' γ' ∘ₗ (Ξ x • th N fr N' fr' cB x) ∘ₗ rho γ⁻¹)
    rw [hok.equiv γ γ' N (fun P => fr P * (κ P).1) N' (fun P => fr' P * (κ' P).1) cB x hN hN',
      hok.det N fr N' fr' cB x κ κ' hN hN', LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp,
      LinearMap.comp_smul, smul_smul, smul_smul, hΞ₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.BlockWindow

theorem jointTB_iff_jointCond (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ) :
    JointTB D HW F i r π M0 h0 cB ↔ JointConditionTameBound D HW F i r π M0 h0 cB := by
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun C hs Y hc hY => c C.LL C.le hs Y hc hY⟩
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun w hw => ?_⟩
    obtain ⟨a, b, c⟩ := h w hw
    exact ⟨a, b, fun CL hL hs Y hc hY => c ⟨CL, hL⟩ hs Y hc hY⟩

theorem jointCond_TB_at_range (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (large₂ : SizeData₂ D)
    (hJ : AdmissibleParameterJ.JumpConditions large₂) (hA : EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (cB : ℕ)
    (h2 : D.nd.l i ∉ D.host.small) (hq : D.nd.l i ≠ D.host.q) (hd : D.nd.l i ≠ D.host.d) (hG : GoodR D.nd i r)
    (hc : GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * large₂.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ cB) :
    ∃ M0 h0 : ℕ, JointConditionTameBound D HW F i r π M0 h0 cB := by
  obtain ⟨ht, hW⟩ := _root_.GlobalTheory.BlockWindow.jumpWindow_of_jumpSets D large₂ hJ hA
  have hT := _root_.GlobalTheory.BlockWindow.jointTB_of_jumpWindow D HW F i r π ⌊2 * large₂.sc.b⌋₊ h2 hq hd ht (hW i r hG π)
  exact ⟨_, _, (jointTB_iff_jointCond D HW F i r π _ _ _).1 (hT.mono hc)⟩

end GlobalTheory.BlockWindow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelFunctionsCommonLinearOperatorOffSplitPrime
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

namespace GlobalTheory.KerCommon

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := GlobalTheory.T.exists_common_scale_lattice_pairs_split_prime

theorem perO_scale : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (AA0 : Submodule (𝓞 E) E) (N₁ N₂ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₁' N₂' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (w : 𝓞 E), (∀ y ∈ N₂, w • y ∈ N₁) → (∀ y ∈ N₁', w • y ∈ N₂') → ∀ x ∈ perO AA0 N₁ N₁', (w * w) • x ∈ perO AA0 N₂ N₂' := by
  intro E _ _ _ a b AA0 N₁ N₂ N₁' N₂' w h2 h1 x hx
  unfold perO at hx ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, y, hy, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨r, hr, (w * w) • y, ?_, ?_⟩
    · intro v hv
      have h3 := h1 _ (hy _ (h2 v hv))
      have e : ((w * w) • y) v = w • y (w • v) := by
        rw [LinearMap.smul_apply, mul_smul, LinearMap.map_smul_of_tower]
      rw [e]
      exact h3
    · rw [smul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul o z _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h

theorem common_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι κ : Type) [Fintype ι] [Nonempty ι] [Fintype κ] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (AA0 : Submodule (𝓞 E) E) (SS : Finset (HeightOneSpectrum (𝓞 E))) (cl : ℕ) (N₀ : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N₀' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (N : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : κ → Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (g : 𝓞 E), δ ≠ 0 → (∃ k : 𝓞 E, g = 1 + (cl : 𝓞 E) * k) → (∀ i, (∀ x ∈ perO AA0 (N i) (N' i), g • x ∈ perO AA0 N₀ N₀') ∧ ∀ x ∈ perO AA0 N₀ N₀', g • x ∈ perO AA0 (N i) (N' i)) → relIdx (LamC emb δ AA0 N₀ N₀') (AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (BC emb δ AA0 SS N₀ N₀' cl) (LamC emb δ AA0 N₀ N₀' ⊓ AC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → relIdx (LamC emb δ AA0 N₀ N₀') (BC emb δ AA0 SS N₀ N₀' cl) ≠ 0 → ∃ SX SA SB : Finset (VV ι a b), ∀ i, IsReps (LamC emb δ AA0 (N i) (N' i)) (AC emb δ AA0 SS (N i) (N' i) cl) SX ∧ IsReps (BC emb δ AA0 SS (N i) (N' i) cl) (LamC emb δ AA0 (N i) (N' i) ⊓ AC emb δ AA0 SS (N i) (N' i) cl) SA ∧ IsReps (LamC emb δ AA0 (N i) (N' i)) (BC emb δ AA0 SS (N i) (N' i) cl) SB := _root_.GlobalTheory.CommonReps.common_reps_halves

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩

theorem unimod_iff {D : D7} {n : ℕ} (L : Submodule (𝓞 D.host.E) (Formalism.L2.Col.Sp D.host.E n)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ y, y ∈ L ↔ ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hm : ∀ y, y ∈ Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E n) L ↔
      ∀ x ∈ L, Formalism.BasicNotions.stdH D.host.E n x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
      Submodule.mem_one, RingHom.mem_range]
    rfl
  unfold Formalism.HermitianLatticesTheory.IsUnimodular
  constructor
  · intro h y
    rw [← hm y, h]
  · intro h
    ext y
    rw [hm y]
    exact (h y).symm

theorem admissible_pair_twist {D : D7} {a b : ℕ} (cl : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) (ex : HeightOneSpectrum (𝓞 D.host.E) → ℤ)
    (h01 : ∀ Q, ex Q = 1 ∨ ex Q = 0 ∨ ex Q = -1) (hc : ∀ Q, ex (Formalism.L2.Col.conjPrime₂ Q) = -ex Q) :
    TaylorLogMetric.admitted D a b N (twist₂ N' cl ex) := by
  have hl := hh_tw_lattice N' ⟨hA.2.2.2.1, by
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩ hcl ex h01
  have hspan : Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) = ⊤ := by
    apply top_unique
    rw [← hA.2.2.2.2.1]
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E))
    have hx' : (cl : 𝓞 D.host.E) • x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) :=
      Submodule.subset_span (hh_tw_of N' hcl ex h01 hx)
    have hc : (cl : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hcl.ne'
    have hx'' : (cl : D.host.E) • x ∈ Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using hx'
    have := Submodule.smul_mem (Submodule.span D.host.E (↑(twist₂ N' cl ex) : Set (Fin b → D.host.E))) (cl : D.host.E)⁻¹ hx''
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using this
  exact ⟨hA.1, hA.2.1, hA.2.2.1, hl.fg, hspan,
    (unimod_iff _).1 (twist_selfDual D.host.E b N' cl ex hA.2.2.2.1 hcl hc ((unimod_iff _).2 hA.2.2.2.2.2))⟩

theorem split_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl)
    (hSS : ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS) :
    SplitHyp (hK D cc δ a b) (alK D cc δ a b) (halfA cc δ SS cl N N') (halfB cc δ SS cl N N') (lamK cc δ N N') := by
  have := tau_nonempty D
  have he1 : ∀ Q, expS SS Q = 1 ∨ expS SS Q = 0 ∨ expS SS Q = -1 := expS_cases SS
  have he2 : ∀ Q, (fun Q => -expS SS Q) Q = 1 ∨ (fun Q => -expS SS Q) Q = 0 ∨ (fun Q => -expS SS Q) Q = -1 := by
    intro Q
    have := he1 Q
    show -expS SS Q = 1 ∨ -expS SS Q = 0 ∨ -expS SS Q = -1
    omega
  have hconj1 : ∀ Q, expS SS (Formalism.L2.Col.conjPrime₂ Q) = -expS SS Q := exponent_set_conjugate D.host.E SS hSS
  have hconj2 : ∀ Q, (fun Q => -expS SS Q) (Formalism.L2.Col.conjPrime₂ Q) = -(fun Q => -expS SS Q) Q := by
    intro Q
    show -expS SS (Formalism.L2.Col.conjPrime₂ Q) = - -expS SS Q
    rw [hconj1 Q]
  exact half_periods_of_lattice D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ (aaOf D cc) SS N N' cl
    (KS.Lat.delta_ne hcc hδ) hcl hSS hA.2.2.1.1 (laFacts_of_adm B hcc hδ hA)
    (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he1 hconj1)) (laFacts_of_adm B hcc hδ (admissible_pair_twist cl N N' hA hcl _ he2 hconj2))

theorem finIdx_of_adm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {a b : ℕ} (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E))
    (hA : TaylorLogMetric.admitted D a b N N') (hcl : 0 < cl) : FinIdx cc δ SS cl N N' :=
  finite_index_of_fg D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS N N' cl hcl
    (period_lattice_finitely_generated D.host.E D.what₂.Tau a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) N N' hA.2.2.2.1 hA.2.2.1.2.1 (aaOf_fg cc))

theorem eNat_fixed_of_vec {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hV : B.VecP χ) {a b : ℕ}
    {N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} (hA : TaylorLogMetric.admitted D a b N N') :
    B.eNat χ a b N N' ∈ fixedBy (hK D cc δ a b) (alK D cc δ a b) (lamK cc δ N N') := by
  have hm := (hV a b N N' hA).1
  intro x hx z
  have hx' : x ∈ TaylorLogMetric.La D B.tor N N' := by rw [← lamK_eq cc δ N N']; exact hx
  have h1 := hm.2 x hx' z
  rw [U_eq_opU] at h1
  have hal : alK D cc δ a b x = TaylorLogMetric.al D B.tor x := by
    rw [KS.Lat.al_eq_La B hcc hδ hA x hx']
    unfold alK alV
    rw [HV_eq_formV]
  rw [hal]
  exact h1

theorem locP_eq_of_scale {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]
    (M M₀ : Submodule (𝓞 E) W) (g : 𝓞 E) (Q : HeightOneSpectrum (𝓞 E)) (hg : g ∉ Q.asIdeal)
    (h1 : ∀ x ∈ M, g • x ∈ M₀) (h2 : ∀ x ∈ M₀, g • x ∈ M) :
    Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M = Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M₀ := by
  have hg' : g ∈ Q.asIdeal.primeCompl := hg
  ext x
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h1 _ hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨g * s, Q.asIdeal.primeCompl.mul_mem hg' hs, by rw [mul_smul]; exact h2 _ hx⟩

theorem kerTh_common_op : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := by
  intro D cc δ B χ hcc hδ hδ0 _hL hV SS cl hcl hSS a b P _hP hPS hPS' hcP _hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN
  have := tau_nonempty D
  obtain ⟨g, ⟨k, hk⟩, hgQ, hg⟩ := exists_scale D P SS cl hPS hPS' hcP ι a b N N₀ N' N₀' fun i => (hN i).2
  have hsc : ∀ i, (∀ x ∈ perO (aaOf D cc) (N i) (N' i), (g * g) • x ∈ perO (aaOf D cc) N₀ N₀') ∧
      ∀ x ∈ perO (aaOf D cc) N₀ N₀', (g * g) • x ∈ perO (aaOf D cc) (N i) (N' i) := fun i =>
    ⟨perO_scale D.host.E a b (aaOf D cc) (N i) N₀ (N' i) N₀' g (hg i).1.2 (hg i).2.1,
      perO_scale D.host.E a b (aaOf D cc) N₀ (N i) N₀' (N' i) g (hg i).1.1 (hg i).2.2⟩
  have hI0 := finIdx_of_adm (cc := cc) (δ := δ) SS cl N₀ N₀' hA0 hcl
  obtain ⟨SX, SA, SB, hR⟩ := common_reps D.host.E D.what₂.Tau ι a b (fun τ => TaylorLogMetric.embT D τ) δ (aaOf D cc) SS cl N₀ N₀' N N' (g * g) hδ0
    ⟨k + k + (cl : 𝓞 D.host.E) * k * k, by rw [hk]; ring⟩ hsc hI0.1 hI0.2.1 hI0.2.2
  have hxi0 : ∀ z, xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 z = 0 := by
    intro z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) 0 0 z).2.2.2
    have e : (fun v : TaylorLogMetric.VC D a b => (1 : ℂ) * (0 : TaylorLogMetric.VC D a b → ℂ) v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = 0 := by
      funext v; simp
    rw [e, one_mul] at h
    linear_combination -h
  refine ⟨{ toFun := fun θ => xiL (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) θ,
            map_add' := ?_, map_smul' := ?_ }, fun i => ?_⟩
  · intro x y
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB 1 (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x y z).2.2.2
    have e : (fun v => (1 : ℂ) * x v + y v) = x + y := by funext v; simp
    rw [e, one_mul] at h
    simpa using h
  · intro c x
    funext z
    have h := (twist_linear _ (hK D cc δ a b) (alK D cc δ a b) 1 SX SA SB c (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ)
      (onV (fun τ => TaylorLogMetric.embT D τ) δ Ξ) x 0 z).2.2.2
    have e : (fun v => c * x v + (0 : TaylorLogMetric.VC D a b → ℂ) v) = c • x := by funext v; simp
    rw [e, hxi0, add_zero] at h
    simpa using h
  · obtain ⟨hAi, -, -⟩ := hN i
    have hyp := split_of_adm B SS cl (N i) (N' i) hcc hδ hAi hcl hSS
    have hIi := finIdx_of_adm (cc := cc) (δ := δ) SS cl (N i) (N' i) hAi hcl
    have hθ := eNat_fixed_of_vec B χ hcc hδ hV hAi
    have hg2 : ∀ Q ∈ SS, g * g ∉ Q.asIdeal := fun Q hQ h =>
      (Q.isPrime.mem_or_mem h).elim (hgQ Q hQ) (hgQ Q hQ)
    have hDi : DatLoc D cc SS cl (N i) (N' i) Ξ :=
      hD.of_locP_eq fun Q hQ => locP_eq_of_scale _ _ (g * g) Q (hg2 Q hQ) (hsc i).1 (hsc i).2
    have hinv := hDi.invOn (fun τ => TaylorLogMetric.embT D τ) δ (embH_inj _ hδ0)
    funext z
    exact twist_representatives _ (hK D cc δ a b) (alK D cc δ a b) _ _ _ hyp SX SA SB _ _ _ (hR i).1 (hR i).2.1 (hR i).2.2
      (repsOf_spec _ _ hIi.1) (repsOf_spec _ _ hIi.2.1) (repsOf_spec _ _ hIi.2.2) 1 _ hθ _ hinv z

end GlobalTheory.KerCommon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeterssonFormProportionalClassSumAllLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ChainE

variable {D : D7}

theorem mult_level {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (U : MMap M) (hU : U ∈ Mult θ M J χ) (v : M.Vec) : ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy, mul_add]
  | smul a x _ hx => simp only [MultilinearMap.smul_apply, Pi.smul_apply, hx, smul_eq_mul, mul_left_comm]

theorem natCast_pow_notMem (P : Pl D.host.E) {n : ℕ} (h : ((n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (c : ℕ) :
    ((n ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
  h (P.isPrime.mem_of_pow_mem c (by rwa [Nat.cast_pow] at h'))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (H : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (Φ : GA D V → ℂ)
    (h : ∀ g0 : G0 L.Pg L.r, actG0 V β L g0 (H Φ) = H (actG0 V β L g0 Φ)) :
    gaL V β L eG c (H Φ) = H (gaL V β L eG c Φ) := by
  unfold gaL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg (c g • ·) (h (eG g))

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnFrom_hk (t : T) (P : Pl D.host.E) (cs : ℕ → List ℤ →₀ ℂ)
    (hs : ∀ k, k + 1 < D.R.m → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P (cs (k + 1)) (U.1 v)) →
      ∀ v, (R.ioY t k U').1 v = hk _ P (cs k) ((R.ioY t k U).1 v))
    (n : ℕ) (hn : n < D.R.m) (U U' : R.CC t n) (hU : ∀ v, U'.1 v = hk _ P (cs n) (U.1 v)) :
    ∀ v, (Lift.dnFrom (R.CC t) (R.ioY t) n U').1 v = hk _ P (cs 0) ((Lift.dnFrom (R.CC t) (R.ioY t) n U).1 v) := by
  induction n with
  | zero => exact hU
  | succ k ih => exact ih (by omega) (R.ioY t k U) (R.ioY t k U') (hs k hn U U' hU)

noncomputable def liftCC (t : T) (y : (R.HX t).H) : R.CC t 0 :=
  Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))

theorem thDn_eq (t : T) (y : (R.HX t).H) : R.thDn t y = (liftCC t y).1 := rfl

theorem e_Th (hT : R.chain_Th) (t : T) (x : (R.HX t).H) (v : (R.MY 0).Vec) : R.HE.e (R.Th t x) v =
    R.e0 ((liftCC t x).1 (PiTensorProduct.tprod ℂ v)) := by
  rw [hT t x, postOn_apply, thDn_eq t x]
  rfl

theorem compositeLift_relation_passes_to_rows (F : Face D A) (hl : R.toLevCh.Is A.μ0) (t : T) (P : Pl D.host.E) (hP : Good R t P) (c : List ℤ →₀ ℂ) (U : R.CC t 0)
    (v : (R.MY 0).Vec) :
    R.e0 (hk _ P c (U.1 (PiTensorProduct.tprod ℂ v))) = hk _ P c (R.e0 (U.1 (PiTensorProduct.tprod ℂ v))) := by
  obtain ⟨n, hn⟩ := hl.βY 0 (by have := D.R.two_le_m; omega)
  have hN := natCast_pow_notMem P ((_root_.GlobalTheory.GoodPrimes.good_primes R F hl).2.1 t P hP).1 n
  have h1 := (_root_.GlobalTheory.LevOp.level_operators _ _ _ _ (R.datYt t 0 R.triv) hn P hN hP).1
  have h2 := (_root_.GlobalTheory.LevOp.level_operators _ _ _ _ (R.dat0 R.triv) hn P hN fun PP h =>
    hP PP (Or.inl (h.resolve_right (Finset.notMem_empty PP)))).2.2.2.1
  have h3 := mult_level _ _ _ _ _ ((mem_multT R.θ (R.MY 0) _ _ _).1 U.2) v
  refine gaL_comm _ _ _ _ _ _ _ fun g0 => h2 c g0 _ fun k hk h => ?_
  have h4 := h3 k (h1 k hk).1 h
  rw [(h1 k hk).2, one_mul] at h4
  exact h4

theorem e_Th_hk (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hT : R.chain_Th) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (c : List ℤ →₀ ℂ) (y y' : (R.HX t).H) (h : ∀ v, (liftCC t y').1 v = hk _ P c ((liftCC t y).1 v)) :
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e (R.Th t y)) := by
  refine MultilinearMap.ext fun v => ?_
  exact ((e_Th hT t y' v).trans ((congrArg R.e0 (h _)).trans (compositeLift_relation_passes_to_rows F hl t P hP c (liftCC t y) v))).trans
    ((postOn_apply _ _ _ v).trans (congrArg (hk (Yc D 0) P c) (e_Th hT t y v))).symm

end Chain

theorem matchE_of_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P hP hF cX cs hX hY y y' hy
  refine e_Th_hk F hC.lev hC.chain.Th t P hP (cs 0) y y' ?_
  exact dnFrom_hk t P cs (fun k hk => _root_.GlobalTheory.ChainStepHecke.step_hk R F hI hC hS t P k hP hk (hF.1 k hk) _ _ (hY k hk))
    (D.R.m - 1) (by have := D.R.two_le_m; omega) _ _ (_root_.GlobalTheory.Hk3.StepX.stepX_hk R F hC hS t P hP hF.2.1 _ _ hX y y' hy)

end GlobalTheory.Hk3.ChainE
end

