module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TracePairingNonzeroIntertwiner
section
noncomputable section

open MeasureTheory
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {Z : Type} [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]

theorem avg_inner_map {T : W →L[ℂ] W} (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : W) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : W →ₗ[ℂ] W), hT⟩ : W →ₗᵢ[ℂ] W).inner_map_map x y

theorem avg_secondCountable (ε : Fin n → Bool) : SecondCountableTopology (KG ε) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact hemb.isInducing.secondCountableTopology

theorem avg_continuous_toMK (ε : Fin n → Bool) : Continuous (fun k : KG ε => toMK k) :=
  ((Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal).continuous

def avgF (T : Mat n → (W →L[ℂ] W)) (S : Mat n → (Z →L[ℂ] Z)) (e : W) (f : Z) (w : W) (k : KG ε) : Z :=
  ⟪T (toMK k) e, w⟫_ℂ • S (toMK k) f

theorem avgF_continuous {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Continuous (avgF (ε := ε) T S e f w) := by
  have h1 : Continuous fun k : KG ε => T (toMK k) e :=
    (hT.2.2 e).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  have h2 : Continuous fun k : KG ε => S (toMK k) f :=
    (hS.2.2 f).comp_continuous (avg_continuous_toMK ε) fun k => k.2
  exact (h1.inner continuous_const).smul h2

theorem avgF_integrable {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : Integrable (avgF (ε := ε) T S e f w) (muK ε) := by
  have := avg_secondCountable ε
  exact integrableOn_univ.1 ((avgF_continuous hT hS e f w).continuousOn.integrableOn_compact isCompact_univ)

def avgMapL {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z) :
    W →ₗ[ℂ] Z where
  toFun w := ∫ k, avgF T S e f w k ∂(muK ε)
  map_add' x y := by
    rw [← integral_add (avgF_integrable hT hS e f x) (avgF_integrable hT hS e f y)]
    congr 1; funext k; simp [avgF, inner_add_right, add_smul]
  map_smul' c x := by
    rw [RingHom.id_apply, ← integral_smul]
    congr 1; funext k; simp [avgF, inner_smul_right, smul_smul]

theorem avgMapL_apply {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (w : W) : avgMapL hT hS e f w = ∫ k, avgF T S e f w k ∂(muK ε) := rfl

theorem avgMapL_intertwines {T : Mat n → (W →L[ℂ] W)} {S : Mat n → (Z →L[ℂ] Z)}
    (hT : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T) (hS : Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S) (e : W) (f : Z)
    (g : KG ε) (w : W) : avgMapL hT hS e f (T (toMK g) w) = S (toMK g) (avgMapL hT hS e f w) := by
  rw [avgMapL_apply, avgMapL_apply, ← (S (toMK g)).integral_comp_comm (avgF_integrable hT hS e f w),
    ← integral_mul_left_eq_self _ g]
  congr 1; funext k
  have hm : toMK (g * k) = toMK g * toMK k := rfl
  simp only [avgF, hm, hT.1.2 _ g.2 _ k.2, hS.1.2 _ g.2 _ k.2, ContinuousLinearMap.comp_apply, map_smul]
  rw [avg_inner_map (hT.2.1 _ g.2)]

end

theorem tracePairing_nonzero_intertwiner : AvgMap := by
  intro n ε W _ _ _ T Z _ _ _ S Γ hT hS hne
  classical
  set b := stdOrthonormalBasis ℂ W
  set c := stdOrthonormalBasis ℂ Z
  let φ : Fin (Module.finrank ℂ Z) → Z →L[ℂ] ℂ := fun j =>
    LinearMap.toContinuousLinearMap ((innerₛₗ ℂ (c j)).comp Γ)
  have hφ : ∀ j u, φ j u = ⟪c j, Γ u⟫_ℂ := fun j u => rfl
  have hpt : ∀ i j (k : KG ε), φ j (avgF T S (b i) (c j) (b i) k) =
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
    intro i j k
    simp [avgF, hφ, map_smul, inner_conj_symm]
  have hint : ∀ i j, Integrable (fun k : KG ε =>
      conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ) (muK ε) := fun i j =>
    ((φ j).integrable_comp (avgF_integrable hT hS (b i) (c j) (b i))).congr
      (Filter.Eventually.of_forall fun k => hpt i j k)
  have key : ∀ i j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ =
      ∫ k, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ ∂(muK ε) := by
    intro i j
    rw [avgMapL_apply, ← hφ, ← (φ j).integral_comp_comm (avgF_integrable hT hS _ _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => hpt i j k)
  have hsum : ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) =
      ∑ i, ∑ j, ⟪c j, Γ (avgMapL hT hS (b i) (c j) (b i))⟫_ℂ := by
    simp only [key]
    have hpw : ∀ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) =
        ∑ i, ∑ j, conj ⟪b i, T (toMK k) (b i)⟫_ℂ * ⟪c j, Γ (S (toMK k) (c j))⟫_ℂ := by
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [trK, LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ c, map_sum,
        Finset.sum_mul, Finset.mul_sum, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact Finset.sum_comm
    simp_rw [hpw]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
  rw [hsum] at hne
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  refine ⟨avgMapL hT hS (b i) (c j), fun h0 => hj ?_, fun k hk v => ?_⟩
  · rw [h0, LinearMap.zero_apply, map_zero, inner_zero_right]
  · have hk' : k ∈ Set.range (fun g : KG ε => toMK g) := by rw [Formalism.REAL.range_toMK]; exact hk
    obtain ⟨g, rfl⟩ := hk'
    exact avgMapL_intertwines hT hS (b i) (c j) g v

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexGermCongr
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem curvAt_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G G' : V n → Matrix r r ℂ} {v : V n}
    (h : G =ᶠ[𝓝 v] G') : curvAt G v = curvAt G' v := by
  funext a b
  exact curv_congr h _ _

theorem cutForm_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : cutForm ρ G₀ G₁ v = cutForm ρ' G₀' G₁' v := by
  funext a b
  have hc : (fun x => (ρ x : ℂ)) =ᶠ[𝓝 v] fun x => (ρ' x : ℂ) := hρ.mono fun x hx => by simp only [hx]
  simp only [cutForm]
  rw [dbar_congr hc, conn_congr h₀, conn_congr h₁]

theorem corrC_germ_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ ρ' : V n → ℝ}
    {G₀ G₁ G₀' G₁' : V n → Matrix r r ℂ} {v : V n} (hρ : ρ =ᶠ[𝓝 v] ρ') (h₀ : G₀ =ᶠ[𝓝 v] G₀')
    (h₁ : G₁ =ᶠ[𝓝 v] G₁') : corrC ρ G₀ G₁ v = corrC ρ' G₀' G₁' v := by
  simp only [corrC]
  rw [curvAt_germ_congr h₀, curvAt_germ_congr h₁, cutForm_germ_congr hρ h₀ h₁]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFunc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc :
    ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L)
      (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L →
      j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d →
      Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  intro F k L _ _ _ _ _ α j d hα hj hd
  let jF : L →ₐ[F] RatFunc k :=
    { j with
      commutes' := fun x => by
        show j (algebraMap F L x) = algebraMap k (RatFunc k) (algebraMap F k x)
        rw [← hα, ← hj]; rfl }
  have h1 : Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) :=
    trdeg_le_of_injective jF j.injective
  have hR : Algebra.trdeg k (RatFunc k) = 1 := by
    have : Algebra.IsAlgebraic (Polynomial k) (RatFunc k) :=
      IsLocalization.isAlgebraic (RatFunc k) (nonZeroDivisors (Polynomial k))
    rw [← trdeg_add_eq k (Polynomial k), trdeg_eq_zero (R := Polynomial k) (A := RatFunc k),
      add_zero, Polynomial.trdeg_of_isDomain]
  have h2 := trdeg_add_eq F k (A := RatFunc k)
  calc Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) := h1
    _ = ((d + 1 : ℕ) : Cardinal) := by rw [← h2, hR, hd]; push_cast; rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G] [TopologicalSpace G]

def twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq_finsum_twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), twTerm θ K δ f (Quotient.out q) :=
  rfl

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwSubISupInfLevel
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dualLab_dualLab' (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]

section Tw
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool)

theorem twSub_map (V : Submodule ℂ E) : V.map (Tw.mkL s E) = Tw.sub s V := by
  ext x
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun hx => ⟨Tw.out x, hx, rfl⟩⟩

theorem twSub_iSup {C : Type} (S : C → Prop) (V : C → Submodule ℂ E) :
    Tw.sub s (⨆ (c : C) (_ : S c), V c) = ⨆ (c : C) (_ : S c), Tw.sub s (V c) := by
  rw [← twSub_map, Submodule.map_iSup]
  refine iSup_congr fun c => ?_
  rw [Submodule.map_iSup]
  refine iSup_congr fun _ => ?_
  exact twSub_map s (V c)

theorem twSub_finrank (V : Submodule ℂ E) : Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  unfold Module.finrank
  congr 1
  symm
  exact rank_eq_of_equiv_equiv (cj s)
    (show V ≃+ Tw.sub s V from
      { toFun := fun x => ⟨Tw.mk s x.1, x.2⟩
        invFun := fun x => ⟨Tw.out x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl })
    (Function.Involutive.bijective (cj_cj s))
    (fun r m => Subtype.ext ((Tw.mkL s E).map_smulₛₗ r m.1))

theorem twSub_le {V V' : Submodule ℂ E} (h : V ≤ V') : Tw.sub s V ≤ Tw.sub s V' := fun _ hx => h hx

theorem twSub_stable {G : Type} [Group G] (ρ : Representation ℂ G E) (V : Submodule ℂ E)
    (h : ∀ g, V.map (ρ g) ≤ V) (g : G) : (Tw.sub s V).map (Tw.rep s ρ g) ≤ Tw.sub s V := by
  rintro _ ⟨x, hx, rfl⟩
  exact h g ⟨Tw.out x, hx, rfl⟩

end Tw

theorem twSub_iSup_inf_level {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) {G : Type} [Group G] [Fintype G]
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* ℂˣ) {C : Type} (S : C → Prop) (U : C → Submodule ℂ E)
    (B Lev : Submodule ℂ E) (hUB : ∀ c, U c ≤ B) (hstab : ∀ c g, (U c).map (ρ g) ≤ U c)
    (hLev : Tw.sub s Lev = Tw.sub s B ⊓
      ⨅ h : P, LinearMap.ker (Tw.rep s ρ (h : G) - ((ψ h : ℂˣ) : ℂ) • LinearMap.id)) :
    Tw.sub s (⨆ (c : C) (_ : S c), U c) ⊓ Tw.sub s Lev = Tw.sub s (⨆ (c : C) (_ : S c), U c ⊓ Lev) := by
  rw [twSub_iSup, hLev, ← inf_assoc, inf_eq_left.2 (iSup₂_le fun c _ => twSub_le s (hUB c)),
    GlobalTheory.iSup_stable_inf_typeSpace (Tw.rep s ρ) P ψ _ S (fun c g => twSub_stable s ρ _ (hstab c) g), twSub_iSup]
  refine iSup_congr fun c => iSup_congr fun _ => ?_
  show _ = Tw.sub s (U c) ⊓ Tw.sub s Lev
  rw [hLev, ← inf_assoc, inf_eq_left.2 (twSub_le s (hUB c))]

open Classical in
theorem evC_single {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) :
    GlobalTheory.Hk3.evC V P a (Finsupp.single d 1) = if IsLab V P d then a d else 0 := by
  unfold GlobalTheory.Hk3.evC
  rw [Finsupp.sum_single_index]
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem dimParts_of_schur {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ} (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt)
    (hX : GoodStable A3.A.X) (hD : GlobalTheory.CuspMult.CuspDecomp D) (hM : GlobalTheory.CuspMult.MultEq R.toRealDat)
    (hU : R.toRealDat.LUnif) (hS : SchurAll R.toRealDat) : (R.toCx3 F).DimParts false := by
  obtain ⟨hC, hSF, hEE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE, -, -, -, hEev, hEchar⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hC hS R.SF hSF
  intro j p
  obtain ⟨hWo, -, -, -, hWtop, hWstab, hWev, hWchar⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hC hS hIrr R.SF hSF j
  have hI := (GlobalTheory.Hk3.eH_laws R.toRealDat F.lv2 hC hIrr j).1
  have hlab : ∀ P d, Good R.toRealDat A3.A.μ0 P → (IsLab (Wc D j) P d ↔ IsLab (Yc D 0) P (dualLab d)) :=
    fun P d hP => (_root_.GlobalTheory.LabEq.isLab_W_iff (s := 0) R.toRealDat F.lv2 hC j P d hP).1
  let LevW : Submodule ℂ (R.HW j (sg0 D A3.A)).H :=
    (R.toRealDat.Wat j (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW j (sg0 D A3.A)).e
  let LevE : Submodule ℂ R.HE.H := (R.toRealDat.EEat (R.toRealDat.levR F.lv2 false)).comap R.HE.e
  have hWle : ∀ c, Wcc R.toRealDat R.SF j c ≤ LinearMap.range (eH R.toRealDat j) := fun c =>
    hWtop ▸ le_iSup (fun c => Wcc R.toRealDat R.SF j c) c
  have hr1 : LinearMap.range ((R.toCx3 F).w0C false j) = Tw.sub (twAt D.what₂.embLL A3.A.v0) LevW :=
    _root_.GlobalTheory.LevelRange.range_w0C_eq R F hOk hW hU false j
  have hr2 := _root_.GlobalTheory.WType.range_w0C_type R F hOk hW hEx hU j
  have hWside : (R.toCx3 F).Wp j p ⊓ LinearMap.range ((R.toCx3 F).w0C false j) =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c ⊓ LevW) := by
    have e0 : (R.toCx3 F).Wp j p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), Wcc R.toRealDat R.SF j c) := by
      show Tw.sub _ (R.Wp3 j p) = _
      unfold RealDat3.Wp3
      simp only [hWc]
    rw [e0, hr1]
    exact twSub_iSup_inf_level _ (R.gW j (sg0 D A3.A)) F.P0 ((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0⁻¹)
      (R.Carries p) _ _ LevW hWle hWstab (hr1.symm.trans hr2)
  have hEside : (R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false =
      Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c ⊓ LevE) := by
    have e0 : (R.toCx3 F).EEp p = Tw.sub (twAt D.what₂.embLL A3.A.v0)
        (⨆ (c : Pl D.host.E → List ℤ → ℂ) (_ : R.Carries p c), EEc R.toRealDat R.SF c) := by
      show Tw.sub _ (R.EEp3 p) = _
      unfold RealDat3.EEp3
      simp only [hEE]
    have hl : Tw.sub (twAt D.what₂.embLL A3.A.v0) LevE = Tw.sub (twAt D.what₂.embLL A3.A.v0) ⊤ ⊓
        ⨅ h : F.P0, LinearMap.ker (Tw.rep (twAt D.what₂.embLL A3.A.v0) R.gE (h : G) -
          ((((Units.map A3.A.fam.v0.embedding.toMonoidHom).comp F.ψ0) h : ℂˣ) : ℂ) • LinearMap.id) := by
      have := (_root_.GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hW).1
      refine this.trans ?_
      ext x
      exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
    rw [e0]
    exact twSub_iSup_inf_level _ R.gE F.P0 _ (R.Carries p) _ ⊤ LevE (fun _ => le_top)
      (fun c g => _root_.GlobalTheory.RowPartStable.map_gE_le (s := 0) R.toRealDat F.lv2 hC R.SF hSF c g) hl
  rw [hWside, hEside]
  refine (twSub_finrank (E := (R.HW j (sg0 D A3.A)).H) _ _).trans (Eq.trans ?_ (twSub_finrank (E := R.HE.H) _ _).symm)
  have hWfix : ∀ c, ∀ x ∈ Wcc R.toRealDat R.SF j c, eH R.toRealDat j x = x := by
    intro c x hx
    obtain ⟨y, rfl⟩ := hWle c hx
    rw [← Module.End.mul_apply, hI]
  let I := {x : Pl D.host.E × List ℤ // Good R.toRealDat A3.A.μ0 x.1 ∧ IsLab (Wc D j) x.1 x.2}
  let lab : (Pl D.host.E → List ℤ → ℂ) → I → ℂ := fun c i => c i.1.1 i.1.2
  have hEle : ∀ c c', lab c = lab c' → EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
    intro c c' hcc x hx
    refine hEchar c' x fun P d hP hd => ?_
    rw [hEev c P hP _ x hx, evC_single, if_pos hd]
    have hl : IsLab (Wc D j) P (dualLab d) := (hlab P (dualLab d) hP).2 (by rwa [dualLab_dualLab'])
    exact congrArg (· • x) (congrFun hcc ⟨(P, dualLab d), hP, hl⟩)
  have hWcle : ∀ c c', lab c = lab c' → Wcc R.toRealDat R.SF j c ≤ Wcc R.toRealDat R.SF j c' := by
    intro c c' hcc x hx
    refine hWchar c' x (hWfix c x hx) fun P d hP hd => ?_
    rw [hWev c P hP _ x hx, evC_single, if_pos hd]
    exact congrArg (· • x) (congrFun hcc ⟨(P, d), hP, hd⟩)
  symm
  refine GlobalTheory.finrank_iSup_joint_eigen_eq (I := I)
    (fun i => hE i.1.1 (Finsupp.single (dualLab i.1.2) 1)) (fun i => hWo i.1.1 (Finsupp.single i.1.2 1))
    (fun c => EEc R.toRealDat R.SF c ⊓ LevE) (fun c => Wcc R.toRealDat R.SF j c ⊓ LevW) lab ?_ ?_ ?_ ?_ (R.Carries p)
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hEev c P hP _ x hx.1, evC_single, if_pos ((hlab P d hP).1 hd), dualLab_dualLab']
  · rintro c x hx ⟨⟨P, d⟩, hP, hd⟩
    rw [hWev c P hP _ x hx.1, evC_single, if_pos hd]
  · intro c c' hcc
    rw [le_antisymm (hEle c c' hcc) (hEle c' c hcc.symm), le_antisymm (hWcle c c' hcc) (hWcle c' c hcc.symm)]
    exact ⟨rfl, rfl⟩
  · intro c
    exact (_root_.GlobalTheory.DimFull.dim_parts_full R.toRealDat F.lv2 hOk.ok2 hC hS hX hD hM R.SF hSF F.P0 F.ψ0 j c).symm

end GlobalTheory.DimPartsFull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc

theorem intertwiner_eq_zero_of_isCoprime {K : Type} [Field K] {a b : ℕ}
    (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K)
    (hc : IsCoprime A.charpoly B.charpoly) (hC : C * A = B * C) : C = 0 := by
  first
  | exact @_root_.GlobalTheory.IntertwiningOperators.main
  | exact _root_.GlobalTheory.IntertwiningOperators.main
  | (apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningOperators.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningOperators.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningOperators.main ..)

theorem twCent_blk_le_parP : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable →
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) ≤ GlobalTheory.LeviDesc.parP a n w := by
  intro E _ _ n a b h w m hsep g hg
  have hcop := hsep.isCoprime
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dite_eq_left hM]
    rfl
  rw [Matrix.mul_zero] at hval
  have hc : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (blk h w m 0 : GLw n w) =
      ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * g := by
    have := congrArg Units.val (show g * blk h w m 0 = blk h w m 0 * MonoidHom.id _ g from hg)
    simpa using this
  rw [hval] at hc
  set e := finSumFinEquiv.trans (finCongr h) with he
  set g' := Matrix.reindex e.symm e.symm (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hg'
  have hgg : (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.reindex e e g' := by
    simp [hg']
  rw [hgg, ← Matrix.fromBlocks_toBlocks g'] at hc
  have hc2 := congrArg (Matrix.reindex e.symm e.symm) hc
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix,
    Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply] at hc2
  rw [Matrix.fromBlocks_inj] at hc2
  have hC : g'.toBlocks₂₁ * m.1.val = m.2.val * g'.toBlocks₂₁ := by
    have := hc2.2.2.1
    simpa using this
  have hC0 := intertwiner_eq_zero_of_isCoprime _ _ _ hcop hC
  show (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)).BlockTriangular fun i : Fin n => decide (a ≤ (i : ℕ))
  intro i j hij
  have hi : a ≤ (i : ℕ) := by
    by_contra hc'
    revert hij
    simp only [hc', decide_false]
    cases decide (a ≤ (j : ℕ)) <;> decide
  have hj : ¬ a ≤ (j : ℕ) := by
    intro hc'
    revert hij
    simp only [hc', decide_true]
    cases decide (a ≤ (i : ℕ)) <;> decide
  have hie : i = e (Sum.inr ⟨(i : ℕ) - a, by omega⟩) := by
    ext; simp [he]; omega
  have hje : j = e (Sum.inl ⟨(j : ℕ), by omega⟩) := by
    ext; simp [he]
  rw [hgg, hie, hje]
  have : g'.toBlocks₂₁ ⟨(i : ℕ) - a, by omega⟩ ⟨(j : ℕ), by omega⟩ = 0 := by rw [hC0]; rfl
  simpa [Matrix.toBlocks₂₁] using this

end GlobalTheory.LeviDesc
end
end

