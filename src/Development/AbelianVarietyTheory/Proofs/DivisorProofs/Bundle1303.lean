module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1278
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMultiplicationFlatColumnsEval
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort.ColEval

theorem word_succ {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) {t : ℕ} (u : Fin (t + 1) → Fin N → K) :
    word mul u = mul (u 0) * word mul (fun i => u i.succ) := by
  simp [word, List.ofFn_succ]

theorem mul_eq_sum {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (v : Fin N → K) :
    mul v = ∑ k, v k • mul (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

variable {F A : Type} [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A]
  [IsScalarTower (𝓞 F) F A] {S : Sys F A} {E A' : Type} [Field E] [Algebra F E] [AddCommGroup A'] [Module E A']
  {s : Fin S.D → Fin S.N → E} {δ : ℕ}

theorem mul_single_ι (Φ : S.Flat E A' s δ) (k : Fin S.N) (y : A) :
    Φ.mul (Pi.single k 1) (Φ.ι y) = Φ.ι (S.mul (Pi.single k 1) y) := by
  rw [← Φ.mul_ι]
  congr 2
  ext j
  by_cases h : j = k
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem word_ι_expand (Φ : S.Flat E A' s δ) : ∀ (t : ℕ) (U : Fin t → Fin S.N → E) (z : A),
    word Φ.mul U (Φ.ι z) =
      ∑ e : Fin t → Fin S.N, (∏ q, U q (e q)) • Φ.ι (word S.mul (fun q => Pi.single (e q) (1 : F)) z)
  | 0, U, z => by simp [word]
  | t + 1, U, z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [word_succ, Module.End.mul_apply, word_ι_expand Φ t, map_sum]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => Fin S.N).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, word_succ,
      Module.End.mul_apply, map_smul, mul_eq_sum Φ.mul (U 0), LinearMap.sum_apply, LinearMap.smul_apply,
      mul_single_ι, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun e _ => ?_
    rw [mul_comm]

end GlobalTheory.HSShort.ColEval

namespace GlobalTheory.HSShort.ColEval

theorem columns_eval : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A), S.Hyp → ∀ (E A' : Type) [Field E] [Algebra F E] [AddCommGroup A'] [Module E A'] (s : Fin S.D → Fin S.N → E) (δ : ℕ) (Φ : S.Flat E A' s δ) (d : ℕ) (b : Module.Basis (Fin d) F (S.V S.T)) (c : Fin d → A →ₗ[F] F), S.IsCo b c → ∃ c' : Fin d → A' →ₗ[E] E, (∀ x ∈ Submodule.span E (Φ.ι '' S.V S.T), ∑ i, c' i x • Φ.ι (b i) = x) ∧ ∀ (κ : S.Col) (u : Fin (S.D + 1) × Fin S.N → E), word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x) ∈ Submodule.span E (Φ.ι '' S.V S.T) ∧ ∀ i, aeval u (coordP S.mul (c i) κ.β (κ.x : A)) = c' i (word Φ.mul (fun q k => u (κ.β q, k)) (Φ.ι κ.x)) := by
  intro F A _ _ _ _ _ _ S hS E A' _ _ _ _ s δ Φ d b c hc
  set W := Submodule.span E (Φ.ι '' (S.V S.T : Set A)) with hW
  have hli : LinearIndependent E (fun i => Φ.ι (b i)) := Φ.indep d b b.linearIndependent
  have hιV : ∀ (y : A) (hy : y ∈ S.V S.T), Φ.ι y = ∑ i, algebraMap F E (b.repr ⟨y, hy⟩ i) • Φ.ι (b i) := by
    intro y hy
    conv_lhs => rw [show y = ((⟨y, hy⟩ : S.V S.T) : A) from rfl, ← b.sum_repr ⟨y, hy⟩]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Submodule.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, LinearMap.map_smulₛₗ]
  have hWspan : W = Submodule.span E (Set.range fun i => Φ.ι (b i)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      rw [hιV y hy]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((Finsupp.linearEquivFunOnFinite E E (Fin d)).toLinearMap ∘ₗ (hli.repr ∘ₗ Submodule.inclusion (le_of_eq hWspan)))
  have h1 : ∀ x ∈ W, ∑ i, g x i • Φ.ι (b i) = x := by
    intro x hx
    have hx' : x ∈ Submodule.span E (Set.range fun i => Φ.ι (b i)) := hWspan ▸ hx
    have e1 := LinearMap.congr_fun hg ⟨x, hx⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe] at e1
    rw [e1, show Submodule.inclusion (le_of_eq hWspan) ⟨x, hx⟩ = ⟨x, hx'⟩ from rfl]
    have e2 := hli.linearCombination_repr ⟨x, hx'⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e2
    simpa using e2
  have h2 : ∀ x ∈ W, ∀ a : Fin d → E, ∑ i, a i • Φ.ι (b i) = x → ∀ i, g x i = a i := by
    intro x hx a ha
    have h0 : ∑ i, (g x i - a i) • Φ.ι (b i) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, h1 x hx, ha, sub_self]
    intro i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 i)
  have h3 : ∀ (y : A) (hy : y ∈ S.V S.T) i, g (Φ.ι y) i = algebraMap F E (c i y) := by
    intro y hy i
    rw [h2 _ (Submodule.subset_span ⟨y, hy, rfl⟩) _ (hιV y hy).symm i]
    congr 1
    exact (hc i ⟨y, hy⟩).symm
  refine ⟨fun i => LinearMap.proj i ∘ₗ g, fun x hx => h1 x hx, fun κ u => ?_⟩
  have hmem : ∀ e : Fin κ.t → Fin S.N, word S.mul (fun q => Pi.single (e q) (1 : F)) (κ.x : A) ∈ S.V S.T := by
    intro e
    have := (GlobalTheory.HSShort.wordMem F A S hS κ.j κ.t (by rw [κ.add])).1 (fun q => Pi.single (e q) (1 : F)) κ.x κ.x.2
    rwa [κ.add] at this
  rw [word_ι_expand Φ κ.t]
  refine ⟨Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hmem e, rfl⟩), fun i => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordP, map_sum, map_mul, aeval_C, map_prod, aeval_X, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.map_smul, LinearMap.coe_proj, Function.eval, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [h3 _ (hmem e) i, mul_comm]

end GlobalTheory.HSShort.ColEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTraceFormLattice
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem latEmb_model_of_eq (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (j : ℕ) (hj : InR D j)
    (hrt : (H.rt : D.host.E) = D.host.sqrtMinusD) (hrt0 : H.rt0 = D.host.φ₀ D.host.sqrtMinusD)
    (hp : Dw.p = (D.R.sigW j).1) (hq : Dw.q = (D.R.sigW j).2) (V : HSp D) (hV : V = D.sp.W j) (r : ℕ)
    (hr : V.rank = r) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (hL : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀))
    (hI : LatIsom V Dw.EF (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀)) :
    Function.Injective ι₀ ∧ Submodule.span D.host.E (Set.range ι₀) = ⊤ ∧
      ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
        herm (GlobalTheory.RecDict.gmW V hr) (ι₀ x) (ι₀ y)) := by
  subst hV
  subst hr
  have hL' : LatEmb (D.sp.W j) ι₀ := hL
  obtain ⟨ε, hε⟩ : LatIsom (D.sp.W j) Dw.EF ι₀ := hI
  have hsp : Submodule.span D.host.E (Set.range ι₀) = ⊤ := by
    rw [← LinearMap.coe_range, hL'.2]
    exact (GlobalTheory.Member.latG_lattice_and_completion D (D.sp.W j) 1).2.1
  let f := ((D.sp.W j).frame.equivFun.symm.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hsp' : Submodule.span D.host.E (Set.range (f ∘ₗ ι₀)) = ⊤ := by
    have : Set.range (f ∘ₗ ι₀) = (D.sp.W j).frame.equivFun.symm.toLinearMap '' Set.range ι₀ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hsp, Submodule.map_top, LinearEquiv.range]
  have h1 : ε = 1 := GlobalTheory.Member.sign_eq_one D H Dw j hj hrt hrt0 hp hq (f ∘ₗ ι₀) ε
    ((D.sp.W j).frame.equivFun.symm.injective.comp hL'.1) hsp' hε
  subst h1
  refine ⟨hL'.1, hsp, (GlobalTheory.Member.isom_iff_model Dw (D.sp.W j) rfl ι₀).1 fun x y => ?_⟩
  rw [hε x y, Units.val_one, Int.cast_one, _root_.one_mul]


set_option maxHeartbeats 2000000 in
theorem model_space_of_lawsJ : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, (∀ τ : D.host.E →+* ℂ, τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 → (τ ((T.U j σ).X k).ξ0).im < 0) ∧ ∃ φD : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E), Function.Injective φD ∧ Submodule.span D.host.E (Set.range φD) = ⊤ ∧ ∀ x y, (((T.Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-((T.U j σ).X k).ξ0 * herm ((T.U j σ).X k).Gm (φD x) (φD y)) := by
  intro D T h j hj σ hσ k
  obtain ⟨hr, hW⟩ := h.modelW j hj σ hσ
  obtain ⟨-, hrt, hrt0, -⟩ := h.pins.1
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨hr', -, -, -, -, -, -, hL, hI, -⟩ := h.adPin j hj σ hσ
  refine ⟨fun τ hτ => ?_, T.iota j, ?_⟩
  · rw [(hW k).2]
    exact GlobalTheory.Member.hostCMType_neg_constant_im_neg D τ (by rw [← hrt0, ← hrt, hτ])
  · rw [(hW k).1, (hW k).2]
    exact latEmb_model_of_eq D T.Q.H (T.Q.Dw j) j hj hrt hrt0 hp hq (T.V j σ) (h.spaceW j hj σ hσ) D.R.r hr
      (T.iota j) hL hI

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherCohomologyBoundTwistNegOfRegularSection
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem higherCohomology_bound_twist_neg_of_regular_section : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ j, 0 < j → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist E (lbPow L m)) j ≤ C * (d * (m + 1) ^ (d - 1)))) → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → ∀ (B : LB X) (hB : B.IsLB) (s : B.Sec), Mono (cutHom F hB s) → (∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → ∀ i, 0 < i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist (twistZ F B (-1)) (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  intro k _ _ X _ hX d L hL ih F _ hF B hB s hs hb i hi
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hX
  have hcut : suppDim (cut F hB s) ≤ (d : ℕ) := suppDim_cut_le F hB s hF
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 : ∃ C : ℕ, ∀ m : ℕ,
      hdim k (twist (cut F hB s) (lbPow L m)) j ≤ C * ((d + 1) * (m + 1) ^ d) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨C, hC⟩ := GlobalTheory.T.global_sections_polynomial_growth k X hX d L hL (cut F hB s) hcut
      exact ⟨C, fun m => (hC m).trans
        (Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.succ_pos d)))⟩
    · obtain ⟨C, hC⟩ := ih (cut F hB s) hcut j hj
      exact ⟨C, fun m => (hC m).trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.le_succ d)
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.sub_le d 1))))⟩
  obtain ⟨C₁, hC₁⟩ := h1
  obtain ⟨C₂, hC₂⟩ := hb (j + 1) hi
  refine ⟨C₁ + C₂, fun m => ?_⟩
  have hM : (lbPow L m).IsLB := isLB_lbPow hL m
  have hB' := Twist.isLB_lbZPow hB (-1)
  obtain ⟨M', hM', e'⟩ := cls_surj (cls _ hB' + cls _ hM)
  obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq F hB' hM hM' e'
  have key := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B (lbPow L m) M' hB hM hM' s hs (by
    rw [e', cls_lbZPow hB (-1) hB']
    simp [add_comm, add_left_comm, add_assoc])).2.1 j
  have e2 : hdim k (twist (twistZ F B (-1)) (lbPow L m)) (j + 1) = hdim k (twist F M') (j + 1) :=
    hdim_congr k _ e
  rw [e2, add_mul]
  exact key.trans (Nat.add_le_add (hC₁ m) (hC₂ m))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelLatticeSystemHyp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SysHyp

variable {F : Type} [Field F] [NumberField F]

theorem mulW_comm (G : Geo F) (j : ℕ) (u v : Fin G.N → F) (m : G.Sec j) :
    G.mulW (j + 1) u (G.mulW j v m) = G.mulW (j + 1) v (G.mulW j u m) := by
  simp only [Geo.mulW_apply]
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun i c y hy hi hc => ?_
  rw [germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc,
    germ_mulSec _ _ _ _ _ _ _ _ _ hi hc, germ_mulSec _ _ _ _ _ _ _ _ _ hi hc]
  exact mul_left_comm _ _ _

theorem shift_comm (G : Geo F) (u v : Fin G.N → F) : shift G u * shift G v = shift G v * shift G u := by
  refine LinearMap.ext fun x => funext fun j => ?_
  rcases j with _ | _ | j
  · rfl
  · change G.mulW 0 u 0 = G.mulW 0 v 0
    rw [map_zero, map_zero]
  · exact mulW_comm G j u v (x j)

theorem shift_single (G : Geo F) (j : ℕ) (u : Fin G.N → F) (m : G.Sec j) :
    shift G u (Pi.single j m) = Pi.single (j + 1) (G.mulW j u m) := by
  funext l
  rcases l with _ | l
  · rw [Pi.single_eq_of_ne (Nat.succ_ne_zero j).symm]
    rfl
  · change G.mulW l u ((Pi.single j m : Tot G) l) = _
    by_cases h : l = j
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun e => h (Nat.succ_injective e)), map_zero]

variable (X : Data F)

theorem coe_inclEquiv (j : ℕ) (x : X.V j) :
    (inclEquiv X j x : Tot X.toGeo) = Pi.single j (x : X.Sec j) := rfl

theorem coe_eq_single (j : ℕ) (x : LinearMap.range (incl X j)) :
    (x : Tot X.toGeo) = Pi.single j ((inclEquiv X j).symm x : X.Sec j) := by
  rw [← coe_inclEquiv, LinearEquiv.apply_symm_apply]

theorem isFull (Λ₀ : ℝ) (j : ℕ) : IsFull ((sysOf X Λ₀).M j) := by
  refine ⟨(X.full j).fg.map _, ?_⟩
  change Submodule.span F ((inclEquiv X j).toLinearMap '' (X.M j : Set (X.V j))) = ⊤
  rw [← Submodule.map_span, (X.full j).span, Submodule.map_top, LinearEquiv.range]

theorem short (Λ₀ : ℝ) {j : ℕ} {Λ : ℝ} (h : X.ShortFamily j Λ) : (sysOf X Λ₀).Short j Λ := by
  obtain ⟨v, hm, hi, hn⟩ := h
  have hs : ⊤ ≤ Submodule.span F (Set.range v) :=
    (hi.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, X.latRank_M])).ge
  refine ⟨_, (Module.Basis.mk hi hs).map (inclEquiv X j), fun i => ?_⟩
  have e : (Module.Basis.mk hi hs).map (inclEquiv X j) i = inclEquiv X j (v i) := by
    rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  refine e ▸ ⟨⟨v i, hm i, rfl⟩, fun σ => ?_⟩
  change (X.nm j).nrm σ ((inclEquiv X j).symm (inclEquiv X j (v i))) ≤ Λ
  rw [LinearEquiv.symm_apply_apply]
  exact hn i σ

end GlobalTheory.HSShort.SysHyp

namespace GlobalTheory.HSShort

open SysHyp

theorem GeoHyp.sysOf_hyp : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ),
    GeoHyp X Λ₀ → (sysOf X Λ₀).Hyp := by
  intro F _ _ X Λ₀ h
  have := h.totallyComplex
  refine ⟨X.geom.alg.variety.one_le, X.le_T, ⟨?_, X.geom.alg.spans, X.herm, fun k σ => h.normsLe k σ, h.one_le_Lam⟩,
    shift_comm X.toGeo, fun j _ => isFull X Λ₀ j, ?_, ?_, X.one_le_beta, h.hermSysHyp_one_le_lambdaZero, X.one_le_LamD, X.one_le_LamT,
    short X Λ₀ h.short0, short X Λ₀ h.shortD, short X Λ₀ h.shortT⟩
  · obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (X.geom.alg.bpf.ge (Set.mem_univ (genericPoint X.Y)))
    exact j.pos
  · rintro j hj k _ ⟨f, hf, rfl⟩
    obtain ⟨g, hg, e⟩ := h.mulStable j hj (X.w.col k) (Submodule.subset_span ⟨k, rfl⟩) f hf
    refine ⟨inclEquiv X (j + 1) g, ⟨g, hg, rfl⟩, ?_⟩
    exact ((shift_single X.toGeo j _ f).trans (congrArg (Pi.single (M := fun l => X.Sec l) (j + 1)) e.symm)).symm
  · intro σ j hj u m c f g e
    refine h.mulBound.mulBoundAt σ j hj u m c (fun i => (inclEquiv X j).symm (f i))
      (fun t => (inclEquiv X (j + 1)).symm (g t)) fun k i => ?_
    have e₁ := (coe_eq_single X (j + 1) (g (k, i))).symm.trans ((e k i).trans
      ((congrArg (shift X.toGeo (Pi.single k 1)) (coe_eq_single X j (f i))).trans (shift_single X.toGeo j _ _)))
    exact Pi.single_injective (M := fun l => X.Sec l) (j + 1) e₁

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelSectionBaseChangeProperties
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort

section Lemmas

variable {F : Type} [Field F] [NumberField F] (G : Geo F)

theorem shift_apply_zero (u : Fin G.N → F) (x : Tot G) : shift G u x 0 = 0 := rfl

theorem shift_apply_succ (u : Fin G.N → F) (x : Tot G) (j : ℕ) : shift G u x (j + 1) = G.mulW j u (x j) := rfl

variable (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem totExt_apply (x : Tot G) (j : ℕ) : totExt G E x j = G.toExt E j (x j) := rfl

theorem totExt_single (j : ℕ) (s : G.Sec j) :
    totExt G E (Pi.single j s) = Pi.single j (G.toExt E j s) := by
  funext k
  rw [totExt_apply]
  by_cases h : k = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem shift_totExt (u : Fin G.N → F) (x : Tot G) :
    shift (G.baseChange E) (fun k => algebraMap F E (u k)) (totExt G E x) = totExt G E (shift G u x) := by
  funext j
  cases j with
  | zero => rw [shift_apply_zero, totExt_apply, shift_apply_zero, map_zero]
  | succ j =>
    rw [shift_apply_succ, totExt_apply, totExt_apply, shift_apply_succ, Geo.toExt_mulW]
    rfl

end Lemmas

theorem totExt_props : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (Λ₀ : ℝ) (E : Type) [Field E] [NumberField E] [Algebra F E], (∀ (m : ℕ) (v : Fin m → (sysOf X Λ₀).V X.T), LinearIndependent F v → LinearIndependent E fun i => totExt X.toGeo E (v i)) ∧ (∀ u x, shift (X.toGeo.baseChange E) (fun k => algebraMap F E (u k)) (totExt X.toGeo E x) = totExt X.toGeo E (shift X.toGeo u x)) ∧ ∀ j, Submodule.span E (totExt X.toGeo E '' (sysOf X Λ₀).V j) = LinearMap.range (incl (X.baseChange E) j) := by
  intro F _ _ X Λ₀ E _ _ _
  refine ⟨?_, fun u x => shift_totExt X.toGeo E u x, ?_⟩
  · intro m v hv
    have hv' := hv.map' ((sysOf X Λ₀).V X.T).subtype (Submodule.ker_subtype _)
    have hform : ∀ i, ∃ y : X.toGeo.Sec X.T, (v i : Tot X.toGeo) = Pi.single X.T y := by
      intro i
      obtain ⟨y, hy⟩ := (v i).2
      exact ⟨y, hy.symm⟩
    choose f hf using hform
    have h1 : LinearIndependent F (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) := by
      have e : (LinearMap.single F (fun k => X.toGeo.Sec k) X.T ∘ f) = ((sysOf X Λ₀).V X.T).subtype ∘ v :=
        funext fun i => (hf i).symm
      rw [e]
      exact hv'
    have h2 := X.toGeo.linearIndependent_toExt E X.T m f h1.of_comp
    have h3 := h2.map' (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T)
      (LinearMap.ker_eq_bot.2 (Pi.single_injective _))
    have e2 : (fun i => totExt X.toGeo E (v i)) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) X.T ∘ fun i => X.toGeo.toExt E X.T (f i)) := by
      funext i
      rw [hf i, totExt_single]
      rfl
    rw [e2]
    exact h3
  · intro j
    have hset : (totExt X.toGeo E '' ((sysOf X Λ₀).V j : Set (Tot X.toGeo))) =
        (LinearMap.single E (fun k => (X.toGeo.baseChange E).Sec k) j) ''
          (X.toGeo.toExt E j '' (X.V j : Set (X.toGeo.Sec j))) := by
      ext z
      constructor
      · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
        exact ⟨_, ⟨y, y.2, rfl⟩, (totExt_single X.toGeo E j y).symm⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨_, ⟨⟨y, hy⟩, rfl⟩, totExt_single X.toGeo E j y⟩
    rw [hset, ← Submodule.map_span]
    refine Eq.trans ?_ (LinearMap.range_comp ((X.baseChange E).V j).subtype (LinearMap.single E _ j)).symm
    rw [Submodule.range_subtype]
    rfl

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplit
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwSplitLine

theorem iwasawa_line_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  obtain ⟨P, P', hne, hP, hP'⟩ := hv
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (v := v) hne (IsDedekindDomain.HeightOneSpectrum.ext hP) (IsDedekindDomain.HeightOneSpectrum.ext hP')
  obtain ⟨k, i, qq, hn, hsum⟩ := GlobalTheory.IwSplitFrame.exists_compl x y (cT (σ : E →+* E) y * J) (cT (σ : E →+* E) x * J)
    hyx hyy hxx hxy
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ
    (e := x) (e' := y) (i := i) (p := cT (σ : E →+* E) y * J) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum hxy
  have hQ : ∀ z : GLoc σ J v, (B⁻¹ * splitHom σ J τ z * B).1.BlockTriangular lv →
      z ∈ GlobalTheory.IwSplitFrame.keepGrp (σ := σ) (J := J) (v := v) (x.map (inclR (F := F) (Fv F v))) :=
    fun z hz => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB z hz
      exact GlobalTheory.IwSplitFrame.keeps_of_split h τ z hyx hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular h hJ τ L hL _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  exact ⟨q, k', hk, rfl, β, hβ⟩

end GlobalTheory.IwSplitLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingRightTranslateMaxCompactStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothing_right_translate_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ), KInv α → ∀ (ψ : GA E a → ℂ) (k : Kinf E a) (g : GA E a), smoothing ν α (fun x => ψ (x * infGL E a (Unitary.toUnits k))) g = smoothing ν α ψ (g * infGL E a (Unitary.toUnits k)) := by
  first | exact @GlobalTheory.AutGrowth.smoothing_rt_Kinf | exact GlobalTheory.AutGrowth.smoothing_rt_Kinf | (intros; apply GlobalTheory.AutGrowth.smoothing_rt_Kinf <;> assumption)
end

