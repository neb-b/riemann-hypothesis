module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefBTensSubKStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0014
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.WeightedB

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def tensGrp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (dual : Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, (cond dual ((g⁻¹) d c) (g c d)) • σ g (f d)

theorem coef_of_emb (dual : Bool) {lam lam' : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {V' : Submodule ℂ D} (hgap' : StdGap ε lam') (hV' : IsKIrrHW ε E (lowK ε lam') V')
    (hc' : ∀ v ∈ V', casimir E v = (casVal lam' : ℂ) • v)
    (hVK' : ∀ k ∈ Kset ε, ∀ v ∈ V', ∃ w ∈ V', (w : H) = σ k v)
    {ι : D →ₗ[ℂ] (Fin n → D)} (hι : IsGKEmb dual ε σ E (genSub E V) (genSub E V') ι) :
    (∀ f ∈ tensSub (genSub E V), ∀ x' ∈ genSub E V', ∃ z ∈ genSub E V', ∀ g ∈ UJset ε,
      ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) =
        inner ℂ ((z : D) : H) (σ g ((x' : D) : H))) ∧
    ∀ z ∈ genSub E V', ∀ x' ∈ genSub E V', ∃ f ∈ tensSub (genSub E V), ∀ g ∈ UJset ε,
      inner ℂ ((z : D) : H) (σ g ((x' : D) : H)) =
        ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) := by
  have hVf := hV.1
  have hVst := hV.2.1
  have hV'f := hV'.1
  have hV'st := hV'.2.1
  have hTG : ∀ g : Matrix (Fin n) (Fin n) ℂ, ∀ w : Fin n → H,
      tensGrp dual σ g w = coefTG dual σ g w := by
    intro g w
    cases dual <;> rfl
  have hιE : ∀ a b, ∀ x ∈ genSub E V', ι (E a b x) = tensF dual E a b (ι x) :=
    hι.2.2.1
  have key : ∀ f ∈ tensSub (genSub E V), ∀ z ∈ genSub E V',
      (∀ y ∈ genSub E V', inner ℂ z y = ∑ c, inner ℂ (f c) (ι y c)) →
      ∀ x' ∈ genSub E V', ∀ g ∈ UJset ε,
        ∑ c, inner ℂ ((f c : D) : H) (tensGrp dual σ g (fun d => ((ι x' d : D) : H)) c) =
          inner ℂ ((z : D) : H) (σ g ((x' : D) : H)) := by
    intro f _ z _ hz x' hx' g hg
    rw [hTG]
    exact coefE_all dual hσ hD hVf hVst hc hV'f hV'st hc' hι.1 hιE f z hz g hg x' hx'
  refine ⟨fun f hf x' hx' => ?_, fun z hz x' hx' => ?_⟩
  · obtain ⟨z, hzm, hz⟩ :=
      ReciprocityTheory.ChartRestriction.DS.G2.coefB_toSum_exists dual hσ hD hVf hVst hgap' hV' hc' hι f hf
    exact ⟨z, hzm, key f hf z hzm hz x' hx'⟩
  · obtain ⟨f, hf, hzf⟩ :=
      ReciprocityTheory.ChartRestriction.DS.G2.coefB_ofSum_exists dual hσ hD hgap' hV' hc' hι z hz
    exact ⟨f, hf, fun g hg => (key f hf z hz hzf x' hx' g hg).symm⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.OccDAdjA
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem adjA_high {D : Type*} [AddCommGroup D] [Module ℂ D] {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (M : Submodule ℂ D) (T : Module.End ℂ D) (hT : ∀ y ∈ M, T y ∈ M)
    (Φ : D →ₗ[ℂ] W) (hΦ : ∀ y ∈ M, Φ y = 0 → Φ (T y) = 0) :
    ∃ C : ℝ, ∀ y ∈ M, ∀ θ : ℝ, C < θ → T y = (θ : ℂ) • y → Φ y = 0 := by
  classical
  set TM : Module.End ℂ M := T.restrict hT
  set Φ' : M →ₗ[ℂ] W := Φ.comp M.subtype
  set p : Submodule ℂ M := LinearMap.ker Φ'
  have hp : p ≤ p.comap TM := by
    intro y hy
    simp only [Submodule.mem_comap, p, LinearMap.mem_ker, Φ', LinearMap.comp_apply,
      Submodule.subtype_apply] at hy ⊢
    exact hΦ y y.2 hy
  set Tb : Module.End ℂ (M ⧸ p) := p.mapQ p TM hp
  have : FiniteDimensional ℂ (LinearMap.range Φ') := inferInstance
  have : FiniteDimensional ℂ (M ⧸ p) := LinearEquiv.finiteDimensional Φ'.quotKerEquivRange.symm
  have hfin := Module.End.finite_hasEigenvalue Tb
  refine ⟨∑ μ ∈ hfin.toFinset, ‖μ‖, fun y hy θ hθ hTy => ?_⟩
  by_contra hne
  have hq : Submodule.Quotient.mk (p := p) (⟨y, hy⟩ : M) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hne
  have hTb : Tb (Submodule.Quotient.mk (⟨y, hy⟩ : M)) = (θ : ℂ) • Submodule.Quotient.mk (⟨y, hy⟩ : M) := by
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext hTy
  have hev : Tb.HasEigenvalue (θ : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hTb, hq⟩
  have hmem : (θ : ℂ) ∈ hfin.toFinset := hfin.mem_toFinset.2 hev
  have hle : ‖(θ : ℂ)‖ ≤ ∑ μ ∈ hfin.toFinset, ‖μ‖ :=
    Finset.single_le_sum (f := fun μ : ℂ => ‖μ‖) (fun _ _ => norm_nonneg _) hmem
  rw [Complex.norm_real, Real.norm_eq_abs] at hle
  linarith [le_abs_self θ]

theorem adjA_tensF_single {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (y : M) :
    ∃ c' : Fin n, ∃ r : ℂ, tensF dual E a b (Pi.single c y) = Pi.single c (E a b y) + r • (Pi.single c' y : Fin n → M) := by
  classical
  cases dual
  · refine ⟨a, if b = c then 1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_false, tensV_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all
  · refine ⟨b, if a = c then -1 else 0, ?_⟩
    funext x
    simp only [tensF, cond_true, tensVd_coord, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp_all [sub_eq_add_neg]

theorem adjA_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] {S : Submodule ℂ M} (c : Fin n) {y : M}
    (hy : y ∈ S) : (Pi.single c y : Fin n → M) ∈ tensSub S := by
  classical
  refine Submodule.mem_pi.2 fun x _ => ?_
  rw [Pi.single_apply]
  split_ifs
  · exact hy
  · exact S.zero_mem

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem adjA_rep (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {lam : Fin n → ℝ} {V V' : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hV'f : FiniteDimensional ℂ V')
    (hV'k : IsKStableSub ε E V') {ps : (Fin n → D) →ₗ[ℂ] D}
    (hps : ∀ a b, ∀ f ∈ tensSub (genSub E V), ps (tensF dual E a b f) = E a b (ps f))
    {x' : D} (hx' : x' ∈ genSub E V') (c : Fin n) :
    ∃ z ∈ genSub E V, ∀ y ∈ genSub E V, inner ℂ z y = inner ℂ x' (ps (Pi.single c y)) := by
  classical
  have hE := hD.glRep
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hUk := isKUnitary_of_isInfUnitary hU
  obtain ⟨m', hm'⟩ := exists_layer_of_mem_genSub hE hV'k hx'
  set L' := layer ε E V' m'
  have hL'f : FiniteDimensional ℂ L' := finiteDimensional_layer hV'f m'
  have hL'k : IsKStableSub ε E L' := layer_kStable hE hV'k m'
  set bs := Module.finBasis ℂ L'
  set Φ : D →ₗ[ℂ] (Fin n × Fin (Module.finrank ℂ L') → ℂ) :=
    LinearMap.pi fun p => (innerₛₗ ℂ (bs p.2 : D)).comp (ps.comp (LinearMap.single ℂ (fun _ => D) p.1))
  have hΦ : ∀ y, ∀ p : Fin n × Fin (Module.finrank ℂ L'), Φ y p = inner ℂ (bs p.2 : D) (ps (Pi.single p.1 y)) :=
    fun y p => rfl

  set P : D → Prop := fun y => ∀ v ∈ L', ∀ c, inner ℂ v (ps (Pi.single c y)) = 0
  have hPΦ : ∀ y, Φ y = 0 → P y := by
    intro y hy v hv c
    have hv' : v = ∑ i, (bs.repr ⟨v, hv⟩ i) • (bs i : D) := by
      have := congrArg Subtype.val (bs.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simpa only [Submodule.coe_smul] using this.symm
    rw [hv', sum_inner]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [inner_smul_left, ← hΦ y (c, i), hy, Pi.zero_apply, mul_zero]
  have hΦP : ∀ y, P y → Φ y = 0 := by
    intro y hy
    funext p
    rw [hΦ, Pi.zero_apply]
    exact hy _ (bs p.2).2 p.1
  have hMk : IsKStableSub ε E (genSub E V) := fun a b _ v hv => closure_E_mem_genSub a b hv
  have hPE : ∀ y ∈ genSub E V, P y → ∀ a b, ε a = ε b → P (E a b y) := by
    intro y hy hPy a b hab v hv c
    obtain ⟨c', r, hcr⟩ := adjA_tensF_single dual E a b c y
    have h1 : ps (Pi.single c (E a b y)) = E a b (ps (Pi.single c y)) - r • ps (Pi.single c' y) := by
      rw [← hps a b _ (adjA_single_mem c hy), hcr, map_add (f := _), map_smul]
      abel
    rw [h1, inner_sub_right, inner_smul_right, hPy v hv c', mul_zero, sub_zero, ← hUk b a hab.symm]
    exact hPy _ (hL'k b a hab.symm v hv) c
  have hPadd : ∀ s : Finset (Fin n), ∀ g : Fin n → D, (∀ q ∈ s, P (g q)) → P (∑ q ∈ s, g q) := by
    intro s g hg v hv c
    have : (Pi.single c (∑ q ∈ s, g q) : Fin n → D) = ∑ q ∈ s, Pi.single c (g q) := by
      funext x
      simp only [Pi.single_apply, Finset.sum_apply]
      split_ifs <;> simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, inner_sum]
    exact Finset.sum_eq_zero fun q hq => hg q hq v hv c
  have hcasP : ∀ y ∈ genSub E V, P y → P (casimirK ε E y) := by
    intro y hy hPy
    simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply]
    refine hPadd _ _ fun a _ => hPadd _ _ fun b hb => ?_
    have hq' : ε b = ε a := (Finset.mem_filter.1 hb).2
    exact hPE _ (closure_E_mem_genSub _ _ hy) (hPE y hy hPy b a hq') a b hq'.symm
  obtain ⟨C, hC⟩ := adjA_high (genSub E V) (casimirK ε E)
    (fun y hy => casimirK_mem_of_kStable hMk hy) Φ (fun y hy h0 => hΦP _ (hcasP y hy (hPΦ y h0)))
  obtain ⟨K, hK⟩ := coefB_adm hE hU hV hc hgap C
  have hTsym : ∀ x y, inner ℂ (casimirK ε E x) y = inner ℂ x (casimirK ε E y) := casimirK_inner_symm hUk
  set ℓ : D →ₗ[ℂ] ℂ := (innerₛₗ ℂ x').comp (ps.comp (LinearMap.single ℂ (fun _ => D) c))
  obtain ⟨z, hzM, hz⟩ := coefA_toSum hTsym (coefB_locFin hE hV.1 hV.2.1) ℓ C
    (finiteDimensional_layer hV.1 K) (layer_le_genSub K) (fun y hy θ hθ hyθ => hK y hy θ hθ hyθ)
    (fun y hy θ hθ hyθ => hPΦ y (hC y hy θ hθ hyθ) x' hm' c)
  exact ⟨z, hzM, fun y hy => hz y hy⟩

end Rep

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize
section
noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open UnitA UnitB

section SlopeTestRemainingChoices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

def hvec (f : Fin n → D) : Fin n → H := fun c => ((f c : D) : H)

theorem hvec_add (f g : Fin n → D) : hvec (f + g) = hvec f + hvec g := by
  funext c; simp [hvec]

theorem hvec_smul (a : ℂ) (f : Fin n → D) : hvec (a • f) = a • hvec f := by
  funext c; simp [hvec]

theorem mx_mem {M : Submodule ℂ D} (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hst : ∀ a b, ∀ f ∈ tensSub M, tensF dual E a b f ∈ tensSub M) {f : Fin n → D} (hf : f ∈ tensSub M) :
    mx (tensF dual E) X f ∈ tensSub M := by
  unfold mx
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hst a b f hf)

theorem mat_decomp2 (Y Z : Matrix (Fin n) (Fin n) ℂ) :
    (1 / 2 : ℂ) • (Y - Z) + (Complex.I / 2) • (Complex.I • (Y + Z)) = -Z := by
  rw [smul_smul, show Complex.I / 2 * Complex.I = -(1 / 2) by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring]
  module

end SlopeTestRemainingChoices

theorem tens_unitarize (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ,
      (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), Q g f = star (Q f g)) ∧
      (∀ f ∈ tensSub (genSub E V), f ≠ 0 → 0 < (Q f f).re) ∧
      (∀ a b, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) ∧
      ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        ∀ f' ∈ tensSub (genSub E V), ∀ g' ∈ tensSub (genSub E V),
          (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
          (fun c => ((g' c : D) : H)) = kDiag dual σ k (fun c => ((g c : D) : H)) → Q f' g' = Q f g := by
  classical
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : FiniteDimensional ℂ V := hV.1
  let bV := Module.finBasis ℂ V
  let ys : Fin (Module.finrank ℂ V) → H := fun j => (((bV j : V) : D) : H)
  have hVM : V ≤ genSub E V := le_sInf fun T hT => hT.1
  have hmem : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c, f c ∈ genSub E V := fun f hf c =>
    (Submodule.mem_pi.1 hf) c (Set.mem_univ c)
  have hst : ∀ a b : Fin n, ∀ f ∈ tensSub (n := n) (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) :=
    tensSub_stable dual
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let P : (Fin n → D) →ₗ[ℂ] (Fin n → D) :=
    (tensSub (n := n) (genSub E V)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hPm : ∀ f : Fin n → D, P f ∈ tensSub (genSub E V) := fun f => (Submodule.linearProjOfIsCompl _ _ hC f).2
  have hPid : ∀ f ∈ tensSub (n := n) (genSub E V), P f = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨f, hf⟩)
  let u : Fin (Module.finrank ℂ V) → Fin n → (Fin n → D) → Formalism.REAL.UJ ε → ℂ :=
    fun j ξ f => cf dual ε σ (ys j) ξ (hvec f)
  have hL : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ j ξ, MemLp (u j ξ f) 2 (Formalism.REAL.muG ε) := fun f hf j ξ =>
    memLp_cf hσ dual _ ξ _ fun c => hW (f c) (hmem f hf c) ((bV j : V) : D) (hVM (bV j).2)
  have hLP : ∀ (f : Fin n → D) j ξ, MemLp (u j ξ (P f)) 2 (Formalism.REAL.muG ε) := fun f => hL _ (hPm f)
  have hu_add : ∀ j ξ f g, u j ξ (f + g) = u j ξ f + u j ξ g := fun j ξ f g => by
    simp only [u, hvec_add, cf_add]
  have hu_smul : ∀ j ξ (a : ℂ) f, u j ξ (a • f) = a • u j ξ f := fun j ξ a f => by
    simp only [u, hvec_smul, cf_smul]
  let Q0 : (Fin n → D) → (Fin n → D) → ℂ := fun f g =>
    ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ (P f)) (u j ξ (P g))
  let Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) Q0
    (fun f f' g => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_left (hLP f j ξ) (hLP f' j ξ) (hLP g j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_left, Finset.mul_sum, smul_eq_mul, starRingEnd_apply])
    (fun f g g' => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_right (hLP f j ξ) (hLP g j ξ) (hLP g' j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])
  have hQ : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q f g = ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ g) := by
    intro f hf g hg
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, hPid f hf, hPid g hg]
  have hskew : ∀ X (hX : inG ε X), ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (mx (tensF dual E) X f) g = -Q f (mx (tensF dual E) X g) := by
    intro X hX f hf g hg
    have hXf := mx_mem dual X hst hf
    have hXg := mx_mem dual X hst hg
    rw [hQ _ hXf g hg, hQ f hf _ hXg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    exact skew (continuous_ex hX) (ex_zero hX) (ex_add hX)
      (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _)
      (continuous_cf hσ dual _ ξ _)
      (hL f hf j ξ) (hL _ hXf j ξ) (hL g hg j ξ) (hL _ hXg j ξ)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ f x t)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ g x t)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro f _ g _
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, star_sum, pr_star]
  · intro f hf hf0
    rw [hQ f hf f hf]
    have hre : ∀ j ξ, (pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ f)).re =
        ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := by
      intro j ξ
      rw [(pr_self_re (hL f hf j ξ)).1, Complex.ofReal_re]
    simp only [Complex.re_sum, hre]
    have hnn : ∀ j ξ, 0 ≤ ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := fun j ξ =>
      integral_nonneg fun x => by positivity
    by_contra hneg
    push_neg at hneg
    have h0 : ∑ j, ∑ ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 :=
      le_antisymm hneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ)
    have hz : ∀ j ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 := by
      intro j ξ
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ).1 h0 j
        (Finset.mem_univ j)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun ξ _ => hnn j ξ).1 h1 ξ (Finset.mem_univ ξ)
    have hz' : ∀ j ξ x, u j ξ f x = 0 := by
      intro j ξ
      have hi := (pr_self_re (hL f hf j ξ)).2
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 (hz j ξ)
      have hc : Continuous (fun x => ‖u j ξ f x‖ ^ 2) := ((continuous_cf hσ dual _ ξ _).norm).pow 2
      have h2 := (hc.ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae
      intro x
      have h3 := congrFun h2 x
      simpa using h3
    apply hf0
    refine cf_inj hσ hD dual (hmem f hf) fun y hy ξ x => ?_
    have hy' : ((y : D) : H) = ∑ j, (bV.repr ⟨y, hy⟩ j) • ys j := by
      have h2 := congrArg (fun w : V => ((w : D) : H)) (bV.sum_repr ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    have e : cf dual ε σ ((y : D) : H) ξ (fun c => ((f c : D) : H)) x =
        ∑ j, star (bV.repr ⟨y, hy⟩ j) * u j ξ f x := by
      simp only [u, cf, hvec, hy', sum_inner, inner_smul_left, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [starRingEnd_apply]
      ring
    rw [e]
    exact Finset.sum_eq_zero fun j _ => by rw [hz' j ξ x, mul_zero]
  · intro a b f hf g hg
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε := ⟨_, rfl⟩
    have hX1 : inG ε (Matrix.single a b 1 - Z) := by rw [hZ]; exact inG_sub _
    have hX2 : inG ε (Complex.I • (Matrix.single a b 1 + Z)) := by rw [hZ]; exact inG_add _
    have hTab : tensF dual E a b = (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (-(Complex.I / 2)) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, ← mat_decomp, mx_single]
    have hTba : (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (Complex.I / 2) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) =
        -(adjSign ε a b • tensF dual E b a) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, mat_decomp2, hZ, single_conj, ← neg_smul, mx_smul, mx_single,
        neg_smul]
    have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    have s2 : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [Complex.conj_I, neg_div]
    have e1 : Q (tensF dual E a b f) g =
        (1 / 2 : ℂ) * Q (mx (tensF dual E) (Matrix.single a b 1 - Z) f) g +
        (Complex.I / 2) * Q (mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) f) g := by
      rw [hTab]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, smul_eq_mul,
        starRingEnd_apply, s1, s2]
    have e2 := congrArg (fun A : Module.End ℂ (Fin n → D) => Q f (A g)) hTba
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, map_add (f := _), map_smul, map_neg,
      smul_eq_mul] at e2
    rw [e1, hskew _ hX1 f hf g hg, hskew _ hX2 f hf g hg]
    linear_combination (-1 : ℂ) * e2
  · intro k hk f hf g hg f' hf' g' hg' hff hgg
    have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hQ f' hf' g' hg', hQ f hf g hg]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ => ?_
    have e : ∀ (h h' : Fin n → D), (fun c => ((h' c : D) : H)) = kDiag dual σ k (fun c => ((h c : D) : H)) →
        u j ξ h' = fun x => u j ξ h (x * toG k hkU) := by
      intro h h' hh
      funext x
      show cf dual ε σ (ys j) ξ (hvec h') x = _
      rw [show hvec h' = kDiag dual σ (Formalism.MainNotions.S.umat (toG k hkU)) (hvec h) from hh]
      exact cf_kDiag hσ dual _ ξ _ (toG k hkU) hk.2 x
    rw [e f f' hff, e g g' hgg, pr_rt]

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Weighted
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem weighted_datum {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V} (hgap : StdGap ε lam)
    (hP : IsPsiFor ε lam T Ψ) (hv₀ : v₀ ≠ 0)
    (hΨw : ∀ μ : Measure (S7.UJ ε), μ.IsHaarMeasure →
      Integrable (fun g : S7.UJ ε => ‖Ψ (S7.toM g)‖ ^ 2 * S7.hs (S7.toM g) ^ ((2 : ℝ) / 2)) μ) :
    ∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
      MemLp (fun g : Formalism.REAL.UJ ε =>
        ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε)))
        2 (Formalism.REAL.muG ε) := by
  intro v hv w hw
  show MemLp (wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v)) 2 (Formalism.REAL.muG ε)
  rcases isEmpty_or_nonempty (Fin n) with hn | hne
  · have e : wdF ε (wdCoef ε ((w : smD ε (rreg ε)) : L2 ε) v) = 0 := by
      funext g
      simp [wdF, S7.hs]
    rw [e]
    exact MemLp.zero
  · obtain ⟨i⟩ := hne
    exact wd_key hP hv₀ i (w : L2 ε) (fun x hx => wd_gen_datum hgap hP hv₀ hΨw i w hw x hx) v hv

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

