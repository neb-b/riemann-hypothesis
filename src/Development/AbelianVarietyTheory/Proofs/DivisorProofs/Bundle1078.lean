module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountUpSt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOpenNhdOneOfIntegralEqOneOnFinset
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Topology

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E]

theorem isOpen_intAt (v : HeightOneSpectrum (𝓞 E)) :
    IsOpen (v.adicCompletionIntegers E : Set (v.adicCompletion E)) := by
  have h : (v.adicCompletionIntegers E : Set (v.adicCompletion E)) =
      ((Valued.v : Valuation (v.adicCompletion E) _).integer : Set (v.adicCompletion E)) := by
    ext x
    simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.mem_integer_iff]
  rw [h]
  exact Valued.isOpen_integer _

theorem tendsto_af {α : Type} {l : Filter α} (g : α → Af E) (c : Af E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v c ∈ v.adicCompletionIntegers E)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (g a) = pLoc E v c) :
    Tendsto g l (𝓝 c) := by
  let c' : Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun v => ⟨pLoc E v c, hc v⟩
  have hcc : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite c' = c := by
    apply RestrictedProduct.ext
    intro v
    rfl
  let g' : α → Π v : HeightOneSpectrum (𝓞 E), v.adicCompletionIntegers E := fun a =>
    if h : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (g a) ∈ v.adicCompletionIntegers E then fun v => ⟨pLoc E v (g a), h v⟩
    else c'
  have hg' : Tendsto g' l (𝓝 c') := by
    rw [tendsto_pi_nhds]
    intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [h2, h3 v] with a ha hav
    simp only [g', dif_pos ha]
    exact Subtype.ext hav.symm
  have hmap := (tendsto_map (f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) cofinite)).comp hg'
  rw [← RestrictedProduct.nhds_eq_map_structureMap (fun v => isOpen_intAt v), hcc] at hmap
  apply hmap.congr'
  filter_upwards [h2] with a ha
  simp only [Function.comp_apply, g', dif_pos ha]
  apply RestrictedProduct.ext
  intro v
  rfl

theorem tendsto_ad {α : Type} {l : Filter α} (g : α → Ad E) (c : Ad E)
    (hc : ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E c) ∈ v.adicCompletionIntegers E)
    (h1 : ∀ᶠ a in l, (g a).1 = c.1)
    (h2 : ∀ᶠ a in l, ∀ v : HeightOneSpectrum (𝓞 E), pLoc E v (pFin E (g a)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, pLoc E v (pFin E (g a)) = pLoc E v (pFin E c)) :
    Tendsto g l (𝓝 c) := by
  have hA : Tendsto (fun a => (g a).1) l (𝓝 c.1) := tendsto_const_nhds.congr' (h1.mono fun a ha => ha.symm)
  have hB : Tendsto (fun a => (g a).2) l (𝓝 c.2) := tendsto_af (fun a => (g a).2) c.2 hc h2 h3
  exact hA.prodMk_nhds hB

end GlobalTheory.FixLevOpen

namespace GlobalTheory.FixLevOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem tendsto_mat {α : Type} {l : Filter α} (f : α → Matrix (Fin n) (Fin n) (Ad E))
    (h1 : ∀ᶠ a in l, ∀ i j, (f a i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1)
    (h2 : ∀ᶠ a in l, ∀ (v : HeightOneSpectrum (𝓞 E)) i j, pLoc E v (pFin E (f a i j)) ∈ v.adicCompletionIntegers E)
    (h3 : ∀ v : HeightOneSpectrum (𝓞 E), ∀ᶠ a in l, ∀ i j,
      pLoc E v (pFin E (f a i j)) = pLoc E v (pFin E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j))) :
    Tendsto f l (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  apply tendsto_ad
  · intro v
    rcases eq_or_ne i j with rfl | h
    · rw [Matrix.one_apply_eq, map_one, map_one]
      exact one_mem _
    · rw [Matrix.one_apply_ne h, map_zero, map_zero]
      exact zero_mem _
  · exact h1.mono fun a ha => ha i j
  · exact h2.mono fun a ha v => ha v i j
  · exact fun v => (h3 v).mono fun a ha => ha i j

theorem inf_entry (u : finU (E := E) (n := n)) (i j : Fin n) :
    ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 = ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := by
  have hu : cInf (u : UA E n) = 1 := u.2
  have h := congrArg (fun g : GL (Fin n) (Cinf E) => (g : Matrix (Fin n) (Fin n) (Cinf E)) i j) hu
  have h' : pInf E ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j) =
      pInf E ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j) := by
    refine h.trans ?_
    rcases eq_or_ne i j with rfl | hij
    · simp [Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne hij]
  have h'' : (infEq E).symm ((((u : UA E n) : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j).1 =
      (infEq E).symm ((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 := h'
  exact (infEq E).symm.injective h''

theorem mem_of_isOpen_of_eq_one_on_finset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (U : Set (finU (E := E) (n := n))), IsOpen U →
    (1 : finU (E := E) (n := n)) ∈ U → ∃ T : Finset (Pl E), ∀ u : finU (E := E) (n := n), (∀ v ∈ T, cLoc v (u : UA E n) = 1) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) →
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E) → u ∈ U := by
  intro E _ _ _ n U hU h1
  let S : Finset (Pl E) → Set (finU (E := E) (n := n)) := fun T => {u | (∀ v ∈ T, cLoc v (u : UA E n) = 1) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n)) i j ∈ v.adicCompletionIntegers E) ∧
    (∀ (v : Pl E) (i j : Fin n), (cLoc v (u : UA E n))⁻¹ i j ∈ v.adicCompletionIntegers E)}
  have hanti : ∀ T₁ T₂ : Finset (Pl E), T₁ ⊆ T₂ → S T₂ ⊆ S T₁ := fun T₁ T₂ h u hu =>
    ⟨fun v hv => hu.1 v (h hv), hu.2.1, hu.2.2⟩
  have hdir : Directed (fun x1 x2 => x1 ≥ x2) (fun T => 𝓟 (S T)) := by
    intro T₁ T₂
    refine ⟨T₁ ∪ T₂, ?_, ?_⟩
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_left)
    · exact principal_mono.mpr (hanti _ _ Finset.subset_union_right)
  let l : Filter (finU (E := E) (n := n)) := ⨅ T, 𝓟 (S T)
  have hmem : ∀ T, S T ∈ l := fun T => mem_iInf_of_mem T (mem_principal_self _)
  let ι : finU (E := E) (n := n) → GA E n := fun u => ((u : UA E n) : GA E n)
  have hι : Topology.IsInducing ι := Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  have hl : Tendsto id l (𝓝 (1 : finU (E := E) (n := n))) := by
    rw [hι.tendsto_nhds_iff, Units.isEmbedding_embedProduct.isInducing.tendsto_nhds_iff]
    show Tendsto (fun u => (((ι u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)),
      MulOpposite.op (((ι u)⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)))) l
      (𝓝 ((1 : Matrix (Fin n) (Fin n) (Ad E)), MulOpposite.op (1 : Matrix (Fin n) (Fin n) (Ad E))))
    refine Tendsto.prodMk_nhds ?_ (MulOpposite.continuous_op.tendsto _ |>.comp ?_)
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u i j
      · filter_upwards [hmem ∅] with u hu
        exact fun v i j => hu.2.1 v i j
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (hu.1 v (Finset.mem_singleton_self v))
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
    · apply tendsto_mat
      · exact Eventually.of_forall fun u i j => inf_entry u⁻¹ i j
      · filter_upwards [hmem ∅] with u hu
        intro v i j
        have := hu.2.2 v i j
        rwa [← map_inv] at this
      · intro v
        filter_upwards [hmem {v}] with u hu
        intro i j
        have hv : cLoc v ((u : UA E n)⁻¹) = 1 := by
          rw [map_inv, hu.1 v (Finset.mem_singleton_self v), inv_one]
        have e1 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j) hv
        have e2 := congrArg (fun g : GL (Fin n) (v.adicCompletion E) => g.val i j)
          (map_one (cLoc (E := E) (n := n) v))
        exact e1.trans e2.symm
  have hU' : U ∈ l := hl (hU.mem_nhds h1)
  rw [mem_iInf_of_directed hdir] at hU'
  obtain ⟨T, hT⟩ := hU'
  exact ⟨T, fun u a b c => mem_principal.mp hT ⟨a, b, c⟩⟩

end GlobalTheory.FixLevOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtBaseChange
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.ChowHt GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

open H0

variable {Y T : Scheme.{0}} {k k' : Type} [CommRing k] [CommRing k'] {p : Y ⟶ Sp k} {q : T ⟶ Sp k'} {φ : k →+* k'}
  {r : T ⟶ Y} {P B N : LB Y} {P' B' N' : LB T} {O : Y.Opens} {W : T.Opens}

theorem pullChart_ofSec (a : ChartPull B' B r) (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (s : B.Sec) :
    pullChart a hq h (H0.ofSec p O s) = H0.ofSec q W (GlobalTheory.chartSec a s) :=
  LB.sec_ext fun i => fun_ext_ger fun z hz => by
    change germ i z hz.1 hz.2 _ = germ i z hz.1 hz.2 _
    rw [germ_pullChart, germ_ofSec]
    exact (congrArg _ (germ_ofSec _ _ _ _ s)).trans (ger_appLE r _ z hz.2 _).symm

theorem pullChart_mul (C : ProdChart P B N) (C' : ProdChart P' B' N') (a : ChartPull P' P r) (b : ChartPull B' B r)
    (c : ChartPull N' N r) (hC : ∀ t, ∃ s, a.idx (C'.a t) = C.a s ∧ b.idx (C'.b t) = C.b s ∧ c.idx (C'.c t) = C.c s)
    (hq : r ≫ p = q ≫ spMap φ) (h : W ≤ r ⁻¹ᵁ O) (σ : H0 p P O) (f : H0 p B O) :
    pullChart c hq h (C.mul σ f) = C'.mul (pullChart a hq h σ) (pullChart b hq h f) :=
  C'.sec_ext fun t z hz ha hb hc => by
    obtain ⟨s, e₁, e₂, e₃⟩ := hC t
    have key (y hy i j l) (e₁ : i = C.a s) (e₂ : j = C.b s) (e₃ : l = C.c s) (hi hj hl) :
        germ l y hy hl (C.mul σ f) = germ i y hy hi σ * germ j y hy hj f := by
      subst e₁ e₂ e₃
      exact C.germ_mul σ f s y hy hi hj hl
    rw [C'.germ_mul _ _ t z hz ha hb hc, germ_pullChart, germ_pullChart, germ_pullChart, ← map_mul]
    exact congrArg _ (key _ _ _ _ _ e₁ e₂ e₃ _ _ _)

end GlobalTheory.Vanishing

namespace GlobalTheory.HermTools

end GlobalTheory.HermTools

namespace GlobalTheory.Adelic.HermSys

variable {F : Type} [Field F] [NumberField F] {T : HermSys F} (E : Type) [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.Adelic.HermSys

namespace GlobalTheory.HilbertSamuel

variable {F : Type} [Field F] [NumberField F]

namespace Geo

variable (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem toExt_mulW (j : ℕ) (u : Fin G.N → F) (f : G.Sec j) :
    G.toExt E (j + 1) (G.mulW j u f) = (G.baseChange E).mulW j (algebraMap F E ∘ u) (G.toExt E j f) := by
  refine (pullChart_mul _ (oneChart (isLB_tens (G.baseChange E).K.isLB (G.baseChange E).isLBA) (G.baseChange E).isLB
    (Nat.cast_succ j).symm) (GlobalTheory.chartPullPull G.L (G.fst E)) (G.chartAdj E j) (G.chartAdj E (j + 1))
    (fun t => ⟨((t.1.1 PUnit.unit, t.1.2 PUnit.unit), t.2 PUnit.unit), rfl, rfl, rfl⟩) _ le_rfl _ f).trans ?_
  refine congrArg (fun s => ProdChart.mul _ s _) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (map_smulₛₗ _ _ _).trans (congrArg _ (pullChart_ofSec _ _ _ (G.b k)))

end Geo

namespace Data

variable {X : Data F} (E : Type) [Field E] [NumberField E] [Algebra F E]



variable (X) in
theorem toExtV_mem {j : ℕ} {x : X.V j} (hx : x ∈ X.M j) : X.toExtV E j x ∈ (X.baseChange E).M j :=
  (Submodule.subset_span ⟨x, hx, rfl⟩ : extMap (X.toExt E j) (X.V j) x ∈
    Submodule.span (𝓞 E) (extMap (X.toExt E j) (X.V j) '' X.M j))

theorem MulStable.baseChange (h : X.MulStable) : (X.baseChange E).MulStable := fun j hj w hw f hf => by
  let X' := X.baseChange E
  let S := (X'.M (j + 1)).map ((X'.V (j + 1)).subtype.restrictScalars (𝓞 E))
  change X'.mulW j w f ∈ S
  induction hw using Submodule.span_induction with
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply]; exact add_mem ha hb
  | smul c a _ ha => rw [← algebraMap_smul E, map_smul, LinearMap.smul_apply, algebraMap_smul]; exact S.smul_mem _ ha
  | mem w hw =>
    obtain ⟨k, rfl⟩ := hw
    induction hf using Submodule.span_induction with
    | zero => exact (map_zero (X'.mulW j _)).symm ▸ zero_mem _
    | add a b _ _ ha hb => exact (map_add (X'.mulW j _) _ _).symm ▸ add_mem ha hb
    | smul c a _ ha =>
      exact (map_smul (X'.mulW j _) (algebraMap _ E c) _).symm ▸ S.smul_mem c ha
    | mem f hf =>
      obtain ⟨f, hf, rfl⟩ := hf
      obtain ⟨g, hg, e⟩ := h j hj _ (Submodule.subset_span ⟨k, rfl⟩) f hf
      exact ⟨_, X.toExtV_mem E hg, (congrArg (X.toExt E (j + 1)) e).trans (X.toExt_mulW E j _ _)⟩




end Data

end GlobalTheory.HilbertSamuel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulBoundAtOfNotIsReal
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.ChowHt GlobalTheory.HermTools

namespace GlobalTheory.HilbertSamuel

theorem denseRange_of_not_isReal {K : Type*} [Field K] {σ : K →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure σ.fieldRange) with h | h
  · refine absurd (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)) hσ
    obtain ⟨r, hr⟩ := h.le (Subfield.le_topologicalClosure _ ⟨x, rfl⟩)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · rw [denseRange_iff_closure_range, ← RingHom.coe_fieldRange]
    exact congrArg (fun s : Subfield ℂ => (s : Set ℂ)) h

theorem frameNorm_mul {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (x : Fin N → ℂ) :
    frameNorm A (fun j => c * x j) = ‖c‖ * frameNorm A x := by
  change frameNorm A (c • x) = _
  simp only [frameNorm, Matrix.mulVec_smul, Pi.smul_apply, norm_smul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

theorem continuous_frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : Continuous (frameNorm A) := by
  unfold frameNorm Matrix.mulVec dotProduct
  fun_prop

theorem continuous_cnrm {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] (h : HermFam K V)
    (σ : K →+* ℂ) (v : ι → V) : Continuous fun c => cnrm h σ c v := by
  unfold cnrm csq
  fun_prop

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_mem_span {V : Type*} [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    {S : Set V} (hS : Submodule.span F S = ⊤) (x : V) : ∃ a : F, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 F) S := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 F)) F S x (hS.ge trivial)
  refine ⟨algebraMap (𝓞 F) F t, ?_, by rwa [algebraMap_smul]⟩
  exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 (nonZeroDivisors.coe_ne_zero t)

namespace Data

variable {X : Data F} {β : (F →+* ℂ) → ℝ}

theorem MulBound.of_field (h : X.MulBound β) {j : ℕ} (hj : j < X.T) (σ : F →+* ℂ) (u : Fin X.N → F) (f : X.V j)
    (g : X.V (j + 1)) (e : (g : X.Sec (j + 1)) = X.mulW j u f) :
    (X.nm (j + 1)).nrm σ g ≤ Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (u k)) * (X.nm j).nrm σ f := by
  obtain ⟨a, ha, hu⟩ := exists_smul_mem_span X.geom.alg.spans u
  obtain ⟨b, hb, hf⟩ := exists_smul_mem_span (X.full j).span f
  rw [Submodule.span_eq] at hf
  have key : (X.nm (j + 1)).nrm σ (a • b • g) ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) (fun k => σ (a * u k)) * (X.nm j).nrm σ (b • f) :=
    h j hj σ _ hu _ hf (a • b • g) (by
      rw [Submodule.coe_smul, Submodule.coe_smul, Submodule.coe_smul, e, map_smul, map_smul, LinearMap.smul_apply,
        smul_comm])
  simp only [map_mul, frameNorm_mul, HermFam.nrm_smul_up] at key
  have ha' : 0 < ‖σ a‖ := norm_pos_iff.2 ((map_ne_zero σ).2 ha)
  have hb' : 0 < ‖σ b‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hb)
  exact le_of_mul_le_mul_left (by linarith) (mul_pos ha' hb')

theorem MulBound.mulBoundAt_of_not_isReal (h : X.MulBound β) {σ : F →+* ℂ} (hσ : ¬ComplexEmbedding.IsReal σ) :
    X.MulBoundAt σ (β σ) := fun j hj u m c f g hg => by
  have hd := denseRange_of_not_isReal hσ
  refine ((DenseRange.piMap fun _ : Fin X.N => hd).prodMap (DenseRange.piMap fun _ : Fin m => hd)).induction_on
    (p := fun z => cnrm (X.nm (j + 1)) σ (fun t => z.1 t.1 * z.2 t.2) g ≤
      Real.sqrt (β σ) * frameNorm (X.A σ) z.1 * cnrm (X.nm j) σ z.2 f) (u, c) ?_ ?_
  · exact isClosed_le ((continuous_cnrm _ _ _).comp (by fun_prop))
      ((continuous_const.mul ((continuous_frameNorm _).comp continuous_fst)).mul
        ((continuous_cnrm _ _ _).comp continuous_snd))
  · rintro ⟨a, b⟩
    have := h.of_field hj σ a (∑ i, b i • f i) (∑ t : Fin X.N × Fin m, (a t.1 * b t.2) • g t) (by
      conv_rhs => rw [pi_eq_sum_univ' a]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fintype.sum_prod_type, Submodule.coe_sum, Submodule.coe_smul, hg, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => smul_comm _ _ _))
    simp only [← cnrm_map, map_mul] at this
    exact this

theorem MulBound.mulBoundAt [_root_.NumberField.IsTotallyComplex F] (h : X.MulBound β) (σ : F →+* ℂ) : X.MulBoundAt σ (β σ) :=
  h.mulBoundAt_of_not_isReal (IsTotallyComplex.complexEmbedding_not_isReal σ)

end Data

end GlobalTheory.HilbertSamuel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {a : ℕ} {B : GlobalTheory.UnitLemma.InvAlg K} (b : Module.Basis (Fin a) K.E B.A)

def crd (y : B.A) : Fin a → w.adicCompletion E := fun i => e (b.repr y i)

def ofCrd (v : Fin a → w.adicCompletion E) : B.A := b.equivFun.symm fun i => e.symm (v i)

def mulHom : B.A →+* Matrix (Fin a) (Fin a) (w.adicCompletion E) :=
  e.toRingHom.mapMatrix.comp (Algebra.leftMulMatrix b).toRingHom

def mulGL : B.Aˣ →* GLw a w := Units.map (mulHom e b).toMonoidHom

theorem mulHom_eq (t : B.A) : mulHom e b t = GlobalTheory.TwLat.mulMat e b t := by
  ext i j
  simp [mulHom, GlobalTheory.TwLat.mulMat, Algebra.leftMulMatrix_apply]

theorem latOf_eq (q : GLw a w) :
    GlobalTheory.TwLat.lat e b q = Submodule.span K.O (Set.range fun j => ofCrd e b fun i => q.val i j) := by
  simp [GlobalTheory.TwLat.lat, ofCrd, Module.Basis.equivFun_symm_apply]

theorem crd_ofCrd (v : Fin a → w.adicCompletion E) : crd e b (ofCrd e b v) = v := by
  funext i
  simp only [crd, ofCrd]
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem ofCrd_crd (y : B.A) : ofCrd e b (crd e b y) = y := by
  simp [crd, ofCrd]

theorem mulHom_apply (t : B.A) (i j : Fin a) : mulHom e b t i j = e (b.repr (t * b j) i) := by
  simp [mulHom, Algebra.leftMulMatrix_eq_repr_mul]

theorem mulGL_val (t : B.Aˣ) : (mulGL e b t).val = GlobalTheory.TwLat.mulMat e b t := mulHom_eq e b t

theorem mulHom_injective : Function.Injective (mulHom e b) := by
  intro x y h
  apply Algebra.leftMulMatrix_injective b
  ext i j
  have := congrFun (congrFun h i) j
  exact e.injective (by simpa [mulHom] using this)

theorem mulGL_injective : Function.Injective (mulGL e b) := by
  intro x y h
  exact Units.ext (mulHom_injective e b (congrArg Units.val h))

theorem crd_injective : Function.Injective (crd e b) := fun x y h => by
  rw [← ofCrd_crd e b x, h, ofCrd_crd]

theorem crd_add (y z : B.A) : crd e b (y + z) = crd e b y + crd e b z := by
  funext i; simp [crd]

theorem crd_smul (c : K.E) (y : B.A) : crd e b (c • y) = e c • crd e b y := by
  funext i; simp [crd]

theorem crd_mul (t y : B.A) : crd e b (t * y) = mulHom e b t *ᵥ crd e b y := by
  funext i
  simp only [crd, mulHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← Algebra.leftMulMatrix_mulVec_repr]
  simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, crd]

theorem ofCrd_mulVec (t : B.A) (v : Fin a → w.adicCompletion E) :
    ofCrd e b (mulHom e b t *ᵥ v) = t * ofCrd e b v := by
  apply crd_injective e b
  rw [crd_mul, crd_ofCrd, crd_ofCrd]

theorem col_mul (M N : Matrix (Fin a) (Fin a) (w.adicCompletion E)) (j : Fin a) :
    (fun i => (M * N) i j) = M *ᵥ fun i => N i j := by
  funext i; simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem crd_sum (s : Finset (Fin a)) (f : Fin a → B.A) : crd e b (∑ j ∈ s, f j) = ∑ j ∈ s, crd e b (f j) := by
  induction s using Finset.induction_on with
  | empty => funext i; simp [crd]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, crd_add, ih]

theorem latOf_mul (t : B.Aˣ) (q : GLw a w) :
    GlobalTheory.TwLat.lat e b (mulGL e b t * q) = GlobalTheory.UnitLemma.mulLat K.O (t : B.A) (GlobalTheory.TwLat.lat e b q) := by
  rw [latOf_eq, latOf_eq]
  unfold GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span K.O) (congrArg Set.range (funext fun j => ?_))
  simp only [Function.comp_apply, LinearMap.mulLeft_apply, Units.val_mul]
  change (ofCrd e b fun i => (mulHom e b (t : B.A) * q.val) i j) = _
  rw [col_mul (mulHom e b (t : B.A)) q.val j, ofCrd_mulVec]

theorem latOf_isLat (q : GLw a w) : GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b q) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  rw [latOf_eq, Submodule.span_span_of_tower, eq_top_iff]
  intro z _
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => e.symm (((q⁻¹ : GLw a w).val *ᵥ crd e b z) j), ?_⟩
  apply crd_injective e b
  rw [crd_sum]
  have h1 : crd e b z = q.val *ᵥ ((q⁻¹ : GLw a w).val *ᵥ crd e b z) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  conv_rhs => rw [h1]
  funext i
  simp [crd_smul, crd_ofCrd, Finset.sum_apply, Matrix.mulVec, dotProduct, mul_comm]

end GlobalTheory.TwOrbLat
end
end

