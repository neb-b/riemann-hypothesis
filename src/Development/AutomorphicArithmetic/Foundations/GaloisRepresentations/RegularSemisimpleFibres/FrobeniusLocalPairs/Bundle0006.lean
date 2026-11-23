module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.NumberField
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import GroundTheory.LocalFields.Uniqueness

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemTest
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {E : Type} [Field E] [ValuativeRel E] {n : ℕ}

private theorem near_mul {r : ValueGroupWithZero E} (h1 : r < 1) {x y : E} (hx : valuation E (x - 1) ≤ r)
    (hy : valuation E (y - 1) ≤ r) : valuation E (x * y - 1) ≤ r := by
  have hx1 : valuation E x ≤ 1 := by
    have e : x = (x - 1) + 1 := by ring
    rw [e]
    exact (Valuation.map_add_le _ (hx.trans h1.le) (by simp))
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine Valuation.map_add_le _ ?_ hx
  rw [map_mul]
  exact (mul_le_mul' hx1 hy).trans (by simp)

private theorem near_prod {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {ι : Type} (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, valuation E (f i - 1) ≤ r) : valuation E (∏ i ∈ s, f i - 1) ≤ r := by
  induction s using Finset.induction_on with
  | empty => simpa using h0.le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact near_mul h1 (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem small_prod {r : ValueGroupWithZero E} {ι : Type} (s : Finset ι) (f : ι → E) (hs : ∀ i ∈ s, valuation E (f i) ≤ 1)
    (a : ι) (ha : a ∈ s) (hr : valuation E (f a) ≤ r) : valuation E (∏ i ∈ s, f i) ≤ r := by
  rw [← Finset.mul_prod_erase s f ha, map_mul, map_prod]
  exact (mul_le_of_le_one_right' (Finset.prod_le_one' fun i hi => hs i (Finset.mem_of_mem_erase hi))).trans hr

private theorem det_near {r : ValueGroupWithZero E} (h0 : 0 < r) (h1 : r < 1) {M : Matrix (Fin n) (Fin n) E}
    (hM : ∀ i j, valuation E (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) ≤ r) : valuation E (M.det - 1) ≤ r := by
  have hb : ∀ i j, valuation E (M i j) ≤ 1 := fun i j => by
    have e : M i j = (M i j - (1 : Matrix (Fin n) (Fin n) E) i j) + (1 : Matrix (Fin n) (Fin n) E) i j := by ring
    rw [e]
    refine Valuation.map_add_le _ ((hM i j).trans h1.le) ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n))), add_sub_right_comm]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun p hp => ?_)
  · have hd : valuation E (∏ i, M i i - 1) ≤ r := near_prod h0 h1 _ _ fun i _ => by simpa using hM i i
    simpa using hd
  · have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
    obtain ⟨a, ha⟩ : ∃ a, p a ≠ a := by
      by_contra hc
      push Not at hc
      exact hp1 (Equiv.ext hc)
    have hs : valuation E (∏ i, M (p i) i) ≤ r := by
      refine small_prod _ _ (fun i _ => hb _ _) a (Finset.mem_univ _) ?_
      simpa [Matrix.one_apply, ha] using hM (p a) a
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with e | e <;> simpa [e, Units.smul_def] using hs

end

private theorem diag_cont (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) :
    Continuous (diagT E (Fin n)) :=
  (continuous_leviEmb E (points (Fin n))).comp (continuous_leviTorus E (Fin n))

theorem elemTest : ElemTest := by
  intro E _ _ _ _ n r h0 h1 A hA
  obtain ⟨K, hK, hKo, hKc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub E n r h0 h1
  haveI := (UpperTheory.V.Z.Tf.Orb.gLTop E n).2.2.1
  have mK : ∀ g : GL (Fin n) E, g ∈ ball n r ↔ g ∈ K := fun g => by rw [← hK]; rfl
  have e : elemSet r A = (fun z : GL (Fin n) E × (Fin n → Eˣ) × GL (Fin n) E => z.1 * diagT E (Fin n) z.2.1 * z.2.2) ''
      ((K : Set (GL (Fin n) E)) ×ˢ (A ×ˢ (K : Set (GL (Fin n) E)))) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, s, hs, rfl⟩
      exact ⟨(a, s, b), ⟨(mK a).1 ha, hs, (mK b).1 hb⟩, rfl⟩
    · rintro ⟨⟨a, s, b⟩, ⟨ha, hs, hb⟩, rfl⟩
      exact ⟨a, (mK a).2 ha, b, (mK b).2 hb, s, hs, rfl⟩
  have hS : IsCompact (elemSet r A) := by
    rw [e]
    refine (hKc.prod (hA.prod hKc)).image ?_
    exact (continuous_fst.mul ((diag_cont E n).comp (continuous_fst.comp continuous_snd))).mul
      (continuous_snd.comp continuous_snd)
  have hO : IsOpen (elemSet r A) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
    refine Filter.mem_of_superset ((hKo.preimage (f := fun g => (a * diagT E (Fin n) s)⁻¹ * g) (by fun_prop)).mem_nhds
      (by simpa [mul_assoc] using (mK b).1 hb)) fun g hg => ?_
    exact ⟨a, ha, _, (mK _).2 hg, s, hs, by group⟩
  have hT : UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) := by
    refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun g => ?_, HasCompactSupport.intro hS fun g hg => Set.indicator_of_notMem hg _⟩
    by_cases h : g ∈ elemSet r A
    · filter_upwards [hO.mem_nhds h] with y hy
      exact (Set.indicator_of_mem hy _).trans (Set.indicator_of_mem h (1 : GL (Fin n) E → ℂ)).symm
    · filter_upwards [hS.isClosed.isOpen_compl.mem_nhds h] with y hy
      exact (Set.indicator_of_notMem hy _).trans (Set.indicator_of_notMem h _).symm
  refine ⟨hO, hS, hT, hT, ?_⟩
  rintro _ ⟨a, ha, b, hb, s, hs, rfl⟩
  have hd : ∀ g ∈ ball (E := E) n r, valuation E (((GeneralLinearGroup.det g : Eˣ) : E) - 1) ≤ r := fun g hg => by
    simpa [GeneralLinearGroup.val_det_apply] using det_near h0 h1 hg
  refine ⟨s, hs, GeneralLinearGroup.det a * GeneralLinearGroup.det b, ?_, ?_⟩
  · rw [Units.val_mul]
    exact near_mul h1 (hd a ha) (hd b hb)
  · have hdiag : GeneralLinearGroup.det (diagT E (Fin n) s) = ∏ i, s i := by
      ext
      simp [GeneralLinearGroup.val_det_apply, val_diagT, Matrix.det_diagonal]
    rw [map_mul, map_mul, hdiag]
    simp only [mul_comm, mul_left_comm, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt.L
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FinTrace
section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem finsum_smul_comp {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W)
    (R : W →ₗ[ℂ] W) : ∑ᶠ g, a g • (L g ∘ₗ R) = (∑ᶠ g, a g • L g) ∘ₗ R := by
  letI := Fintype.ofFinite G
  simp only [finsum_eq_sum_of_fintype]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.smul_apply]

private theorem trace_finsum_smul {G W : Type} [Finite G] [AddCommGroup W] [Module ℂ W] (a : G → ℂ) (L : G → W →ₗ[ℂ] W) :
    LinearMap.trace ℂ W (∑ᶠ g, a g • L g) = ∑ᶠ g, a g * LinearMap.trace ℂ W (L g) := by
  letI := Fintype.ofFinite G
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [finsum_eq_sum_of_fintype, map_sum, map_smul, smul_eq_mul]

private theorem trace_step {G G' W W' : Type} [Finite G] [Finite G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (a : G' → ℂ) (L : G' → W' →ₗ[ℂ] W') (R : W' →ₗ[ℂ] W') (b : G → ℂ) (M : G → W →ₗ[ℂ] W) (R' : W →ₗ[ℂ] W) (hR' : R' = LinearMap.id)
    (c d d' : ℂ) (hc : c ≠ 0) (hd : d ≠ 0)
    (e : d' * LinearMap.trace ℂ W' (∑ᶠ g, a g • (L g ∘ₗ R)) = c * (d * LinearMap.trace ℂ W (∑ᶠ g, b g • (M g ∘ₗ R'))))
    (hne : ∑ᶠ g, b g * LinearMap.trace ℂ W (M g) ≠ 0) : ∑ᶠ g, a g • L g ≠ 0 := by
  subst hR'
  simp only [LinearMap.comp_id] at e
  rw [finsum_smul_comp, trace_finsum_smul] at e
  intro h0
  rw [h0, LinearMap.zero_comp, map_zero, mul_zero] at e
  exact mul_ne_zero hc (mul_ne_zero hd hne) e.symm

open scoped Classical in
private theorem normLift_eq {F F' : Type} [Field F] [Field F'] [Algebra F F'] (s : F' ≃ₐ[F] F') {n : ℕ} (f : GL (Fin n) F → ℂ) :
    normLift s f = GlobalTheory.Shin.shLift s f := by
  have e : ∀ δ : GL (Fin n) F', GlobalTheory.LBC.norm F s δ = GlobalTheory.Shin.nrm s δ := by
    intro δ
    unfold GlobalTheory.LBC.norm GlobalTheory.Shin.nrm GlobalTheory.Shin.nrmG
    congr 1
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      ext a b
      rfl
  funext δ
  have e2 : IsFinNorm s δ = GlobalTheory.Shin.IsNorm s δ := by
    funext γ
    unfold IsFinNorm GlobalTheory.Shin.IsNorm
    rw [e]
    rfl
  have aux : ∀ P Q : GL (Fin n) F → Prop, P = Q →
      (if h : ∃ γ, P γ then f h.choose else 0) = (if h : ∃ γ, Q γ then f h.choose else 0) := by
    rintro P _ rfl; rfl
  exact aux _ _ e2

private theorem twTr_level (hAct : FinAct) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (fb : GL (Fin n) 𝓀[k] → ℂ) (A : V →ₗ[ℂ] V)
    (hA : ∀ x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n)), A x ∈ fixed ρ (GlobalTheory.SplitWeil.KOne k (Fin n))) :
    GlobalTheory.BCT.twTr ρ (KO k n) (K1 (IsLocalRing.residue 𝒪[k]) n) (infl (IsLocalRing.residue 𝒪[k]) fb) A =
      (Nat.card (GL (Fin n) 𝓀[k]) : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (GlobalTheory.LocGL.levelZero ρ g ∘ₗ A.restrict hA)) := by
  letI := Fintype.ofFinite 𝓀[k]
  obtain ⟨hl, r, hr, hT⟩ := hAct k 𝓀[k] (IsLocalRing.residue 𝒪[k]) IsLocalRing.residue_surjective n V ρ
  have er : r = GlobalTheory.LocGL.levelZero ρ := by
    ext g x
    obtain ⟨y, rfl⟩ := hl g
    have e1 := hr y x
    have e2 := GlobalTheory.LocGL.levelZero_apply ρ ((GlobalTheory.LocGL.toKO k (Fin n)) y) x
    have e3 : GlobalTheory.LocGL.redK k (Fin n) ((GlobalTheory.LocGL.toKO k (Fin n)) y) = GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) y := by
      simp [GlobalTheory.LocGL.redK]
    rw [e3] at e2
    exact e1.trans e2.symm
  subst er
  exact hT fb A hA

private theorem exists_isRes (hRes : ResEx) {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K] (hu : PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k K)
    [Algebra 𝓀[k] 𝓀[K]] [Fintype 𝓀[k]]
    (hinc : ∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x →
      IsLocalRing.residue _ y = algebraMap 𝓀[k] 𝓀[K] (IsLocalRing.residue _ x))
    (s : 𝓀[K] ≃ₐ[𝓀[k]] 𝓀[K]) (hs : ∀ z, s z = z ^ Nat.card 𝓀[k]) :
    ∃ t : K ≃ₐ[k] K, IsRes (IsLocalRing.residue 𝒪[k]) (IsLocalRing.residue 𝒪[K]) t s := by
  obtain ⟨F₀, F₁, _, _, _, _, _, rk, rK, t, sb, h⟩ := hRes k K hu

  have kk : ∀ x : 𝒪[k], rk x = 0 ↔ IsLocalRing.residue 𝒪[k] x = 0 := by
    intro x
    have hm : RingHom.ker rk = IsLocalRing.maximalIdeal 𝒪[k] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rk h.onto₀)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  have kK : ∀ x : 𝒪[K], rK x = 0 ↔ IsLocalRing.residue 𝒪[K] x = 0 := by
    intro x
    have hm : RingHom.ker rK = IsLocalRing.maximalIdeal 𝒪[K] :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective rK h.onto₁)
    rw [IsLocalRing.residue_eq_zero_iff, ← hm, RingHom.mem_ker]
  let φ₀ : 𝓀[k] →+* F₀ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[k]) rk
    fun a ha => (kk a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  let φ₁ : 𝓀[K] →+* F₁ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[K]) rK
    fun a ha => (kK a).2 ((IsLocalRing.residue_eq_zero_iff a).2 ha)
  have hφ₀ : ∀ x, φ₀ (IsLocalRing.residue _ x) = rk x := fun x => rfl
  have hφ₁ : ∀ x, φ₁ (IsLocalRing.residue _ x) = rK x := fun x => rfl
  have b₀ : Function.Bijective φ₀ := ⟨φ₀.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₀ z
    exact ⟨_, hφ₀ x⟩⟩
  have b₁ : Function.Bijective φ₁ := ⟨φ₁.injective, fun z => by
    obtain ⟨x, rfl⟩ := h.onto₁ z
    exact ⟨_, hφ₁ x⟩⟩
  let e₀ : 𝓀[k] ≃+* F₀ := RingEquiv.ofBijective φ₀ b₀
  let e₁ : 𝓀[K] ≃+* F₁ := RingEquiv.ofBijective φ₁ b₁
  have hint : ∀ x : 𝒪[k], ∃ y : 𝒪[K], (y : K) = algebraMap k K x := by
    intro x
    have h1 : (x : k) ≤ᵥ 1 := (Valuation.Compatible.vle_iff_le (v := valuation k) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 x.2)
    have h2 : algebraMap k K x ≤ᵥ algebraMap k K 1 := ValuativeExtension.vle_iff_vle.2 h1
    rw [map_one] at h2
    exact ⟨⟨algebraMap k K x, (Valuation.mem_integer_iff _ _).2 (by simpa using (Valuation.Compatible.vle_iff_le (v := valuation K) _ _).1 h2)⟩, rfl⟩
  have hc : (algebraMap F₀ F₁).comp e₀.toRingHom = e₁.toRingHom.comp (algebraMap 𝓀[k] 𝓀[K]) := by
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy⟩ := hint x
    show algebraMap F₀ F₁ (φ₀ _) = φ₁ (algebraMap 𝓀[k] 𝓀[K] _)
    rw [← hinc x y hy, hφ₀, hφ₁, h.inc x y hy]
  have hq : Fintype.card F₀ = Nat.card 𝓀[k] := by
    rw [← Nat.card_eq_fintype_card]; exact (Nat.card_congr e₀.toEquiv).symm
  refine ⟨t, ?_, IsLocalRing.residue_surjective, IsLocalRing.residue_surjective, hinc, ?_, ?_⟩
  · rw [← h.deg]
    exact Algebra.finrank_eq_of_equiv_equiv e₀ e₁ hc
  · intro x y hy
    have h1 : rK y = rK x ^ Nat.card 𝓀[k] := by rw [h.gal x y hy, h.frob, hq]
    have h2 : rK (y - x ^ Nat.card 𝓀[k]) = 0 := by rw [map_sub, map_pow, h1, sub_self]
    have h3 := (kK _).1 h2
    rw [map_sub, map_pow, sub_eq_zero] at h3
    rw [h3, hs]
  · intro z
    rw [hs, Nat.card_eq_fintype_card]

theorem finTrace :
    ResEx → FinAct → InflFacts → FrobFacts → InflTrace → UpperTheory.Gal.InertialTypesAlt.FinTrace := by
  intro hRes hAct hInfl hFrob hIT F E _ _ _ _ _ _ _ _ hp n hn π P hcj hbc v w hsp hu τ τ' hτ hτ' _ hinc s hs f hf hne
  obtain ⟨w', hw'⟩ := UpperTheory.V.Z.Tf.Orb.placeUniq_holds F E hp v hsp
  have hw : ∀ x : PlacesOver E v, x = w := fun x => (hw' x).trans (hw' w).symm
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hp.pos
  haveI : Fact (Module.finrank F E).Prime := ⟨hp⟩
  haveI : IsCyclic (E ≃ₐ[F] E) := by
    apply isCyclic_of_prime_card (p := Module.finrank F E)
    exact IsGalois.card_aut_eq_finrank F E
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := E ≃ₐ[F] E)
  obtain ⟨i1, i2, i3, i4, s0, hs0, hr, h1, h2, h3⟩ := UpperTheory.V.Z.Tf.Orb.placeData_holds F E σ hσ v w hw
  letI := Fintype.ofFinite 𝓀[v.adicCompletion F]
  letI := Fintype.ofFinite 𝓀[w.1.adicCompletion E]
  have hcm : ∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x := h1
  obtain ⟨t, ht⟩ := exists_isRes hRes (h3 (hu w))
    (fun x y hy => hinc x y (hy.trans (hcm x).symm)) s hs
  obtain ⟨I, c, hI, hc, H⟩ := hIT F E hp n hn π P hcj hbc v w hw hu hcm _ _ _ _ t s ht τ τ' hτ hτ'
  have hst := ((hFrob _ _ _ _ _ _ t s ht).2 n).1
  have hA : ∀ x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)),
      I x ∈ fixed τ'.ρ (GlobalTheory.SplitWeil.KOne (w.1.adicCompletion E) (Fin n)) :=
    fun x hx => hI.mem_fixed hst hx
  have hB : ∀ x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)),
      (LinearMap.id : τ.V →ₗ[ℂ] τ.V) x ∈ fixed τ.ρ (GlobalTheory.SplitWeil.KOne (v.adicCompletion F) (Fin n)) :=
    fun x hx => hx
  have e := H f hf
  rw [normLift_eq, twTr_level hAct n τ'.ρ _ I hA, twTr_level hAct n τ.ρ f _ hB] at e
  have hid : (LinearMap.id : τ.V →ₗ[ℂ] τ.V).restrict hB = LinearMap.id := by
    ext x
    rfl
  have hcard : (Nat.card (GL (Fin n) 𝓀[v.adicCompletion F]) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  exact trace_step _ _ _ _ _ _ hid _ _ _ hc hcard e hne

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFacts
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.DZA

namespace UpperTheory.Gal.InertialTypesAlt.L

section

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K]

private theorem mem_int (s : K ≃ₐ[k] K) (x : 𝒪[K]) : s (x : K) ∈ 𝒪[K] := by
  change valuation K (s (x : K)) ≤ 1
  rw [GroundTheory.LocalField.valuation_algEquiv_apply]
  exact x.2

private def resO (s : K ≃ₐ[k] K) : 𝒪[K] →+* 𝒪[K] :=
  (s.toAlgHom.toRingHom.comp (algebraMap 𝒪[K] K)).codRestrict 𝒪[K] fun x => mem_int s x

private theorem resO_coe (s : K ≃ₐ[k] K) (x : 𝒪[K]) : ((resO s x : 𝒪[K]) : K) = s (x : K) := rfl

private theorem resO_inv (s : K ≃ₐ[k] K) (x : 𝒪[K]) : resO s (resO s⁻¹ x) = x := by
  apply Subtype.ext
  rw [resO_coe, resO_coe]
  change s (s.symm (x : K)) = x
  exact s.apply_symm_apply _

private theorem map_res (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact resO_coe s _

private theorem map_res_inv (s : K ≃ₐ[k] K) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map (resO s) (GeneralLinearGroup.map (resO s⁻¹) y) = y := by
  ext i j
  simp [resO_inv]

variable {F₀ F₁ : Type} [Field F₀] [Fintype F₀] [Field F₁] [Algebra F₀ F₁]
    {rk : 𝒪[k] →+* F₀} {rK : 𝒪[K] →+* F₁} {s : K ≃ₐ[k] K} {sb : F₁ ≃ₐ[F₀] F₁}

private theorem map_res_red (h : IsRes rk rK s sb) (n : ℕ) (y : GL (Fin n) 𝒪[K]) :
    GeneralLinearGroup.map rK (GeneralLinearGroup.map (resO s) y) =
      GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y) := by
  ext i j
  simp [GlobalTheory.LBC.galAct]
  exact h.gal _ _ (resO_coe s _)

private theorem pow_red (h : IsRes rk rK s sb) (j : ℕ) (x : 𝒪[K]) :
    (sb ^ j) (rK x) = rK (resO (s ^ j) x) := by
  induction j generalizing x with
  | zero =>
    have hx : resO (s ^ 0) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  | succ j ih =>
    rw [pow_succ, AlgEquiv.mul_apply, ← h.gal x (resO s x) (resO_coe s x), ih]
    congr 1

private theorem finrank_dvd [Fintype F₁] (h : IsRes rk rK s sb) :
    Module.finrank k K ∣ orderOf s := by
  have hsb : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [h.frob z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hpow : sb ^ orderOf s = 1 := by
    ext z
    obtain ⟨x, rfl⟩ := h.onto₁ z
    rw [pow_red h, pow_orderOf_eq_one]
    have hx : resO (1 : K ≃ₐ[k] K) x = x := Subtype.ext (resO_coe _ x)
    rw [hx]
    rfl
  have hord : orderOf sb = Module.finrank F₀ F₁ := by
    rw [hsb]
    exact FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic F₀ F₁
  rw [← h.deg, ← hord]
  exact orderOf_dvd_of_pow_eq_one hpow

private theorem mem_zpowers_of_isRes [IsGalois k K] [Fintype F₁] (h : IsRes rk rK s sb)
    (τ : K ≃ₐ[k] K) : τ ∈ Subgroup.zpowers s := by
  have hdvd := finrank_dvd h
  have hcard : Nat.card (K ≃ₐ[k] K) = Module.finrank k K := IsGalois.card_aut_eq_finrank k K
  have hle : orderOf s ∣ Nat.card (K ≃ₐ[k] K) := orderOf_dvd_natCard s
  have heq : Nat.card (Subgroup.zpowers s) = Nat.card (K ≃ₐ[k] K) := by
    rw [Nat.card_zpowers]
    exact Nat.dvd_antisymm hle (hcard ▸ hdvd)
  rw [Subgroup.eq_top_of_card_eq _ heq]
  exact Subgroup.mem_top τ

end

end UpperTheory.Gal.InertialTypesAlt.L

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.frobFacts :
    UpperTheory.Gal.InertialTypesAlt.L.FrobFacts := by
  intro k K _ _ _ _ _ _ _ _ _ _ _ _ F₀ F₁ _ _ _ _ _ rk rK s sb h
  have key : ∀ (n : ℕ) (z : GL (Fin n) F₁), GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n z) = z := by
    intro n z
    rw [← MonoidHom.comp_apply, ← GlobalTheory.LBC.galAct_mul, inv_mul_cancel, GlobalTheory.LBC.galAct_one]
    rfl
  refine ⟨mem_zpowers_of_isRes h, fun n => ⟨?_, ?_, fun y =>
    ⟨GeneralLinearGroup.map (resO s) y, map_res s n y, map_res_red h n y⟩⟩⟩
  · have hinj : Function.Injective (GlobalTheory.LBC.galAct sb n) := by
      intro a b hab
      calc a = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n a) := (key n a).symm
        _ = GlobalTheory.LBC.galAct sb⁻¹ n (GlobalTheory.LBC.galAct sb n b) := by rw [hab]
        _ = b := key n b
    unfold GlobalTheory.LBC.IsStable K1
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨GeneralLinearGroup.map (resO s) y, ?_, map_res s n y⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
      rw [map_res_red h, hy, map_one]
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨GeneralLinearGroup.map (resO s⁻¹) y, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy ⊢
        apply hinj
        rw [← map_res_red h, map_res_inv, hy, map_one]
      · rw [← map_res, map_res_inv]
  · unfold GlobalTheory.LBC.IsStable KO
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨GeneralLinearGroup.map (resO s) y, map_res s n y⟩
    · rintro _ ⟨y, rfl⟩
      exact ⟨GeneralLinearGroup.map (algebraMap 𝒪[K] K) (GeneralLinearGroup.map (resO s⁻¹) y),
        ⟨_, rfl⟩, by rw [← map_res, map_res_inv]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmul
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem quotInt_smul {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (c : ℂ) (Φ : X → ℂ) :
    quotInt μ u j ν (c • Φ) = c * quotInt μ u j ν Φ := by
  unfold quotInt
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  · simp

private theorem orb_smul {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace (GL (Fin n) R)]
    (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ})) (c : ℂ)
    (f : GL (Fin n) R → ℂ) : orb μ γ ν (c • f) = c * orb μ γ ν f := by
  unfold orb
  exact quotInt_smul μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν c
    (fun x => f (x⁻¹ * γ * x))

theorem matchSmul : MatchSmul := by
  intro F E _ _ _ _ _ σ n v c hc φ f h
  intro _ _ _ _ mE mF h1 h2 h3 h4 γ hγ ν hν
  obtain ⟨hA, hB⟩ := h mE mF h1 h2 h3 h4 γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [hA δ hδ, one_mul, orb_smul]
  · have := hB hn
    rw [orb_smul] at this
    exact (mul_eq_zero.1 this).resolve_left hc

end UpperTheory.Gal.InertialTypesAlt.L

end
end

