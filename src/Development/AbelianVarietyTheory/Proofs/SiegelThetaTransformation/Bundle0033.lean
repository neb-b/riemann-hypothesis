module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MeasurePreservingMulLeft
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

section DoubleCoset
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
theorem _root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen (Γ K : Subgroup G) (hK : IsOpen (K : Set G)) (a : G) :
    IsOpen {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} := by
  have hunion : {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} =
      ⋃ γ ∈ Γ, (fun k => γ * a * k) '' (K : Set G) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨γ, hγ, k, hk, rfl⟩
  rw [hunion]
  exact isOpen_biUnion fun γ _ => isOpenMap_mul_left (γ * a) _ hK


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem _root_.GlobalTheory.Ker.tsum_indicator_coset (Γ K : Subgroup G) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) (x : G) :
    ∑' γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ • x)
      = ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) *
        {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}.indicator 1 x := by
  by_cases hx : x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k}
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    obtain ⟨γ₀, hγ₀, k₀, hk₀, rfl⟩ := hx
    set T : Set Γ := {γ | a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K} with hT
    have hterm : ∀ γ : Γ, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal)
        (γ • (γ₀ * a * k₀)) = T.indicator (1 : Γ → ENNReal) γ := by
      intro γ
      by_cases hγ : γ ∈ T
      · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem]
        · rfl
        · exact hγ
      · rw [Set.indicator_of_notMem hγ, Set.indicator_of_notMem]
        exact hγ
    simp_rw [hterm]
    rw [← tsum_subtype T (1 : Γ → ENNReal)]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    have hinj : Function.Injective (fun γ : Γ => (γ : G) * γ₀) :=
      fun γ δ hγδ => Subtype.ext (mul_right_cancel hγδ)
    have himg : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K} = (fun γ : Γ => (γ : G) * γ₀) '' T := by
      ext δ
      constructor
      · rintro ⟨hδ, hδK⟩
        refine ⟨⟨δ * γ₀⁻¹, Γ.mul_mem hδ (Γ.inv_mem hγ₀)⟩, ?_, by simp⟩
        show a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) ∈ K
        have heq : a⁻¹ * (δ * γ₀⁻¹ * (γ₀ * a * k₀)) = a⁻¹ * δ * a * k₀ := by group
        rw [heq]
        exact K.mul_mem hδK hk₀
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨Γ.mul_mem γ.2 hγ₀, ?_⟩
        have hγ' : a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) ∈ K := hγ
        have heq : a⁻¹ * ((γ : G) * γ₀) * a = a⁻¹ * ((γ : G) * (γ₀ * a * k₀)) * k₀⁻¹ := by group
        rw [heq]
        exact K.mul_mem hγ' (K.inv_mem hk₀)
    rw [← hinj.encard_image, ← himg, ← hfin.cast_ncard_eq, ENat.toENNReal_coe]
  · rw [Set.indicator_of_notMem hx, mul_zero]
    refine tsum_eq_zero_iff.2 fun γ => Set.indicator_of_notMem ?_ _
    intro hmem
    have hk : a⁻¹ * ((γ : G) * x) ∈ K := hmem
    exact hx ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, _, hk, by group⟩

variable [MeasurableSpace G] [BorelSpace G]

end DoubleCoset

open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
private theorem measure_fd_inter_doubleCoset_mul_ncard_eq {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (D : Set G)
    (hD : IsFundamentalDomain Γ D ν) (hK : IsOpen (K : Set G)) (a : G)
    (hfin : {γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.Finite) :
    ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} ∩ D) *
      ({γ : G | γ ∈ Γ ∧ a⁻¹ * γ * a ∈ K}.ncard : ENNReal) = ν K := by
  have hC : MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * a * k} :=
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK a).measurableSet
  have hmeasK : MeasurableSet ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)) :=
    hK.measurableSet.preimage (measurable_const_mul _)
  have hwhole : ∫⁻ x, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator 1 x ∂ν = ν K := by
    rw [lintegral_indicator_one hmeasK, measure_preimage_mul]
  have hinv := (Equiv.inv Γ).tsum_eq (fun γ : Γ =>
    ∫⁻ x in D, ((fun y => a⁻¹ * y) ⁻¹' (K : Set G)).indicator (1 : G → ENNReal) (γ⁻¹ • x) ∂ν)
  simp only [Equiv.inv_apply, inv_inv] at hinv
  rw [← hwhole, hD.lintegral_eq_tsum', ← hinv, ← lintegral_tsum]
  · simp_rw [_root_.GlobalTheory.Ker.tsum_indicator_coset Γ K a hfin]
    rw [lintegral_const_mul _ (measurable_one.indicator hC), lintegral_indicator_one hC,
      Measure.restrict_apply hC, mul_comm]
  · intro γ
    exact ((measurable_one.indicator hmeasK).comp (measurable_const_smul γ)).aemeasurable


open Matrix Complex NumberField MeasureTheory in
open scoped ComplexConjugate ComplexOrder Real Classical in
theorem _root_.GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant] (Γ K : Subgroup G) [Countable Γ] (𝓖 : Set G), IsFundamentalDomain Γ 𝓖 ν → IsOpen (K : Set G) → ν K ≠ ⊤ → ∀ (ι : Type) [Fintype ι] (h : ι → G), (∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k) → (∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.Finite) → ∀ F : G → ℂ, (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ k ∈ K, ∀ x, F (x * k) = F x) → ν 𝓖 ≠ ⊤ ∧ IntegrableOn F 𝓖 ν ∧ ∫ x in 𝓖, F x ∂ν = ((ν K).toReal : ℂ) * ∑ i, (({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ℕ) : ℂ)⁻¹ * F (h i) := by
  intro G _ _ _ _ _ ν _ Γ K _ 𝓖 h𝓖 hK hKtop ι _ h huniq hfin F hFΓ hFK
  have hCmeas : ∀ i, MeasurableSet {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} := fun i =>
    (_root_.GlobalTheory.Ker.isOpen_doubleCoset_of_isOpen Γ K hK (h i)).measurableSet
  have hpos : ∀ i, {γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard ≠ 0 := fun i =>
    ((Set.ncard_pos (hfin i)).2 ⟨1, Γ.one_mem, by simpa using K.one_mem⟩).ne'
  have hCG : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) =
      ν K / ({γ : G | γ ∈ Γ ∧ (h i)⁻¹ * γ * h i ∈ K}.ncard : ENNReal) := by
    intro i
    rw [ENNReal.eq_div_iff (by exact_mod_cast hpos i) (ENNReal.natCast_ne_top _), mul_comm]
    exact measure_fd_inter_doubleCoset_mul_ncard_eq ν Γ K 𝓖 h𝓖 hK (h i) (hfin i)
  have hCGtop : ∀ i, ν ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) ≠ ⊤ := by
    intro i
    rw [hCG i]
    exact (ENNReal.div_lt_top hKtop (by exact_mod_cast hpos i)).ne
  have h𝓖top : ν 𝓖 ≠ ⊤ := by
    have hsub : 𝓖 ⊆ ⋃ i, ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} ∩ 𝓖) := fun x hx =>
      Set.mem_iUnion.2 ⟨(huniq x).exists.choose, (huniq x).exists.choose_spec, hx⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    exact ENNReal.sum_ne_top.2 fun i _ => hCGtop i
  have hdecomp : ∀ x, F x =
      ∑ i, {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i)) x := by
    intro x
    obtain ⟨i, hi, hiuniq⟩ := huniq x
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem (show x ∈ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k} from hi)]
      obtain ⟨γ, hγ, k, hk, rfl⟩ := hi
      rw [hFK k hk, hFΓ γ hγ]
    · intro j _ hj
      exact Set.indicator_of_notMem
        (show x ∉ {x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h j * k} from fun hx => hj (hiuniq j hx)) _
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  have hint : ∀ i, IntegrableOn
      ({x : G | ∃ γ ∈ Γ, ∃ k ∈ K, x = γ * h i * k}.indicator (fun _ => F (h i))) 𝓖 ν := by
    intro i
    refine (integrable_indicator_iff (hCmeas i)).2 ?_
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (hCmeas i)]
    exact hCGtop i
  refine ⟨h𝓖top, ?_, ?_⟩
  · exact (integrable_finsetSum _ fun i _ => hint i).congr
      (ae_of_all _ fun x => (hdecomp x).symm)
  · refine (congrArg (fun f : G → ℂ => ∫ x in 𝓖, f x ∂ν) (funext hdecomp)).trans ?_
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_indicator_const _ (hCmeas i), measureReal_def, Measure.restrict_apply (hCmeas i),
      hCG i, ENNReal.toReal_div, ENNReal.toReal_natCast, Complex.real_smul]
    push_cast
    ring

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsStabiliserInvariantPullBoundedSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.Pull

open GlobalTheory.Dict.Extend

variable {E : Type} [Field E] {r : ℕ}

section Cast

variable {Ψ Ψ' : Finset (E →+* ℂ)}

theorem cast_symm (h : Ψ = Ψ') (x : Frame Ψ r) : castFr h.symm (castFr h x) = x := rfl

theorem cast_lact (h : Ψ = Ψ') (a : GL (Fin r) E) (x : Frame Ψ r) :
    castFr h (lact a x) = lact a (castFr h x) := rfl

theorem cast_rmul (h : Ψ = Ψ') (x b : Frame Ψ r) :
    castFr h (rmul x b) = rmul (castFr h x) (castFr h b) := rfl

theorem cast_bor (h : Ψ = Ψ') {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : castFr h b ∈ Bor Ψ' r := by
  subst h; exact hb

theorem cast_GG (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {p p' : ℕ} (hp : p = p')
    {x : Frame Ψ r} (hx : x ∈ GG Ψ G p) : castFr h x ∈ GG Ψ' G' p' := by
  subst h hG hp; exact hx

theorem cast_diff (h : Ψ = Ψ') : Differentiable ℂ (castFr (r := r) h) := by
  subst h; exact differentiable_id

theorem cast_bchar (h : Ψ = Ψ') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (b : Frame Ψ r) :
    bchar la' (castFr h b) = bchar la b := by
  subst h
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

theorem cast_wt (h : Ψ = Ψ') {G G' : Matrix (Fin r) (Fin r) E} (hG : G = G') {la : Wt Ψ r} {la' : Wt Ψ' r}
    (hl : ∀ (τ : Ψ') i, la' τ i = la ⟨τ.1, h ▸ τ.2⟩ i) (x : Frame Ψ' r) :
    (∏ τ, ∏ i, ‖dmin G (castFr h.symm x) τ (Fin.succ i) / dmin G (castFr h.symm x) τ i.castSucc‖ ^
        (-(la τ i : ℝ) / 2)) =
      ∏ τ, ∏ i, ‖dmin G' x τ (Fin.succ i) / dmin G' x τ i.castSucc‖ ^ (-(la' τ i : ℝ) / 2) := by
  subst h hG
  obtain rfl : la' = la := funext fun τ => funext fun i => hl τ i
  rfl

end Cast

theorem inv_mulVec (a : GL (Fin r) E) (v : Fin r → E) :
    ((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv (a : GL (Fin r) E) (v : Fin r → E) :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

variable [NumberField E]

theorem mem_mapL {a : GL (Fin r) E} {L : Lt E r} {v : Fin r → E} :
    (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ mapL a L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, e⟩
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = (a : Matrix (Fin r) (Fin r) E) *ᵥ v := e
    have : w = v := by rw [← inv_mulVec a w, e', inv_mulVec]
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

variable [IsCMField E] {X : Data E r}

theorem isUn_inv {a : GL (Fin r) E} (ha : IsUn X a) : IsUn X a⁻¹ := fun x y => by
  rw [← ha, mulVec_inv, mulVec_inv]

theorem isUn_mul {a b : GL (Fin r) E} (ha : IsUn X a) (hb : IsUn X b) : IsUn X (a * b) := fun x y => by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]

theorem conj_mem {X' : Data E r} (hG : X'.Gm = X.Gm) {a g : GL (Fin r) E} {M : ℕ} (ha : IsUn X a) (hg : IsUn X g)
    (hfix : mapL g (mapL a X'.Λ) = mapL a X'.Λ)
    (hM : ∀ u ∈ mapL a X'.Λ, ∃ u' ∈ mapL a X'.Λ, (g : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')
    (hP : HasPrinc X' M) : a⁻¹ * g * a ∈ X'.Γ := by
  have hc : mapL (a⁻¹ * g * a) X'.Λ = X'.Λ := by
    rw [mapL_mul, mapL_mul, hfix, ← mapL_mul, inv_mul_cancel, mapL_one]
  refine hP _ ⟨?_, fun x => ?_⟩ fun v hv => ?_
  · rw [hG]
    exact isUn_mul (isUn_mul (isUn_inv ha) hg) ha
  · rw [← mem_mapL (a := a⁻¹ * g * a), hc]
  · obtain ⟨u', ⟨w, hw, e⟩, hu⟩ := hM _ (mem_mapL.2 hv)
    have e' : (a : Matrix (Fin r) (Fin r) E) *ᵥ w = u' := e
    refine ⟨w, hw, ?_⟩
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hu, ← e',
      Matrix.mulVec_add, Matrix.mulVec_smul, inv_mulVec, inv_mulVec]

end GlobalTheory.Dict.Pull


open GlobalTheory.Dict.Extend GlobalTheory.Dict.Pull in
theorem GlobalTheory.Dict.isStabForm_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X' X : Data E r) (h : SameSp X' X) (ga : GL (Fin r) E) (la' : Wt X'.Ψ r) (la : Wt X.Ψ r) (Δ : Subgroup (GL (Fin r) E)) (M : ℕ) (P : Frame X'.Ψ r → ℂ), IsUn X ga → (∀ (τ : X.Ψ) i, la τ i = la' ⟨τ.1, by rw [h.psi]; exact τ.2⟩ i) → (∀ g' ∈ Δ, IsUn X g' ∧ (mapL g' (mapL ga X'.Λ) = mapL ga X'.Λ → ∀ u ∈ mapL ga X'.Λ, ∃ u' ∈ mapL ga X'.Λ, (g' : Matrix (Fin r) (Fin r) E) *ᵥ u = u + M • u')) → HasPrinc X' M → ChiOne X' la' → X'.IsBddSec la' P → IsStabForm X Δ (mapL ga X'.Λ) la (fun x => P (castFr h.psi.symm (lact ga⁻¹ x))) ∧ ∀ Q : Frame X.Ψ r → ℂ, DifferentiableOn ℂ Q X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Q (rmul x b) = bchar la b * Q x) → DifferentiableOn ℂ (fun x => Q (lact ga (castFr h.psi x))) X'.dom ∧ ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom ∧ castFr h.psi.symm (lact ga⁻¹ (lact ga (castFr h.psi x))) = x ∧ ∀ b ∈ Bor X'.Ψ r, Q (lact ga (castFr h.psi (rmul x b))) = bchar la' b * Q (lact ga (castFr h.psi x)) := by
  intro E _ _ _ r X' X h ga la' la Δ M P hga hl hΔ hP hχ hb
  obtain ⟨⟨hd, hbor, hinv⟩, C, hC⟩ := hb
  have m1 : ∀ x ∈ X.dom, castFr h.psi.symm (lact ga⁻¹ x) ∈ X'.dom := fun x hx =>
    cast_GG h.psi.symm h.gm.symm h.p0.symm (lact_mem (isUn_inv hga) hx)
  have m2 : ∀ x ∈ X'.dom, lact ga (castFr h.psi x) ∈ X.dom := fun x hx =>
    lact_mem hga (cast_GG h.psi h.gm h.p0 hx)
  refine ⟨⟨?_, ?_, ?_, C, ?_⟩, fun Q hQ hQb => ⟨?_, fun x hx => ⟨m2 x hx, ?_, fun b hb => ?_⟩⟩⟩
  · exact hd.comp ((cast_diff h.psi.symm).comp (differentiable_lact ga⁻¹)).differentiableOn m1
  · intro x hx b hb
    rw [lact_rmul, cast_rmul, hbor _ (m1 x hx) _ (cast_bor h.psi.symm hb), ← cast_bchar h.psi hl]
    rfl
  · intro g hg hfix x hx
    have hm := conj_mem h.gm hga (hΔ g hg).1 hfix ((hΔ g hg).2 hfix) hP
    have e : lact ga⁻¹ (lact g x) = lact (ga⁻¹ * g * ga) (lact ga⁻¹ x) := by
      rw [lact_lact, lact_lact, mul_inv_cancel_right]
    show P (castFr h.psi.symm (lact ga⁻¹ (lact g x))) = _
    rw [e, cast_lact, hinv _ hm _ (m1 x hx), hχ _ hm, _root_.one_mul]
  · intro x hx
    refine le_of_eq_of_le ?_ (hC _ (m1 x hx))
    unfold Data.pnorm
    rw [cast_wt h.psi h.gm hl]
    simp only [dmin_lact (isUn_inv hga)]
  · exact hQ.comp ((differentiable_lact ga).comp (cast_diff h.psi)).differentiableOn m2
  · rw [lact_lact, inv_mul_cancel, lact_one, cast_symm]
  · rw [cast_rmul, lact_rmul, hQb _ (m2 x hx) _ (cast_bor h.psi hb), cast_bchar h.psi hl]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KZeroOnFrConstEntire
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.Ker

private theorem det_sgnM_eq_prod_sgn {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) : (sgnM X).det = ∏ a : Fin r, ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) := by
  simp [sgnM, Matrix.det_diagonal]

theorem normSq_det_of_isONFr {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {X : Data E r} {x : Frame X.Ψ r} (hx : IsONFr X x) (τ : X.Ψ) :
    normSq (mat x τ).det = ‖(X.Gm.map τ.1).det‖⁻¹ := by

  have hdet := congrArg Matrix.det (hx τ)
  rw [GlobalTheory.SW.Slab.det_gram, det_sgnM_eq_prod_sgn X] at hdet
  have hG : (X.Gm.map τ.1).det = τ.1 X.Gm.det := (RingHom.map_det τ.1 X.Gm).symm
  have hn := congrArg norm hdet
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_prod] at hn
  simp only [GlobalTheory.SW.Slab.norm_sgn, Finset.prod_const_one] at hn
  rw [hG, Complex.normSq_eq_norm_sq]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← hn]
  ring

theorem kZero_onFr_const_entire : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∃ κ : ℝ, 0 < κ ∧ ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ kZero X idx x x (0 : Fin n → Fin g → ℂ) 0 = κ) ∧ ∀ x₁ ∈ X.dom, ∀ x₂ ∈ X.dom, Differentiable ℂ (fun p : (Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ) => kZero X idx x₁ x₂ p.1 p.2) := by
  intro E _ _ _ r X g q0 hr bas idx n _ _
  refine ⟨⟨∏ τ : X.Ψ, ‖(X.Gm.map τ.1).det‖⁻¹ ^ (n / 2), ?_, fun x hx => ⟨?_, ?_⟩⟩, ?_⟩
  ·
    refine Finset.prod_pos fun τ _ => pow_pos (inv_pos.mpr (norm_pos_iff.mpr ?_)) _
    exact GlobalTheory.SW.KernSym.det_map_Gm X τ
  ·
    obtain ⟨δ₀, hδ₀, hs⟩ := GlobalTheory.SW.thin_slab E r X
    obtain ⟨-, hsub, hon, -⟩ := hs δ₀ hδ₀ le_rfl
    exact hsub (hon x hx)
  ·

    rw [GlobalTheory.SW.KernSym.kZero_ortho idx hx]
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun τ _ => by rw [normSq_det_of_isONFr hx τ]
  ·
    intro x₁ _ x₂ _ p
    exact (GlobalTheory.SW.KernSym.analyticAt_kZero X idx x₁ x₂ p).differentiableAt

end GlobalTheory.Ker
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.PolyDerivLetterPushforwardEqColumnAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence


open GlobalTheory.Dict.ColPoly in
theorem GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (s : c.F →+* ℂ) (r g : ℕ) (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = relab c s (e j).1) → ∀ (h : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) (F : (Fin n → Fin g → ℂ) → ℂ), AnalyticOnNhd ℂ F Set.univ → I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h P))) (letterDir X hr idx) F 0 = I2.polyDeriv (MvPolynomial.rename eL (MvPolynomial.map s P)) (letterDir X hr idx) (fun z => F (Dict.hAct X idx h z)) 0 := by
  intro E _ _ _ H Dw l c s r g X idx e q0 n hr eL hdir htype h P F hF
  have hF' : ContDiff ℂ (⊤ : ℕ∞) F := hF.contDiff
  let a : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → ℂ := fun v k =>
    s (Formalism.L2.Pj.embF c (eL.symm v).1 (h k (eL.symm v).2.2))
  let j : Harm.Var X.Ψ q0 X.p0 (Fin n) → Fin n → Harm.Var X.Ψ q0 X.p0 (Fin n) := fun v k =>
    eL ⟨(eL.symm v).1, (eL.symm v).2.1, k⟩
  let Φ : MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ →ₐ[ℂ] MvPolynomial (Harm.Var X.Ψ q0 X.p0 (Fin n)) ℂ :=
    MvPolynomial.aeval fun v => ∑ k, MvPolynomial.C (a v k) * MvPolynomial.X (j v k)
  have ha : ∀ v k, a (eL v) k = s (Formalism.L2.Pj.embF c v.1 (h k v.2.2)) := fun v k => by
    simp only [a]; rw [Equiv.symm_apply_apply]
  have hj : ∀ v k, j (eL v) k = eL ⟨v.1, v.2.1, k⟩ := fun v k => by
    simp only [j]; rw [Equiv.symm_apply_apply]
  have hΦ : ∀ Q : MvPolynomial (LtN Dw n) c.F,
      MvPolynomial.rename eL (MvPolynomial.map s (pushLet c h Q)) =
        Φ (MvPolynomial.rename eL (MvPolynomial.map s Q)) := by
    intro Q
    induction Q using MvPolynomial.induction_on with
    | C x => simp
    | add P Q hP hQ => simp only [map_add (f := _), hP, hQ]
    | mul_X P v hP =>
      simp only [map_mul, hP]
      congr 1
      simp [pushLet, letB, Φ, ha, hj]
  rw [hΦ, ColPoly.polyDeriv_subst hF' a j Φ (fun v => by simp [Φ])]
  refine Eq.symm ((polyDeriv_comp_linear hF' (hActL X idx h) _ _ 0).trans ?_)
  rw [map_zero]
  congr 1
  funext v k i
  obtain ⟨⟨τ, ρ, b⟩, rfl⟩ := eL.surjective v
  change Dict.hAct X idx h _ k i = _
  simp only [Dict.hAct, ha, hj, hdir, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [hl]) (by simp),
    Finset.sum_eq_single k (fun l _ hl => by simp [hl.symm]) (by simp)]
  by_cases hi : i = e.symm ⟨τ, ρ⟩
  · subst hi
    simp only [htype, Equiv.apply_symm_apply, Pi.single_eq_same]
    rfl
  · simp [hi]
end

