module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSubrepCompactInductionSpan
section
open GlobalTheory.PRep Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.PRep.CIndGlue

open GlobalTheory.CompanionTheory.PRep.CIndKer

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem sum_apply (H : Subgroup G) (ρ : Representation ℂ H W) {ι : Type} (s : Finset ι)
    (F : ι → cIndSpace H ρ) (g : G) :
    (∑ i ∈ s, F i).1.1.1 g = ∑ i ∈ s, (F i).1.1.1 g := by
  let ev : cIndSpace H ρ →ₗ[ℂ] W :=
    (LinearMap.proj g) ∘ₗ (indSpace H ρ).subtype ∘ₗ (smoothPart (ind H ρ)).subtype ∘ₗ
      (cIndSpace H ρ).subtype
  exact map_sum ev _ _

theorem exists_small_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧ ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G) :
    ∃ K' : Subgroup G, IsOpen (K' : Set G) ∧ K' ≤ K₁ ∧ ∃ B ∈ I,
      ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g := by
  classical
  have hO : (fun x : G => c⁻¹ * x * c) ⁻¹' (K₁ : Set G) ∈ 𝓝 (1 : G) :=
    (hK₁o.preimage (by fun_prop)).mem_nhds (by simp [one_mem])
  obtain ⟨K, hKo, hKO, B₀, hB₀, hB1, hB0⟩ := hloc (y.1.1.1 c) _ hO
  let K' : Subgroup G := K.comap (MulAut.conj c).toMonoidHom
  have hmem : ∀ x, x ∈ K' ↔ c * x * c⁻¹ ∈ K := fun x => Iff.rfl
  have hK'o : IsOpen (K' : Set G) := by
    have : Continuous fun x : G => c * x * c⁻¹ := by fun_prop
    exact hKo.preimage this
  have hle : K' ≤ K₁ := by
    intro x hx
    have h := hKO ((hmem x).1 hx)
    have e : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    simpa [e] using h
  refine ⟨K', hK'o, hle, cInd H ρ c⁻¹ B₀, hI _ _ hB₀, fun g => ?_⟩
  have e1 : (cInd H ρ c⁻¹ B₀).1.1.1 g = B₀.1.1.1 (g * c⁻¹) := rfl
  rw [e1]
  by_cases hg : g ∈ dc H K' c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    have e2 : (b : G) * c * k * c⁻¹ = (b : G) * (c * k * c⁻¹) := by group
    rw [e2, hB1 b _ ((hmem k).1 hk), mul_assoc, y.1.1.2 b, hy c k (hle hk)]
  · rw [Set.indicator_of_notMem hg]
    apply hB0
    rintro ⟨a, x, hx, e⟩
    apply hg
    refine ⟨a, c⁻¹ * x * c, (hmem _).2 ?_, ?_⟩
    · have e3 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
      rw [e3]
      exact hx
    · have e4 : g = (g * c⁻¹) * c := by group
      rw [e4, e]
      group

theorem average_cut (H : Subgroup G) (ρ : Representation ℂ H W)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (K₁ : Subgroup G) (hK₁c : IsCompact (K₁ : Set G)) (y : cIndSpace H ρ)
    (hy : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g) (c : G)
    (K' : Subgroup G) (hK'o : IsOpen (K' : Set G)) (hle : K' ≤ K₁)
    (B : cIndSpace H ρ) (hBI : B ∈ I) (hB : ∀ g, B.1.1.1 g = (dc H K' c).indicator y.1.1.1 g) :
    ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
  classical
  haveI : CompactSpace K₁ := isCompact_iff_compactSpace.1 hK₁c
  let L : Subgroup K₁ := K'.subgroupOf K₁
  have hLo : IsOpen (L : Set K₁) := hK'o.preimage continuous_subtype_val
  haveI : Finite (K₁ ⧸ L) := Subgroup.quotient_finite_of_isOpen _ hLo
  haveI := Fintype.ofFinite (K₁ ⧸ L)
  let φ : G → ℕ := fun g => ∑ q : K₁ ⧸ L, if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0
  let Sg : cIndSpace H ρ := ∑ q : K₁ ⧸ L, cInd H ρ ((q.out : K₁) : G) B
  have hSg : Sg ∈ I := Submodule.sum_mem _ fun q _ => hI _ _ hBI
  have hval : ∀ g, Sg.1.1.1 g = (φ g : ℂ) • y.1.1.1 g := by
    intro g
    have e0 : Sg.1.1.1 g = ∑ q : K₁ ⧸ L, (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g :=
      sum_apply H ρ _ _ g
    rw [e0]
    simp only [φ]
    push_cast
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : (cInd H ρ ((q.out : K₁) : G) B).1.1.1 g = B.1.1.1 (g * ((q.out : K₁) : G)) := rfl
    rw [e1, hB]
    by_cases h : g * ((q.out : K₁) : G) ∈ dc H K' c
    · rw [Set.indicator_of_mem h, hy g _ q.out.2, if_pos h, one_smul]
    · rw [Set.indicator_of_notMem h, if_neg h, zero_smul]
  have hleft : ∀ (b : H) g, φ ((b : G) * g) = φ g := by
    intro b g
    simp only [φ, mul_assoc, dc_left H K' c (b : G) b.2]
  have hright : ∀ κ ∈ K₁, ∀ g, φ (g * κ) = φ g := by
    intro κ hκ g
    let κ' : K₁ := ⟨κ, hκ⟩
    have key : ∀ q : K₁ ⧸ L, g * κ * ((q.out : K₁) : G) ∈ dc H K' c ↔
        g * (((κ' • q).out : K₁) : G) ∈ dc H K' c := by
      intro q
      have e : ((κ' * q.out : K₁) : K₁ ⧸ L) = κ' • q := by
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      have e2 : (κ' • q).out⁻¹ * (κ' * q.out) ∈ L := by
        apply QuotientGroup.eq.1
        rw [e, QuotientGroup.out_eq']
      have e3 : ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) ∈ K' := e2
      have e4 : g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out⁻¹ * (κ' * q.out) : K₁)) : G) := by
        push_cast
        show g * κ * ((q.out : K₁) : G) = g * (((κ' • q).out : K₁) : G) *
          ((((κ' • q).out : K₁) : G)⁻¹ * (κ * ((q.out : K₁) : G)))
        group
      rw [e4]
      exact dc_right H K' c _ e3 _
    simp only [φ, mul_assoc] at key ⊢
    simp only [← mul_assoc] at key ⊢
    simp only [key]
    exact Equiv.sum_comp (MulAction.toPerm κ')
      (fun q : K₁ ⧸ L => if g * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0)
  have hφc : φ c ≠ 0 := by
    let q₀ : K₁ ⧸ L := ((1 : K₁) : K₁ ⧸ L)
    have h1 : (q₀.out : K₁)⁻¹ * 1 ∈ L := by
      apply QuotientGroup.eq.1
      rw [QuotientGroup.out_eq']
    have h2 : (q₀.out : K₁) ∈ L := by
      have := inv_mem h1
      simpa using this
    have h3 : ((q₀.out : K₁) : G) ∈ K' := h2
    have h4 : c * ((q₀.out : K₁) : G) ∈ dc H K' c := ⟨1, _, h3, by simp⟩
    have h5 : (if c * ((q₀.out : K₁) : G) ∈ dc H K' c then 1 else 0) ≤ φ c :=
      Finset.single_le_sum (f := fun q : K₁ ⧸ L =>
        if c * ((q.out : K₁) : G) ∈ dc H K' c then 1 else 0) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ q₀)
    rw [if_pos h4] at h5
    omega
  have hoff : ∀ g, g ∉ dc H K₁ c → φ g = 0 := by
    intro g hg
    refine Finset.sum_eq_zero fun q _ => if_neg fun h => hg ?_
    obtain ⟨b, k, hk, e⟩ := h
    exact (dc_right H K₁ c _ q.out.2 g).1 ⟨b, k, hle hk, e⟩
  have hc0 : (φ c : ℂ) ≠ 0 := by exact_mod_cast hφc
  refine ⟨(φ c : ℂ)⁻¹ • Sg, Submodule.smul_mem _ _ hSg, fun g => ?_⟩
  have e : ((φ c : ℂ)⁻¹ • Sg).1.1.1 g = (φ c : ℂ)⁻¹ • Sg.1.1.1 g := rfl
  rw [e, hval]
  by_cases hg : g ∈ dc H K₁ c
  · rw [Set.indicator_of_mem hg]
    obtain ⟨b, k, hk, rfl⟩ := hg
    rw [mul_assoc, hleft, hright k hk, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      y.1.1.2 b, hy c k hk]
  · rw [Set.indicator_of_notMem hg, hoff g hg]
    simp

theorem eq_top_of_bumps : ∀ {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [Module ℂ W]
    (H : Subgroup G) (ρ : Representation ℂ H W)
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (I : Submodule ℂ (cIndSpace H ρ)) (hI : ∀ (g : G) (B : cIndSpace H ρ), B ∈ I → cInd H ρ g B ∈ I)
    (hloc : ∀ (v : W) (O : Set G), O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      (K : Set G) ⊆ O ∧
      ∃ B ∈ I, (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * x) = ρ a v) ∧
        ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * x) → B.1.1.1 g = 0)
    (y : cIndSpace H ρ), y ∈ I := by
  intro G W _ _ _ _ _ H ρ hbasis I hI hloc y
  classical
  have hyo : IsOpen {g : G | ind H ρ g y.1.1 = y.1.1} := y.1.2
  obtain ⟨K₁, hK₁o, hK₁c, hK₁U⟩ := hbasis _ (hyo.mem_nhds (by simp))
  have hinv : ∀ g, ∀ x ∈ K₁, y.1.1.1 (g * x) = y.1.1.1 g := by
    intro g x hx
    have h : ind H ρ x y.1.1 = y.1.1 := hK₁U hx
    exact congrArg (fun v : indSpace H ρ => v.1 g) h
  have hdc : ∀ c : G, ∃ z ∈ I, ∀ g, z.1.1.1 g = (dc H K₁ c).indicator y.1.1.1 g := by
    intro c
    obtain ⟨K', hK'o, hle, B, hBI, hB⟩ := exists_small_cut H ρ I hI hloc K₁ hK₁o y hinv c
    exact average_cut H ρ I hI K₁ hK₁c y hinv c K' hK'o hle B hBI hB
  have key : ∀ t : Finset G, ∃ S : Set G, (∀ h ∈ H, ∀ g, h * g ∈ S ↔ g ∈ S) ∧
      (∀ k ∈ K₁, ∀ g, g * k ∈ S ↔ g ∈ S) ∧ (∀ c ∈ t, c ∈ S) ∧
      ∃ z ∈ I, ∀ g, z.1.1.1 g = S.indicator y.1.1.1 g := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨∅, by simp, by simp, by simp, 0, Submodule.zero_mem _, fun g => by simp⟩
    | insert c t _ ih =>
      obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := ih
      by_cases hcS : c ∈ S
      · refine ⟨S, hl, hr, fun c' hc' => ?_, z, hz, ez⟩
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hcS
        · exact hcov c' hc'
      · obtain ⟨z', hz', ez'⟩ := hdc c
        have hdisj : ∀ g, g ∈ dc H K₁ c → g ∉ S := by
          rintro g ⟨b, k, hk, rfl⟩ hg
          rw [mul_assoc, hl _ b.2, hr k hk] at hg
          exact hcS hg
        refine ⟨S ∪ dc H K₁ c, fun h hh g => ?_, fun k hk g => ?_, fun c' hc' => ?_, z + z',
          Submodule.add_mem _ hz hz', fun g => ?_⟩
        · simp only [Set.mem_union, hl h hh g, dc_left H K₁ c h hh g]
        · simp only [Set.mem_union, hr k hk g, dc_right H K₁ c k hk g]
        · rcases Finset.mem_insert.1 hc' with rfl | hc'
          · exact Or.inr ⟨1, 1, one_mem _, by simp⟩
          · exact Or.inl (hcov c' hc')
        · have e : (z + z').1.1.1 g = z.1.1.1 g + z'.1.1.1 g := rfl
          rw [e, ez, ez']
          by_cases h2 : g ∈ dc H K₁ c
          · have h1 := hdisj g h2
            simp [Set.indicator, h1, h2]
          · by_cases h1 : g ∈ S <;> simp [Set.indicator, h1, h2]
  obtain ⟨C, hC, hsupp⟩ := y.2
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover (fun c => (fun x => c * x) '' (K₁ : Set G))
    (fun c _ => by
      have : (fun x => c⁻¹ * x) ⁻¹' (K₁ : Set G) ∈ 𝓝 c :=
        (hK₁o.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp [one_mem])
      filter_upwards [this] with x hx
      exact ⟨c⁻¹ * x, hx, by group⟩)
  obtain ⟨S, hl, hr, hcov, z, hz, ez⟩ := key t
  have hyz : y = z := by
    refine Subtype.ext (Subtype.ext (Subtype.ext (funext fun g => ?_)))
    show y.1.1.1 g = z.1.1.1 g
    rw [ez]
    by_cases h0 : y.1.1.1 g = 0
    · rw [h0]
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg, h0]
      · rw [Set.indicator_of_notMem hg]
    · obtain ⟨a, ha, c', hc', e⟩ := hsupp g h0
      obtain ⟨c, hc, hcc⟩ := Set.mem_iUnion₂.1 (ht hc')
      obtain ⟨x, hx, rfl⟩ := hcc
      have hg : g ∈ S := by
        rw [e]
        exact (hl a ha _).2 ((hr x hx c).2 (hcov c hc))
      rw [Set.indicator_of_mem hg]
  rw [hyz]
  exact hz

end GlobalTheory.CompanionTheory.PRep.CIndGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProduct
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

theorem exists_larger_of_valuationSubring {k : Type} [Field k] (O : ValuationSubring k) (a b : k) :
    ∃ c : k, (c = a ∨ c = b) ∧ (∃ u ∈ O, a = c * u) ∧ (∃ u ∈ O, b = c * u) := by
  by_cases ha : a = 0
  · exact ⟨b, Or.inr rfl, ⟨0, O.zero_mem, by simp [ha]⟩, ⟨1, O.one_mem, by simp⟩⟩
  by_cases hb : b = 0
  · exact ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨0, O.zero_mem, by simp [hb]⟩⟩
  rcases O.mem_or_inv_mem (a / b) with h | h
  · exact ⟨b, Or.inr rfl, ⟨a / b, h, by field_simp⟩, ⟨1, O.one_mem, by simp⟩⟩
  · refine ⟨a, Or.inl rfl, ⟨1, O.one_mem, by simp⟩, ⟨(a / b)⁻¹, h, ?_⟩⟩
    field_simp

theorem fg_eq_prod_principal {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k)
    (φ : R ≃+* k × k) (𝔬 : Subring R)
    (h𝔬 : ∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) (I : Submodule 𝔬 R) (hI : I.FG) :
    ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  induction I, hI using Submodule.fg_induction with
  | singleton r₀ =>
    refine ⟨(φ r₀).1, (φ r₀).2, fun r => ?_⟩
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨t, rfl⟩
      have ht := (h𝔬 t).1 t.2
      have hs : φ (t • r₀) = φ (t : R) * φ r₀ := by
        rw [Subring.smul_def, smul_eq_mul, map_mul]
      refine ⟨⟨(φ (t : R)).1, ht.1, ?_⟩, ⟨(φ (t : R)).2, ht.2, ?_⟩⟩
      · rw [hs, Prod.fst_mul, mul_comm]
      · rw [hs, Prod.snd_mul, mul_comm]
    · rintro ⟨⟨x, hx, h1⟩, ⟨y, hy, h2⟩⟩
      have hmem : φ.symm (x, y) ∈ 𝔬 := by
        rw [h𝔬]
        simpa using ⟨hx, hy⟩
      refine ⟨⟨φ.symm (x, y), hmem⟩, ?_⟩
      apply φ.injective
      rw [Subring.smul_def, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
      ext
      · simp [h1, mul_comm]
      · simp [h2, mul_comm]
  | sup I₁ I₂ _ _ ih₁ ih₂ =>
    obtain ⟨α₁, β₁, h₁⟩ := ih₁
    obtain ⟨α₂, β₂, h₂⟩ := ih₂
    obtain ⟨α, hα, ⟨u₁, hu₁, e₁⟩, ⟨u₂, hu₂, e₂⟩⟩ := exists_larger_of_valuationSubring O α₁ α₂
    obtain ⟨β, hβ, ⟨v₁, hv₁, f₁⟩, ⟨v₂, hv₂, f₂⟩⟩ := exists_larger_of_valuationSubring O β₁ β₂
    refine ⟨α, β, fun r => ?_⟩
    constructor
    · intro hr
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hr
      obtain ⟨⟨x₁, hx₁, p₁⟩, ⟨y₁, hy₁, q₁⟩⟩ := (h₁ a).1 ha
      obtain ⟨⟨x₂, hx₂, p₂⟩, ⟨y₂, hy₂, q₂⟩⟩ := (h₂ b).1 hb
      refine ⟨⟨u₁ * x₁ + u₂ * x₂, O.add_mem _ _ (O.mul_mem _ _ hu₁ hx₁) (O.mul_mem _ _ hu₂ hx₂), ?_⟩,
        ⟨v₁ * y₁ + v₂ * y₂, O.add_mem _ _ (O.mul_mem _ _ hv₁ hy₁) (O.mul_mem _ _ hv₂ hy₂), ?_⟩⟩
      · rw [map_add (f := _), Prod.fst_add, p₁, p₂, e₁, e₂]
        ring
      · rw [map_add (f := _), Prod.snd_add, q₁, q₂, f₁, f₂]
        ring
    · rintro ⟨⟨x, hx, p⟩, ⟨y, hy, q⟩⟩
      have hsplit : r = φ.symm ((φ r).1, 0) + φ.symm (0, (φ r).2) := by
        apply φ.injective
        rw [map_add (f := _), RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
        ext <;> simp
      rw [hsplit]
      refine Submodule.add_mem _ ?_ ?_
      · rcases hα with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨x, hx, p⟩, ⟨0, O.zero_mem, by simp⟩⟩
      · rcases hβ with rfl | rfl
        · refine Submodule.mem_sup_left ((h₁ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩
        · refine Submodule.mem_sup_right ((h₂ _).2 ?_)
          simp only [RingEquiv.apply_symm_apply]
          exact ⟨⟨0, O.zero_mem, by simp⟩, ⟨y, hy, q⟩⟩

end GlobalTheory.CompanionTheory.KFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernel
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.TwistedAverage

theorem sum_reps_eq_sum_out {H V : Type} [Group H] [AddCommGroup V] (K : Subgroup H)
    [Fintype (H ⧸ K)] (T : Finset H) (hT : ∀ x : H, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) (f : H → V)
    (hf : ∀ x, ∀ k ∈ K, f (x * k) = f x) :
    ∑ t ∈ T, f t = ∑ q : H ⧸ K, f q.out := by
  refine Finset.sum_bij (fun t _ => (QuotientGroup.mk t : H ⧸ K)) (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro a ha b hb hab
    exact (hT b).unique ⟨ha, QuotientGroup.eq.1 hab⟩ ⟨hb, by simp⟩
  · intro q _
    obtain ⟨t, ⟨ht, hx⟩, -⟩ := hT q.out
    refine ⟨t, ht, ?_⟩
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 hx
  · intro t _
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K t
    rw [hh, hf _ _ h.2]

theorem sum_reps_eq_zero_of_mem_twKer :
    ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G Z), IsSmooth ρ → ∀ (L : Subgroup G), IsCompact (L : Set G) → ∀ v : Z, v ∈ twKer ρ L 1 → ∀ (K : Subgroup L) (T : Finset L), IsOpen (K : Set L) → (∀ x ∈ K, ρ (x : G) v = v) → (∀ x : L, ∃! t, t ∈ T ∧ t⁻¹ * x ∈ K) → ∑ t ∈ T, ρ (t : G) v = 0 := by
  intro G Z _ _ _ _ _ ρ hρ L hL v hv K T hKo hKv hT
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hθ : IsOpen (((1 : L →* ℂˣ).ker : Subgroup L) : Set L) := by
    rw [MonoidHom.ker_one]
    exact isOpen_univ
  obtain ⟨M, hM, hsum⟩ := exists_sum_eq_zero hρ hL (1 : L →* ℂˣ) hθ hv
  haveI : Finite (L ⧸ K) := Subgroup.quotient_finite_of_isOpen _ hKo
  haveI hKf : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : Fintype (L ⧸ K) := Fintype.ofFinite _
  set C : Subgroup L := (M ⊓ K).normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal _
  haveI : C.FiniteIndex := inferInstance
  haveI : Fintype (L ⧸ C) := Fintype.ofFinite _
  have hCM : C ≤ M ⊓ K := Subgroup.normalCore_le _
  haveI : Finite (K ⧸ C.subgroupOf K) := inferInstance
  haveI : Fintype (K ⧸ C.subgroupOf K) := Fintype.ofFinite _
  have hf : ∀ x : L, ∀ k ∈ K, twOrbit ρ L 1 v (x * k) = twOrbit ρ L 1 v x := by
    intro x k hk
    simp only [twOrbit, MonoidHom.one_apply, mul_one, inv_one, Units.val_one, one_smul,
      Subgroup.coe_mul, map_mul, Module.End.mul_apply, hKv k hk]
  have h0 := hsum C (hCM.trans inf_le_left)
  rw [sum_out_refine (hCM.trans inf_le_right) (twOrbit ρ L 1 v) hf] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  have h1 : ∑ q : L ⧸ K, twOrbit ρ L 1 v q.out = 0 := by
    rcases h0 with h0 | h0
    · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    · exact h0
  have h2 := sum_reps_eq_sum_out K T hT (twOrbit ρ L 1 v) hf
  rw [h1] at h2
  simpa [twOrbit] using h2

end GlobalTheory.CompanionTheory.TwistedAverage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosed
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.SuppOff

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

theorem isClosed_support (H : Subgroup G) (σ : Representation ℂ H W) (f : smoothPart (ind H σ)) :
    IsClosed {c : G | f.1.1 c ≠ 0} := by
  have hopen : IsOpen {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := f.2
  have htrans : ∀ g x : G, GlobalTheory.PRep.ind H σ g f.1 = f.1 → f.1.1 (x * g) = f.1.1 x := by
    intro g x hg
    exact congrArg (fun φ : GlobalTheory.PRep.indSpace H σ => (φ : G → W) x) hg
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro c hc
  have hc0 : f.1.1 c = 0 := by simpa using hc
  have h1 : c⁻¹ * c ∈ {g : G | GlobalTheory.PRep.ind H σ g f.1 = f.1} := by
    show GlobalTheory.PRep.ind H σ (c⁻¹ * c) f.1 = f.1
    rw [inv_mul_cancel, map_one]
    rfl
  refine Filter.mem_of_superset
    ((continuous_const_mul c⁻¹).continuousAt.preimage_mem_nhds (hopen.mem_nhds h1)) ?_
  intro x hx
  have hx' : GlobalTheory.PRep.ind H σ (c⁻¹ * x) f.1 = f.1 := hx
  have hfx : f.1.1 x = 0 := by
    calc f.1.1 x = f.1.1 (c * (c⁻¹ * x)) := by rw [mul_inv_cancel_left]
      _ = f.1.1 c := htrans _ _ hx'
      _ = 0 := hc0
  simpa using hfx

theorem exists_compact_off (H : Subgroup G) (σ : Representation ℂ H W) (f : cIndSpace H σ) (T : Set G)
    (hf : ∀ x ∈ T, (f : smoothPart (ind H σ)).1.1 x = 0) :
    ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
      ∀ g, (f : smoothPart (ind H σ)).1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
  have key : ∀ F : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ),
      (∃ C : Set G, IsCompact C ∧ ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c) →
      (∀ x ∈ T, F.1.1 x = 0) →
      ∃ C : Set G, IsCompact C ∧ (∀ c ∈ C, c ∉ T) ∧
        ∀ g, F.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c := by
    rintro F ⟨C, hC, hsupp⟩ hF
    have hequiv : ∀ (h : H) (g : G), F.1.1 (h * g) = σ h (F.1.1 g) := F.1.2
    refine ⟨C ∩ {c | F.1.1 c ≠ 0}, hC.inter_right (GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.isClosed_support H σ F), ?_, ?_⟩
    · rintro c ⟨-, hc⟩ hcT
      exact hc (hF c hcT)
    · intro g hg
      obtain ⟨h, hH, c, hcC, rfl⟩ := hsupp g hg
      refine ⟨h, hH, c, ⟨hcC, ?_⟩, rfl⟩
      intro hc0
      apply hg
      have e : F.1.1 (h * c) = σ ⟨h, hH⟩ (F.1.1 c) := hequiv ⟨h, hH⟩ c
      rw [e]
      have hc0' : F.1.1 c = 0 := by simpa using hc0
      rw [hc0', map_zero]
  exact key _ f.2 hf

end Abstract

theorem exists_compact_off_Cl (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k ((i + 1) + t + 1)), IsCompact C ∧ (∀ c ∈ C, c ∉ Cl k i t) ∧
      ∀ g, evX f g ≠ 0 → ∃ h ∈ HPG k (i + 1) (t + 1), ∃ c ∈ C, g = h * c :=
  GlobalTheory.CompanionTheory.BZPhiPG.SuppOff.exists_compact_off (GlobalTheory.BZMir.Leib.HPG k (i + 1) (t + 1))
    (GlobalTheory.CompanionTheory.BZPhiPG.sigX τ σ) f _ hf

end GlobalTheory.CompanionTheory.BZPhiPG.SuppOff
end

