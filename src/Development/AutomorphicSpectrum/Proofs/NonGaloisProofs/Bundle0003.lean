module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LatticeOpenCompactNhdsBasis
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsDualLattices

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ActQIsLocallyConstant
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.FinCoc

section Generic

variable {G LL O V : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup V] [Module LL V]
  [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}

theorem actQ_one' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (m : ↥L.T ⧸ I) :
    actQ L I hI 1 m = m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L 1 t) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (by simp [actT])

theorem actQ_mul' (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g h : G)
    (m : ↥L.T ⧸ I) : actQ L I hI (g * h) m = actQ L I hI g (actQ L I hI h m) := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  change Submodule.Quotient.mk (actT L (g * h) t) = Submodule.Quotient.mk (actT L g (actT L h t))
  congr 1
  refine Subtype.ext ?_
  change ρ (g * h) (t : V) = ρ g (ρ h (t : V))
  simp

theorem pow_nsmul_quot (L : Lattice (O := O) ρ) {ϖ : O} {n : ℕ} (hn : (n : O) ∈ Ideal.span {ϖ}) (r : ℕ)
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) : n ^ r • m = 0 := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 hn
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  have hc : ((n ^ r : ℕ) : O) = ϖ ^ r * u ^ r := by
    rw [Nat.cast_pow, ← hu, mul_pow, mul_comm]
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

variable [TopologicalSpace V] [ContinuousAdd V]

theorem mk_isLocallyConstant (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    IsLocallyConstant (fun x : ↥L.T =>
      (Submodule.Quotient.mk x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : ↥L.T => (y : V) + -(x : V) :=
    continuous_subtype_val.add continuous_const
  have hev := hc.continuousAt.eventually_mem (x := x)
    (s := (fun x => ϖ ^ r • x) '' (L.T : Set V)) (by simpa using hW)
  filter_upwards [hev] with y hy
  obtain ⟨t, ht, h⟩ := hy
  rw [Submodule.Quotient.eq]
  have hxy : y - x = ϖ ^ r • (⟨t, ht⟩ : ↥L.T) :=
    Subtype.ext (by simpa [sub_eq_add_neg] using h.symm)
  rw [hxy]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem finite_quot (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ} (hC : IsCompact (L.T : Set V))
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V)) :
    Finite (↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) := by
  have hcs : CompactSpace ↥L.T := isCompact_iff_compactSpace.1 hC
  refine Set.finite_univ_iff.1 ?_
  rw [← (Submodule.Quotient.mk_surjective _).range_eq]
  exact (mk_isLocallyConstant L hW).range_finite

theorem actQ_isLocallyConstant [TopologicalSpace G] (L : Lattice (O := O) ρ) {ϖ : O} {r : ℕ}
    (hW : (fun x => ϖ ^ r • x) '' (L.T : Set V) ∈ nhds (0 : V))
    (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (m : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    IsLocallyConstant fun g => actQ L _ hI g m := by
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  have hc : Continuous fun g : G => actT L g t := (hcont (t : V)).subtype_mk _
  exact (mk_isLocallyConstant L hW).comp_continuous hc

end Generic

end GlobalTheory.CompanionTheory.FinCoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.ExistsFinsetSep
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.Kernels

theorem mem_of_forall_pow {O M : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [AddCommGroup M] [Module O M] (Λ E : Submodule O M) (hΛ : Λ.FG) (ϖ : O) (hϖ : ¬ IsUnit ϖ)
    (w : M) (h : ∀ n : ℕ, ∃ e ∈ E, ∃ t ∈ Λ, w = e + ϖ ^ n • t) : w ∈ E := by
  classical
  set N : Submodule O (M ⧸ E) := Λ.map E.mkQ with hNdef
  have hNfg : N.FG := hΛ.map _
  haveI : Module.Finite O N := Module.Finite.iff_fg.2 hNfg
  have hE : ∀ e ∈ E, E.mkQ e = 0 := fun e he => (Submodule.Quotient.mk_eq_zero E).2 he
  obtain ⟨e₀, he₀, t₀, ht₀, hw₀⟩ := h 0
  have hwN : E.mkQ w ∈ N := ⟨t₀, ht₀, by rw [hw₀, pow_zero, one_smul, map_add (f := _), hE e₀ he₀, zero_add]⟩
  have hI : Ideal.span {ϖ} ≠ ⊤ := fun h' => hϖ (Ideal.span_singleton_eq_top.1 h')
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := N) (Ideal.span {ϖ}) hI
  have hmem : (⟨E.mkQ w, hwN⟩ : N) ∈ (⨅ i : ℕ, Ideal.span {ϖ} ^ i • ⊤ : Submodule O N) := by
    refine Submodule.mem_iInf _ |>.2 fun i => ?_
    obtain ⟨e, he, t, ht, hw⟩ := h i
    have htN : E.mkQ t ∈ N := ⟨t, ht, rfl⟩
    have heq : (⟨E.mkQ w, hwN⟩ : N) = ϖ ^ i • (⟨E.mkQ t, htN⟩ : N) := by
      apply Subtype.ext
      rw [Submodule.coe_smul]
      show E.mkQ w = ϖ ^ i • E.mkQ t
      rw [hw, map_add (f := _), map_smul, hE e he, zero_add]
    rw [heq]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) i) Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  have h0 : E.mkQ w = 0 := congrArg Subtype.val hmem
  exact (Submodule.Quotient.mk_eq_zero E).1 h0

theorem exists_finset_sep {k U G X : Type} [Field k] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U] [AddCommGroup X] [Module k X] (φ : U →ₗ[k] G → X) :
    ∃ F : Finset G, ∀ u, (∀ g ∈ F, φ u g = 0) → φ u = 0 := by
  classical
  let Kf : Finset G → Submodule k U := fun F => ⨅ g ∈ F, LinearMap.ker ((LinearMap.proj g).comp φ)
  obtain ⟨_, ⟨F, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule k U)) (Set.range Kf)
    ⟨Kf ∅, Set.mem_range_self _⟩
  have hall : ∀ g, Kf F ≤ LinearMap.ker ((LinearMap.proj g).comp φ) := by
    intro g
    have hle : Kf (insert g F) ≤ Kf F := by
      refine le_iInf₂ fun g' hg' => iInf₂_le g' (Finset.mem_insert_of_mem hg')
    have heq : Kf (insert g F) = Kf F := by
      by_contra hne
      exact hmin _ (Set.mem_range_self _) (lt_of_le_of_ne hle hne)
    rw [← heq]
    exact iInf₂_le g (Finset.mem_insert_self g F)
  refine ⟨F, fun u hu => funext fun g => ?_⟩
  have huF : u ∈ Kf F := by
    simp only [Kf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    exact hu
  have := hall g huF
  simpa using this

end GlobalTheory.CompanionTheory.LocDual.Kernels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.H2LineOfTateH2AndCoboundaries
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Top

section Hom

variable {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL]
  [IsFractionRing O LL]

theorem exists_mul_of_linear (T : Submodule O LL) (hT : T = LinearMap.range (Algebra.linearMap O LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O) (ψ : LL →ₗ[O] LL ⧸ T) :
    ∃ u : LL, ∀ a, ψ a = Submodule.Quotient.mk (a * u) := by
  obtain ⟨p, hp⟩ : ∃ p : LL, p = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hp0 : p ≠ 0 := fun h => hϖ.ne_zero (IsFractionRing.injective O LL (by simpa [hp] using h))
  have hmem : ∀ x : LL, x ∈ T ↔ ∃ o : O, algebraMap O LL o = x := by
    intro x
    rw [hT]
    simp [LinearMap.mem_range]
  choose u hu using fun n : ℕ => Submodule.Quotient.mk_surjective T (ψ ((p⁻¹) ^ n))
  have step : ∀ n, ∃ o : O, algebraMap O LL o = p * u (n + 1) - u n := by
    intro n
    rw [← hmem, ← Submodule.Quotient.eq]
    have h1 : (Submodule.Quotient.mk (p * u (n + 1)) : LL ⧸ T) =
        ϖ • Submodule.Quotient.mk (u (n + 1)) := by
      rw [← Submodule.Quotient.mk_smul, Algebra.smul_def, hp]
    rw [h1, hu, hu, ← map_smul, Algebra.smul_def, ← hp]
    congr 1
    rw [pow_succ]
    field_simp
  choose o ho using step
  obtain ⟨y, hyd⟩ : ∃ y : ℕ → O, y = fun n => ∑ i ∈ Finset.range n, ϖ ^ i * o i := ⟨_, rfl⟩
  have hys : ∀ n, y (n + 1) = y n + ϖ ^ n * o n := by
    intro n
    simp [hyd, Finset.sum_range_succ]
  have hy0 : y 0 = 0 := by simp [hyd]
  have hy : ∀ n, p ^ n * u n = u 0 + algebraMap O LL (y n) := by
    intro n
    induction n with
    | zero => simp [hy0]
    | succ n ih =>
      have h2 : p ^ (n + 1) * u (n + 1) = p ^ n * u n + p ^ n * (p * u (n + 1) - u n) := by ring
      rw [h2, ih, ← ho n, hys, map_add (f := _), map_mul, map_pow, ← hp]
      ring
  have hI : ∀ m, ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
    intro m
    simp [Ideal.span_singleton_pow]
  have hcauchy : ∀ {m n}, m ≤ n → y m ≡ y n [SMOD ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [hys]
      have h3 : y m - (y n + ϖ ^ n * o n) = (y m - y n) - ϖ ^ n * o n := by ring
      rw [h3]
      exact dvd_sub ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨Y, hY⟩ := IsPrecomplete.prec hc.toIsPrecomplete hcauchy
  refine ⟨u 0 + algebraMap O LL Y, ?_⟩
  have hpow : ∀ n, ψ ((p⁻¹) ^ n) = Submodule.Quotient.mk ((p⁻¹) ^ n * (u 0 + algebraMap O LL Y)) := by
    intro n
    rw [← hu, Submodule.Quotient.eq, hmem]
    have h4 := hY n
    rw [SModEq.sub_mem, hI, Ideal.mem_span_singleton] at h4
    obtain ⟨t, ht⟩ := h4
    refine ⟨t, ?_⟩
    have h5 : algebraMap O LL (y n) - algebraMap O LL Y = p ^ n * algebraMap O LL t := by
      rw [← map_sub, ht, map_mul, map_pow, ← hp]
    have h6 : u n = (p⁻¹) ^ n * (u 0 + algebraMap O LL (y n)) := by
      rw [← hy, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
    rw [h6, ← mul_sub]
    have h7 : u 0 + algebraMap O LL (y n) - (u 0 + algebraMap O LL Y) = p ^ n * algebraMap O LL t := by
      rw [← h5]
      ring
    rw [h7, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp0, one_pow, one_mul]
  intro a
  obtain ⟨x, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := O) a
  have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
  obtain ⟨n, e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hw0 hϖ
  have hw1 : algebraMap O LL w ≠ 0 := fun h => hw0 (IsFractionRing.injective O LL (by simpa using h))
  have ha : algebraMap O LL x / algebraMap O LL w = (x * e) • (p⁻¹) ^ n := by
    rw [Algebra.smul_def, map_mul, div_eq_iff hw1]
    have h8 : p ^ n = algebraMap O LL w * algebraMap O LL (e : O) := by
      rw [hp, ← map_pow, ← he, map_mul]
    have h9 : p ^ n ≠ 0 := pow_ne_zero _ hp0
    rw [inv_pow]
    field_simp
    rw [h8]
    ring
  rw [ha, map_smul, hpow, ← Submodule.Quotient.mk_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]

end Hom

section Red

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]

def red (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : (G × G → LL) →ₗ[O] (G × G → LL ⧸ L1.T) :=
  LinearMap.compLeft L1.T.mkQ (G × G)

def Zc (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Submodule O (G × G → LL) :=
  (ReciprocityTheory.Def.Z2 (repD L1) ⊤).comap (red L1)

def cls (L1 : Lattice (O := O) (charRep (cycLL PD LL))) : Zc L1 →ₗ[O] ReciprocityTheory.Def.H2 (repD L1) ⊤ :=
  (Submodule.mkQ _) ∘ₗ ((red L1).restrict (q := ReciprocityTheory.Def.Z2 (repD L1) ⊤) (fun _ h => h))

theorem cls_eq_zero_iff (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (w : Zc L1) :
    cls L1 w = 0 ↔ CobO PD L1 (w : G × G → LL) := by
  simp only [cls, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem mem_Zc [TopologicalSpace LL] [IsTopologicalRing LL]
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hop : IsOpen (L1.T : Set LL)) {z : G × G → LL} (hz : Continuous z)
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0) : z ∈ Zc L1 := by
  refine ⟨⟨?_, fun _ => trivial⟩, ?_⟩
  · intro s
    have h1 : IsOpen ((Submodule.Quotient.mk : LL → LL ⧸ L1.T) ⁻¹' s) := by
      rw [isOpen_iff_forall_mem_open]
      intro y hy
      refine ⟨(fun t => t - y) ⁻¹' (L1.T : Set LL), ?_, hop.preimage (by fun_prop), ?_⟩
      · intro t ht
        have h2 : (Submodule.Quotient.mk t : LL ⧸ L1.T) = Submodule.Quotient.mk y :=
          (Submodule.Quotient.eq _).2 ht
        simpa [Set.mem_preimage, h2] using hy
      · simp [Set.mem_preimage]
    exact h1.preimage hz
  · ext x
    have h3 := congrFun hd x
    have h4 : (Submodule.Quotient.mk (ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z x) : LL ⧸ L1.T) = 0 := by
      rw [h3]
      simp
    exact h4

theorem topLine_at [TopologicalSpace LL] [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) (hop : IsOpen (L1.T : Set LL))
    {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (φ : ReciprocityTheory.Def.H2 (repD L1) ⊤ ≃ₗ[O] (LL ⧸ L1.T))
    (hC : ∀ z : G × G → LL, Continuous z → (CobL PD z ↔ ∀ a : LL, CobO PD L1 (a • z)))
    {z z' : G × G → LL} (hz : Continuous z) (hz' : Continuous z')
    (hd : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0)
    (hd' : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z' = 0) (hn : ¬ CobL PD z) :
    ∃ a : LL, CobL PD (z' - a • z) := by
  have hsm : ∀ {w : G × G → LL}, Continuous w → ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0 →
      ∀ a : LL, a • w ∈ Zc L1 := by
    intro w hw hdw a
    refine mem_Zc L1 hop (hw.const_smul a) ?_
    rw [map_smul, hdw, smul_zero]
  have key : ∀ {w : G × G → LL} (hw : Continuous w) (hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) w = 0),
      ∃ u : LL, ∀ a : LL, φ (cls L1 ⟨a • w, hsm hw hdw a⟩) = Submodule.Quotient.mk (a * u) := by
    intro w hw hdw
    let ι : LL →ₗ[O] Zc L1 :=
      { toFun := fun a => ⟨a • w, hsm hw hdw a⟩
        map_add' := fun a b => Subtype.ext (add_smul a b w)
        map_smul' := fun r a => Subtype.ext (by
          ext x
          simp [Algebra.smul_def, mul_assoc]) }
    exact exists_mul_of_linear L1.T hT hϖ hc ((φ.toLinearMap ∘ₗ cls L1) ∘ₗ ι)
  obtain ⟨u, hu⟩ := key hz hd
  obtain ⟨u', hu'⟩ := key hz' hd'
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hn
    rw [hC z hz]
    intro a
    have h1 := hu a
    rw [mul_zero, Submodule.Quotient.mk_zero, map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h1
    exact h1
  refine ⟨u' / u, ?_⟩
  have hwc : Continuous (z' - (u' / u) • z) := hz'.sub (hz.const_smul _)
  have hdw : ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) (z' - (u' / u) • z) = 0 := by
    rw [map_sub, map_smul, hd, hd', smul_zero, sub_zero]
  rw [hC _ hwc]
  intro b
  have h2 : (⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩ : Zc L1) =
      ⟨b • z', hsm hz' hd' b⟩ - ⟨(b * (u' / u)) • z, hsm hz hd _⟩ := by
    apply Subtype.ext
    simp [smul_sub, mul_smul]
  have h3 : φ (cls L1 ⟨b • (z' - (u' / u) • z), hsm hwc hdw b⟩) = 0 := by
    rw [h2, map_sub, map_sub, hu, hu', ← Submodule.Quotient.mk_sub]
    have h4 : b * u' - b * (u' / u) * u = 0 := by
      field_simp
      ring
    rw [h4, Submodule.Quotient.mk_zero]
  rw [map_eq_zero_iff φ φ.injective, cls_eq_zero_iff] at h3
  exact h3

end Red

end GlobalTheory.CompanionTheory.LocDual.Top
end
end

