module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.UnipotentAdelicQuotients.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticFormIdeleValuesMemNhdsOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0012
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationality
public import Formalism.LocalRingCardinality.DataLatDefs
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNormGroupIffEverywhereNorm
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct Topology

namespace GlobalTheory.IdeleNormChar

open GlobalTheory.QuadSymbol

variable {K : Type} [Field K] [NumberField K]

def finEval (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEval (w : InfinitePlace K) : AdeleRing (𝓞 K) K →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

def finComp : (AdeleRing (𝓞 K) K)ˣ →* FinFam K :=
  MonoidHom.pi fun v => Units.map (finEval v)

def infComp : (AdeleRing (𝓞 K) K)ˣ →* InfFam K :=
  MonoidHom.pi fun w => Units.map (infEval w)

theorem finComp_toUnits (t : Kˣ) : finComp (toUnits K (AdeleRing (𝓞 K) K) t) = finDiag K t :=
  funext fun _ => Units.ext rfl

theorem infComp_toUnits (t : Kˣ) : infComp (toUnits K (AdeleRing (𝓞 K) K) t) = infDiag K t :=
  funext fun _ => Units.ext rfl

theorem eventually_valued_eq_one (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  filter_upwards [(a : AdeleRing (𝓞 K) K).2.2, ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2.2]
    with v h3 h4
  have hmul : (a : AdeleRing (𝓞 K) K).2 v *
      ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) a.mul_inv
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  change Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1
  refine le_antisymm h3 ?_
  rw [← hm]
  exact mul_le_of_le_one_right' h4

theorem eventually_integral_form (δ : K) (hδ : δ ≠ 0) (a : (AdeleRing (𝓞 K) K)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
  filter_upwards [eventually_valued_eq_one a,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 2 two_ne_zero)).compl_mem_cofinite,
    (GlobalTheory.QNorm.finite_valuation_ne_one K (Units.mk0 δ hδ)).compl_mem_cofinite] with v ha h2 hd
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, Units.val_mk0] at h2 hd
  have key : ∀ x : K, Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  exact GlobalTheory.QNorm.exists_integral_sq_sub_mul_sq_of_unit K v (algebraMap K _ δ) _
    (by rw [← map_ofNat (algebraMap K (v.adicCompletion K)) 2]; exact (key _).trans h2)
    (by rw [key, hd]) ha

variable (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L]


omit [NumberField L] in
theorem almostNorm_finComp (a : (AdeleRing (𝓞 K) K)ˣ) : AlmostNorm K L (finComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  refine Filter.eventually_cofinite.1 ((eventually_integral_form δ hδ0 a).mono ?_)
  rintro v ⟨x, -, y, -, h⟩
  exact (mem_normGroup_iff_form b h0 h1).2 ⟨x, y, h⟩


omit [NumberField L] in
theorem mem_normGroup_iff_everywhereNorm (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ normGroup K L (AdeleRing (𝓞 K) K) ↔ EverywhereNorm K L (finComp a) (infComp a) := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨x, y, h⟩
    exact ⟨fun v => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.2 v, y.2 v, congrArg (fun z : AdeleRing (𝓞 K) K => z.2 v) h⟩,
      fun w => (mem_normGroup_iff_form b h0 h1).2
        ⟨x.1 w, y.1 w, congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) h⟩⟩
  · rintro ⟨hf, hi⟩
    have hc := eventually_integral_form δ hδ0 a
    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K,
        ((∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2) →
          x ∈ v.adicCompletionIntegers K ∧ y ∈ v.adicCompletionIntegers K) ∧
        ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 := by
      intro v
      by_cases hv : ∃ x ∈ v.adicCompletionIntegers K, ∃ y ∈ v.adicCompletionIntegers K,
          ((finComp a v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
            x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2
      · obtain ⟨x, hx, y, hy, h⟩ := hv
        exact ⟨x, y, fun _ => ⟨hx, hy⟩, h⟩
      · obtain ⟨x, y, h⟩ := (mem_normGroup_iff_form b h0 h1).1 (hf v)
        exact ⟨x, y, fun h' => absurd h' hv, h⟩
    choose x y hxy h using hloc
    choose r s hr using fun w => (mem_normGroup_iff_form b h0 h1).1 (hi w)
    let X : FiniteAdeleRing (𝓞 K) K := ⟨x, hc.mono fun v hv => (hxy v hv).1⟩
    let Y : FiniteAdeleRing (𝓞 K) K := ⟨y, hc.mono fun v hv => (hxy v hv).2⟩
    refine ⟨((r : InfiniteAdeleRing K), X), ((s : InfiniteAdeleRing K), Y), Prod.ext ?_ ?_⟩
    · funext w
      exact hr w
    · exact FiniteAdeleRing.ext K fun v => h v

def normSign : (AdeleRing (𝓞 K) K)ˣ →* ℤˣ :=
  MonoidHom.mk' (fun a => etaProd K L (finComp a) (infComp a)) fun a b => by
    obtain ⟨h1, h2⟩ := localCharacters K L
    unfold etaProd
    simp only [map_mul, Pi.mul_apply, h1, h2]
    rw [finprod_mul_distrib (almostNorm_finComp L a).finite_mulSupport
      (almostNorm_finComp L b).finite_mulSupport, Finset.prod_mul_distrib, mul_mul_mul_comm]

theorem normSign_eq_one_iff (a : (AdeleRing (𝓞 K) K)ˣ) :
    normSign L a = 1 ↔ ∃ t : Kˣ, a / toUnits K (AdeleRing (𝓞 K) K) t ∈ normGroup K L (AdeleRing (𝓞 K) K) := by
  refine ((exactSequence K L).2.2.1 _ _ (almostNorm_finComp L a)).symm.trans (exists_congr fun t => ?_)
  rw [mem_normGroup_iff_everywhereNorm, map_div, map_div, finComp_toUnits, infComp_toUnits]

theorem normSign_of_mem {a : (AdeleRing (𝓞 K) K)ˣ} (h : a ∈ normGroup K L (AdeleRing (𝓞 K) K)) :
    normSign L a = 1 :=
  (normSign_eq_one_iff L a).2 ⟨1, by rwa [map_one, div_one]⟩

theorem normSign_toUnits (t : Kˣ) : normSign L (toUnits K (AdeleRing (𝓞 K) K) t) = 1 :=
  (normSign_eq_one_iff L _).2 ⟨t, by rw [div_self']; exact one_mem _⟩

theorem exists_normSign_ne_one : ∃ a : (AdeleRing (𝓞 K) K)ˣ, normSign L a ≠ 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  obtain ⟨a, ha⟩ := GlobalTheory.QNorm.exists_idele_not_mul_norm K δ hδ
  refine ⟨a, fun h => ?_⟩
  obtain ⟨t, ht⟩ := (normSign_eq_one_iff L a).1 h
  obtain ⟨x, y, e⟩ := (mem_normGroup_iff_form b h0 h1).1 ht
  refine ha t x y ?_
  rw [← e]
  exact (congrArg Units.val (mul_div_cancel (toUnits K (AdeleRing (𝓞 K) K) t) a)).symm

theorem eventually_normSign : ∀ᶠ a in 𝓝 (1 : (AdeleRing (𝓞 K) K)ˣ), normSign L a = 1 := by
  obtain ⟨δ, b, hδ, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  filter_upwards [GlobalTheory.QNorm.norm_form_mem_nhds_one K δ hδ0] with a ha
  exact normSign_of_mem L ((mem_normGroup_iff_form b h0 h1).2 ha)

def signToCircle : ℤˣ →* Circle where
  toFun u := if u = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' u u' := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or u' with rfl | rfl <;> simp

theorem circle_neg_one_ne_one : (-1 : Circle) ≠ 1 := fun h => by
  have := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at this

theorem eq_signToCircle_comp {G : Type} [Group G] (ε : G →* ℤˣ) (η : G →* Circle)
    (h : ∀ a, ε a = 1 → η a = 1) (hη : η ≠ 1) : η = signToCircle.comp ε := by
  obtain ⟨b, hb⟩ : ∃ b, η b ≠ 1 := by
    by_contra hh
    push Not at hh
    exact hη (MonoidHom.ext hh)
  have hεb : ε b = -1 := (Int.units_eq_one_or _).resolve_left fun e => hb (h b e)
  refine MonoidHom.ext fun a => ?_
  rcases Int.units_eq_one_or (ε a) with e | e
  · rw [MonoidHom.comp_apply, e, map_one, h a e]
  · have h1 : η a * η b = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e, hεb]; simp)
    have h2 : η a * η a = 1 := by rw [← map_mul]; exact h _ (by rw [map_mul, e]; simp)
    have h3 : (η a : ℂ) * η a = 1 := by exact_mod_cast congrArg (fun w : Circle => (w : ℂ)) h2
    rw [MonoidHom.comp_apply, e]
    change η a = if (-1 : ℤˣ) = 1 then 1 else -1
    rw [if_neg (by decide)]
    rcases mul_self_eq_one_iff.1 h3 with h4 | h4
    · have h5 : η a = 1 := Circle.ext h4
      rw [h5, one_mul] at h1
      exact absurd h1 hb
    · exact Circle.ext h4

theorem globalNormIndexTwo : Formalism.D.Classical.GlobalNormIndexTwo := by
  intro F E _ _ _ _ _ h2
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  refine ⟨signToCircle.comp (normSign E), ⟨?_, fun a => ?_, fun x => ?_, fun e => ?_⟩, ?_⟩
  · refine continuous_of_continuousAt_one _ ((continuousAt_const (y := (1 : Circle))).congr ?_)
    filter_upwards [eventually_normSign (K := F) E] with a ha
    rw [MonoidHom.comp_apply, ha, map_one]
  · exact (congrArg signToCircle (normSign_toUnits E a)).trans (map_one _)
  · exact (congrArg signToCircle (normSign_of_mem E ⟨x, rfl⟩)).trans (map_one _)
  · obtain ⟨a, ha⟩ := exists_normSign_ne_one (K := F) E
    have h : signToCircle (normSign E a) = 1 := DFunLike.congr_fun e a
    exact circle_neg_one_ne_one ((if_neg ha).symm.trans h)
  · rintro η ⟨-, h1, h3, h4⟩
    refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
    obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
    rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
    exact h1 t

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta in
theorem existsUnique_isEta : ∀ D : D7, ∃! η : (AF D.host.F)ˣ →* Circle, IsEta D η := fun D =>
  globalNormIndexTwo D.host.F D.host.E D.sp.cm.deg2

end GlobalTheory.IdeleNormChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotForallNonemptyLocP
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.KudlaSiegelWeil

namespace GlobalTheory.SmallThetaModules

section Restricted

variable {ι : Type} {N : ι → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

def AdmFun (s : ∀ i, N i) : Type := {l : ∀ i, N i →ₗ[ℂ] ℂ // {i | l i (s i) ≠ 1}.Finite}

def evFam (s : ∀ i, N i) (ξ : ∀ i, N i) : AdmFun s → ℂ := fun l => ∏ᶠ i, l.1 i (ξ i)

def RTens (s : ∀ i, N i) : Submodule ℂ (AdmFun s → ℂ) :=
  Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = evFam s ξ}


open Classical in
def pureT (s : ∀ i, N i) (ξ : ∀ i, N i) : RTens s :=
  if h : Restr s ξ then ⟨evFam s ξ, Submodule.subset_span ⟨ξ, h, rfl⟩⟩ else 0

theorem coe_pureT {s ξ : ∀ i, N i} (h : Restr s ξ) : (pureT s ξ : AdmFun s → ℂ) = evFam s ξ := by
  unfold pureT; rw [dite_eq_left h]

omit [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)] in
theorem restr_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (x : N v) :
    Restr s (Function.update ξ v x) := by
  refine (h.insert v).subset fun i hi => ?_
  by_cases hv : i = v
  · exact Or.inl hv
  · right
    simpa [Function.update_of_ne hv] using hi

theorem mulSupport_fin {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) :
    (Function.mulSupport fun i => l.1 i (ξ i)).Finite := by
  refine (Set.Finite.union h l.2).subset fun i hi => ?_
  by_cases e : ξ i = s i
  · right
    simpa [e] using hi
  · exact Or.inl e

theorem evFam_update [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (l : AdmFun s) (v : ι) (x : N v) :
    evFam s (Function.update ξ v x) l = l.1 v x * ∏ᶠ (i) (_ : i ≠ v), l.1 i (ξ i) := by
  unfold evFam
  rw [← mul_finprod_cond_ne v (mulSupport_fin (restr_update h v x) l), Function.update_self]
  congr 1
  refine finprod_congr fun i => finprod_congr fun hi => ?_
  rw [Function.update_of_ne hi]

theorem pureT_mlin [DecidableEq ι] {s ξ : ∀ i, N i} (h : Restr s ξ) (v : ι) (c : ℂ) (x y : N v) :
    pureT s (Function.update ξ v (c • x + y)) =
      c • pureT s (Function.update ξ v x) + pureT s (Function.update ξ v y) := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, coe_pureT (restr_update h v _), coe_pureT (restr_update h v _),
    coe_pureT (restr_update h v _)]
  funext l
  simp only [Pi.add_apply, Pi.smul_apply, evFam_update h, map_add (f := _), map_smul, smul_eq_mul]
  ring

theorem pureT_span (s : ∀ i, N i) :
    Submodule.span ℂ {z | ∃ ξ, Restr s ξ ∧ z = pureT s ξ} = ⊤ := by
  apply Submodule.map_injective_of_injective (RTens s).injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  change _ = Submodule.span ℂ _
  congr 1
  ext z
  constructor
  · rintro ⟨_, ⟨ξ, h, rfl⟩, rfl⟩
    exact ⟨ξ, h, coe_pureT h⟩
  · rintro ⟨ξ, h, rfl⟩
    exact ⟨_, ⟨ξ, h, rfl⟩, coe_pureT h⟩

theorem pureT_sep (s : ∀ i, N i) (l : ∀ i, N i →ₗ[ℂ] ℂ) (hl : {i | l i (s i) ≠ 1}.Finite) :
    ∃ Λ : RTens s →ₗ[ℂ] ℂ, ∀ ξ, Restr s ξ → Λ (pureT s ξ) = ∏ᶠ i, l i (ξ i) :=
  ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : AdmFun s => ℂ) (show AdmFun s from ⟨l, hl⟩)).comp (RTens s).subtype,
    fun _ h => congrFun (coe_pureT h) (show AdmFun s from ⟨l, hl⟩)⟩

theorem exists_lift {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (m : ∀ i, M i)
    {S : Type} [AddCommGroup S] [Module ℂ S] (pu : (∀ i, M i) → S)
    (hsep : ∀ l : ∀ i, M i →ₗ[ℂ] ℂ, {i | l i (m i) ≠ 1}.Finite →
      ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l i (φ i))
    (s : ∀ i, N i) (p : ∀ i, M i →ₗ[ℂ] N i) :
    ∃ P : S →ₗ[ℂ] RTens s, ∀ φ, Restr m φ → P (pu φ) = pureT s fun i => p i (φ i) := by
  by_cases hp : {i | p i (m i) ≠ s i}.Finite
  · have h1 : ∀ l : AdmFun s, ∃ Λ : S →ₗ[ℂ] ℂ, ∀ φ, Restr m φ → Λ (pu φ) = ∏ᶠ i, l.1 i (p i (φ i)) := by
      intro l
      refine hsep (fun i => (l.1 i).comp (p i)) ((hp.union l.2).subset fun i hi => ?_)
      by_cases e : p i (m i) = s i
      · right
        simpa [e] using hi
      · exact Or.inl e
    choose Λ hΛ using h1
    obtain ⟨r, hr⟩ := (RTens s).subtype.exists_leftInverse_of_injective (RTens s).ker_subtype
    refine ⟨r.comp (LinearMap.pi Λ), fun φ hφ => ?_⟩
    have h2 : Restr s fun i => p i (φ i) := by
      refine (Set.Finite.union hφ hp).subset fun i hi => ?_
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    have h3 : LinearMap.pi Λ (pu φ) = (RTens s).subtype (pureT s fun i => p i (φ i)) := by
      rw [Submodule.subtype_apply, coe_pureT h2]
      funext l
      exact hΛ l φ hφ
    rw [LinearMap.comp_apply, h3, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  · refine ⟨0, fun φ hφ => ?_⟩
    have h2 : ¬ Restr s fun i => p i (φ i) := by
      intro h
      refine hp ((Set.Finite.union hφ h).subset fun i hi => ?_)
      by_cases e : φ i = m i
      · right
        simpa [e] using hi
      · exact Or.inl e
    unfold pureT
    rw [dite_eq_right h2, LinearMap.zero_apply]

end Restricted

variable {D : D7} {X : ThetaX D}

section Collapse

open MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Collapse

end GlobalTheory.SmallThetaModules

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeAndTwistPlacesOverOtherThanSplit
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2 Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OtherPlaces

theorem conj_mem_of_comap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {w w' : HeightOneSpectrum (𝓞 E)}
    (h : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
      w'.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) (hne : w ≠ w') :
    ∀ c ∈ w.asIdeal, IsCMField.ringOfIntegersComplexConj E c ∈ w'.asIdeal := by
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ w'.asIdeal ∪
      (w'.asIdeal.comap (IsCMField.ringOfIntegersComplexConj E).toRingEquiv.toRingHom : Ideal (𝓞 E)) := by
    intro y hy
    obtain ⟨x, hx⟩ := (IsCMField.RingOfIntegers.complexConj_eq_self_iff E
      (y * IsCMField.ringOfIntegersComplexConj E y)).1 (by simp [mul_comm])
    have hx' : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x = y * IsCMField.ringOfIntegersComplexConj E y :=
      RingOfIntegers.ext hx
    have h1 : x ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by
      rw [Ideal.mem_comap, hx']; exact Ideal.mul_mem_right _ _ hy
    rw [h, Ideal.mem_comap, hx'] at h1
    exact w'.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h1 | h1
  · exact absurd (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top h1)) hne
  · exact fun c hc => h1 hc

theorem over_ne : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) →
    ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.v ∉ gPl D → s.w ∈ L.Q t →
      (∀ PP ∈ L.Pg, ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) ∧ (∀ PP ∈ L.Q t, PP ≠ s.w → ∃ v', NG.OverPl PP v' ∧ v' ≠ s.v) := by
  intro D T L μ0 hL hPg t s hs hsQ
  refine ⟨fun PP hPP => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => hs ?_⟩,
    fun PP hPP hne => ⟨PP.under (𝓞 (maximalRealSubfield D.host.E)), rfl, fun e => ?_⟩⟩
  · obtain ⟨k, v, rfl⟩ := (hPg PP).1 hPP
    exact ⟨D.naut.plGw k v, congrArg HeightOneSpectrum.asIdeal e, k, D.naut.plGw_over k v⟩
  · letI := D.host.isCMField_hostE
    refine (hL.Q_pl t s.w hsQ).2 PP hPP fun c hc => ⟨_, conj_mem_of_comap_eq
      (s.w_under.trans (congrArg HeightOneSpectrum.asIdeal e).symm) hne.symm c hc, rfl⟩

end GlobalTheory.OtherPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLatticesStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_completion_maps_dualLattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E)) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)), IsUnit J.det → Submodule.IsFullLattice E L → Submodule.IsFullLattice E Lb → y ∈ UPts σ J (v.adicCompletion F) → (∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) → ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  first | exact @GlobalTheory.DualCompletion.dual_move | exact GlobalTheory.DualCompletion.dual_move | (intros; apply GlobalTheory.DualCompletion.dual_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardOperatorPreservesRationalityStatement
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upwardOperator_preserves_rationality : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), (∀ i v h x, ∃ r : D.what₂.LL, D.what₂.embLL r = T.gl.psi0 i v h x) → ∀ (v : (D.mem u).A.vT) (x : ((D.fm u).lat 0).V), LT.Uop D u 0 v ((D.fm u).emb 0 x) ∈ (D.fm u).Fi 0 → ∃ y, (D.fm u).emb 0 y = LT.Uop D u 0 v ((D.fm u).emb 0 x) := by
  first | exact @GlobalTheory.LevelHecke.uop_rat | exact GlobalTheory.LevelHecke.uop_rat | (intros; apply GlobalTheory.LevelHecke.uop_rat <;> assumption)
end

