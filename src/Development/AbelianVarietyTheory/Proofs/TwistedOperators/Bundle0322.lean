module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0300

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsFullLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : HasUniqueDiv Λ := ⟨fun k hk a b h => Subtype.ext
    (nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]


open Matrix in
theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsFullLattice K] [Λ'.IsFullLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dite_eq_left i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h0.sd
  haveI : (G.Λ (.core (i + 1))).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h1.sd
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensors
section
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.TensorMap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem finite_nonint {κ : Type} [Finite κ] (x : κ → AF F) :
    {w : Pl F | ¬ ∀ i, evFin F w (x i) ∈ w.adicCompletionIntegers F}.Finite := by
  have h : ∀ i, {w : Pl F | evFin F w (x i) ∉ w.adicCompletionIntegers F}.Finite := fun i =>
    Filter.eventually_cofinite.1 (x i).2.2
  refine (Set.finite_iUnion h).subset ?_
  intro w hw
  push_neg at hw
  obtain ⟨i, hi⟩ := hw
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}


open Classical in
def vacOff (M : Model σ Y W) (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) : ℂ :=
  ∏ᶠ w, if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i)

def prodT (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v =>
    (LinearMap.proj (fun i => evFin F v.1 (x i)) : ((Fin n × Fin d → Fv F v.1) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SB _).subtype

theorem prodT_apply (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    prodT T x φ = ∏ v : T, (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) fun i => evFin F v.1 (x i) := by
  simp [prodT]

def multi (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
  MultilinearMap.pi fun x => (f (fun i => evI F (x i)) * vacOff M T x) • prodT T x

theorem multi_apply (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (x : Fin n × Fin d → AF F) :
    multi M T f φ x = f (fun i => evI F (x i)) * vacOff M T x * prodT T x φ := by
  simp [multi]

def multiL (M : Model σ Y W) (T : Finset (Pl F)) :
    SInf F (Fin n × Fin d) →ₗ[ℂ]
      ((Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ)) where
  toFun := multi M T
  map_add' f g := by
    ext φ x
    simp only [multi_apply, MultilinearMap.add_apply, Pi.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext φ x
    simp only [multi_apply, MultilinearMap.smul_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring


open Classical in
theorem finprod_split (M : Model σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) (h2 : ∀ v ∉ T, φ' v = M.vac v) (x : Fin n × Fin d → AF F) :
    ∏ᶠ w, φ' w (fun i => evFin F w (x i)) = vacOff M T x * prodT T x φ := by
  set ρ : Pl F → ℂ := fun w => if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i) with hρdef
  set θ : Pl F → ℂ := fun w => if w ∈ T then φ' w (fun i => evFin F w (x i)) else 1 with hθdef
  have e : (fun w => φ' w (fun i => evFin F w (x i))) = fun w => θ w * ρ w := by
    funext w
    by_cases hw : w ∈ T
    · simp [θ, ρ, hw]
    · simp [θ, ρ, hw, h2 w hw]
  have hρ : (Function.mulSupport ρ).Finite := by
    refine ((Filter.eventually_cofinite.1 hstd).union (finite_nonint x)).subset ?_
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hw
    by_cases hwT : w ∈ T
    · simp [ρ, hwT]
    · simp only [ρ, hwT, if_false, hc.1]
      exact Set.indicator_of_mem (s := {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F}) hc.2 1
  have hθ : Function.mulSupport θ ⊆ (T : Set (Pl F)) := by
    intro w hw
    by_contra hc
    exact hw (by simp [θ, show w ∉ T from hc])
  rw [e, finprod_mul_distrib (T.finite_toSet.subset hθ) hρ, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset θ hθ, prodT_apply, ← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [θ, v.2, h1 v.1 v.2]

def tensL (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₗ[ℂ]
      ((Fin n × Fin d → AF F) → ℂ) :=
  TensorProduct.lift ((PiTensorProduct.lift.toLinearMap ∘ₗ multiL M T) ∘ₗ (M.Pol ψ emb).subtype)

theorem tensL_tmul (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (T : Finset (Pl F)) (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = multi M T (f : SInf F (Fin n × Fin d)) φ := by
  simp [tensL, multiL]

theorem exists_tensL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  intro F E _ _ _ _ _ σ n d Y W M ψ emb hstd T
  have hchar : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
      (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
      tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : SInf F (Fin n × Fin d)) φ' := by
    intro f φ φ' h1 h2
    funext x
    rw [tensL_tmul, multi_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, finprod_split M hstd T φ φ' h1 h2 x, mul_assoc]
  refine ⟨tensL M ψ emb T, hchar, Submodule.span_le.2 ?_⟩
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨⟨f, hf⟩ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => ⟨φ v.1, hφ v.1⟩),
    hchar ⟨f, hf⟩ _ φ (fun _ _ => rfl) hv⟩

end GlobalTheory.HoweGlobal.TensorMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic

variable {D : D7}

theorem gram_map_mul_inv {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    S.gram.map φ * (S.gram⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

theorem gram_inv_map_mul {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    (S.gram⁻¹).map φ * S.gram.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

def coordsLin (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    WO S' T' ≃ₗ[AE D] WO S T where
  toFun u := (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
  invFun x := ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
  map_add' u v := by
    show (u + v)ᵀ.submatrix e₂.symm e₁.symm * _ = uᵀ.submatrix e₂.symm e₁.symm * _ + vᵀ.submatrix e₂.symm e₁.symm * _
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl
  map_smul' c u := by
    show (c • u)ᵀ.submatrix e₂.symm e₁.symm * _ = c • (uᵀ.submatrix e₂.symm e₁.symm * _)
    rw [Matrix.transpose_smul, ← Matrix.smul_mul]
    rfl
  left_inv u := by
    show ((uᵀ.submatrix e₂.symm e₁.symm * S.gram.map (incA D) * (S.gram⁻¹).map (incA D))ᵀ).submatrix e₁ e₂ = u
    rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]
    ext i j; simp
  right_inv x := by
    dsimp only
    have : (((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂)ᵀ.submatrix e₂.symm e₁.symm =
        (HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
      ext i j; simp
    rw [this, Matrix.mul_assoc, gram_inv_map_mul, Matrix.mul_one]

theorem map_transpose_submatrix {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B) {m n p q : Type*}
    (u : Matrix m n A) (f : p → n) (g : q → m) : (uᵀ.submatrix f g).map φ = ((u.map φ)ᵀ).submatrix f g := rfl

theorem coordsLin_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') (h : x.map φ = 0) : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 := by
  change (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map φ = 0
  rw [Matrix.map_mul, map_transpose_submatrix, h]
  simp

theorem coordsLin_symm_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (y : WO S T) (h : y.map φ = 0) : ((coordsLin S T S' T' e₁ e₂).symm y).map φ = 0 := by
  change (((HMul.hMul y ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂).map φ = 0
  rw [map_transpose_submatrix, Matrix.map_mul, h]
  simp

theorem coordsLin_map_zero_iff {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, coordsLin_map_zero φ S T S' T' e₁ e₂ x⟩
  have := coordsLin_symm_map_zero φ S T S' T' e₁ e₂ _ h
  rwa [LinearEquiv.symm_apply_apply] at this

theorem coordsLin_rat_iff (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : coordsLin S T S' T' e₁ e₂ x ∈ ratL T S ↔ x ∈ ratL T' S' := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂, ?_⟩
    rw [← (coordsLin S T S' T' e₁ e₂).symm_apply_apply x, ← hγ]
    change (((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂).map (incA D) =
      ((HMul.hMul (γ.map (incA D)) ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    rw [map_transpose_submatrix, Matrix.map_mul]
  · rintro ⟨γ, rfl⟩
    refine ⟨γᵀ.submatrix e₂.symm e₁.symm * S.gram, ?_⟩
    change (γᵀ.submatrix e₂.symm e₁.symm * S.gram).map (incA D) =
      (HMul.hMul ((γ.map (incA D))ᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    rw [Matrix.map_mul, map_transpose_submatrix]

theorem coordsLin_spec (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  refine ⟨coordsLin S T S' T' e₁ e₂, fun _ => rfl, fun _ => rfl, ?_, ?_, coordsLin_rat_iff S T S' T' e₁ e₂,
    coordsLin_map_zero_iff _ S T S' T' e₁ e₂, coordsLin_map_zero_iff _ S T S' T' e₁ e₂⟩
  · change Continuous fun u : WO S' T' =>
      (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    exact (continuous_id.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const
  · change Continuous fun x : WO S T =>
      ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    exact ((continuous_id.matrix_mul continuous_const).matrix_transpose).matrix_submatrix _ _

end GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic
end
end

