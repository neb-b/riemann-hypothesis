module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0134
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0135
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsNormalizedRiemannLattice
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def ipLin (R : RiemLat E g Λ) (x : Fin g → ℂ) : (Fin g → ℂ) →ₗ[ℂ] ℂ where
  toFun := R.ip x
  map_add' y y' := by simp [RiemLat.ip, add_dotProduct]
  map_smul' c y := by simp [RiemLat.ip, smul_dotProduct]

theorem ip_eq_ipLin (R : RiemLat E g Λ) (x y : Fin g → ℂ) : R.ip x y = ipLin R x y := rfl

theorem conj_ip (R : RiemLat E g Λ) (x y : Fin g → ℂ) : starRingEnd ℂ (R.ip x y) = R.ip y x := by
  show star (y ⬝ᵥ R.Hm *ᵥ star x) = x ⬝ᵥ R.Hm *ᵥ star y
  rw [← star_dotProduct_star, star_mulVec, star_star, R.herm.eq, dotProduct_mulVec]

def diagAct (s : Fin g → (𝓞 E →+* ℂ)) : 𝓞 E →+* Module.End ℂ (Fin g → ℂ) where
  toFun a :=
    { toFun := fun x k => s k a * x k
      map_add' := fun x y => funext fun k => by simp [mul_add]
      map_smul' := fun r x => funext fun k => by simp [mul_left_comm] }
  map_one' := LinearMap.ext fun x => funext fun k => by simp
  map_mul' a b := LinearMap.ext fun x => funext fun k => by simp [mul_assoc]
  map_zero' := LinearMap.ext fun x => funext fun k => by simp
  map_add' a b := LinearMap.ext fun x => funext fun k => by simp [add_mul]

theorem diagAct_apply (s : Fin g → (𝓞 E →+* ℂ)) (a : 𝓞 E) (x : Fin g → ℂ) (k : Fin g) :
    diagAct s a x k = s k a * x k := rfl

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (R : RiemLat E g Λ) (e : ι ≃ Fin g) (c : ι → Fin g → ℂ)

include e

theorem sum_ip_smul (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (z : Fin g → ℂ) :
    ∑ i, R.ip (c i) z • c i = z := by
  have hli : LinearIndependent ℂ c := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h := congrArg (ipLin R (c k)) ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h
    simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul] at h
    simpa using h
  have hspan : Submodule.span ℂ (Set.range c) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by simp [Fintype.card_congr e])
  have hz : z ∈ Submodule.span ℂ (Set.range c) := hspan ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hz
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ip_eq_ipLin, map_sum]
  simp only [map_smul, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp

theorem sum_ip_mul_conj (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (u v : Fin g → ℂ) :
    ∑ i, R.ip (c i) u * starRingEnd ℂ (R.ip (c i) v) = R.ip v u := by
  conv_rhs => rw [← sum_ip_smul R e c hc u]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ip_eq_ipLin, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, ← ip_eq_ipLin, conj_ip, smul_eq_mul]

theorem ip_act (hc : ∀ i i', R.ip (c i) (c i') = if i = i' then 1 else 0) (s : ι → (𝓞 E →+* ℂ))
    (hs : ∀ i, c i ∈ eigSp R.B (s i)) (a : 𝓞 E) (i : ι) (z : Fin g → ℂ) :
    R.ip (c i) (R.B a z) = s i a * R.ip (c i) z := by
  have hB : ∀ l, R.B a (c l) = s l a • c l := fun l => by
    have h := (Submodule.mem_iInf _).1 (hs l) a
    have h' := LinearMap.mem_ker.1 h
    simpa [sub_eq_zero] using h'
  conv_lhs => rw [← sum_ip_smul R e c hc z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ip_eq_ipLin, map_sum]
  simp only [map_smul, hB, ← ip_eq_ipLin, hc, smul_eq_mul]
  simp [mul_comm]

end Frame

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' : ℕ}

theorem exists_riemLat_coord (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g)
    (c : Ix Ψ j j' → Fin g → ℂ) (hs : ∀ i, c i ∈ eigSp R₀.B (emb σ i))
    (hc : ∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) :
    ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k := by
  let P : Λ →+ (Fin g → ℂ) :=
    { toFun := fun x k => R₀.ip (c (e.symm k)) (R₀.P x)
      map_zero' := funext fun k => by simp [ip_eq_ipLin]
      map_add' := fun x y => funext fun k => by simp [ip_eq_ipLin] }
  have hP : ∀ x k, P x k = R₀.ip (c (e.symm k)) (R₀.P x) := fun _ _ => rfl
  refine ⟨{ free := R₀.free, fin := R₀.fin, rank := R₀.rank, form := R₀.form, alt := R₀.alt, unimod := R₀.unimod,
            adj := R₀.adj, P := P, Hm := 1, herm := isHermitian_one, pos := ?_, im := ?_,
            B := diagAct fun k => emb σ (e.symm k), act := ?_ }, rfl, rfl, fun _ _ _ => rfl⟩
  · intro z hz
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hz
    have hk' : z k ≠ 0 := hk
    have : (z ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star z).re = ∑ l, Complex.normSq (z l) := by
      simp [dotProduct, Complex.mul_conj]
    rw [this]
    exact Finset.sum_pos' (fun l _ => Complex.normSq_nonneg _) ⟨k, Finset.mem_univ _, Complex.normSq_pos.2 hk'⟩
  · intro x y
    have key : P x ⬝ᵥ (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ star (P y) = R₀.P x ⬝ᵥ R₀.Hm *ᵥ star (R₀.P y) := by
      have h := sum_ip_mul_conj R₀ e c hc (R₀.P x) (R₀.P y)
      rw [← e.symm.sum_comp] at h
      rw [one_mulVec]
      exact h
    rw [key]
    exact R₀.im x y
  · intro a x
    funext k
    rw [diagAct_apply, hP, hP, R₀.act]
    exact ip_act R₀ e c hc (emb σ) hs a (e.symm k) (R₀.P x)

theorem coord_lat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R₀ : RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (e : Ix Ψ j j' ≃ Fin g) (c : Ix Ψ j j' → Fin g → ℂ), (∀ i, c i ∈ eigSp R₀.B (emb σ i)) → (∀ i i', R₀.ip (c i) (c i') = if i = i' then 1 else 0) → ∃ R₁ : RiemLat E g Λ, R₁.form = R₀.form ∧ R₁.Hm = 1 ∧ ∀ a x k, R₁.B a x k = emb σ (e.symm k) a * x k :=
  fun R₀ σ e c hs hc => exists_riemLat_coord R₀ σ e c hs hc

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.CoordLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenusEqCardMulSignature
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim

theorem ringHom_injective {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem restrict_bijective (E : Type) [Field E] [NumberField E] :
    Function.Bijective (fun f : E →+* ℂ => f.comp (algebraMap (𝓞 E) E)) := by
  constructor
  · intro f f' h
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h
  · intro s
    refine ⟨IsFractionRing.lift (ringHom_injective s), ?_⟩
    ext a
    simp

theorem natCard_ringHom (E : Type) [Field E] [NumberField E] :
    Nat.card (𝓞 E →+* ℂ) = Module.finrank ℚ E := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (restrict_bijective E)), Nat.card_eq_fintype_card]
  exact NumberField.Embeddings.card E ℂ

def both {E Ψ : Type} [Field E] [NumberField E] (σ : Ψ → (𝓞 E →+* ℂ)) : Ψ ⊕ Ψ → (𝓞 E →+* ℂ) :=
  Sum.elim σ fun τ => (starRingEnd ℂ).comp (σ τ)

theorem conj_conj_comp {E : Type} [Field E] [NumberField E] (s : 𝓞 E →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a
  simp

theorem both_bijective {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Function.Bijective (both σ) := by
  have hconj : Function.Injective fun s : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp s := by
    intro s t hst
    have := congrArg (fun u : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp u) hst
    simpa only [conj_conj_comp] using this
  have hcross : ∀ τ τ', σ τ ≠ (starRingEnd ℂ).comp (σ τ') := by
    intro τ τ' e
    exact ((h.2 (σ τ')).1 ⟨τ', rfl⟩) ⟨τ, e⟩
  constructor
  · rintro (τ | τ) (τ' | τ') e
    · exact congrArg Sum.inl (h.1 e)
    · exact absurd e (hcross τ τ')
    · exact absurd e.symm (hcross τ' τ)
    · exact congrArg Sum.inr (h.1 (hconj e))
  · intro s
    by_cases hs : ∃ τ, σ τ = s
    · obtain ⟨τ, rfl⟩ := hs
      exact ⟨Sum.inl τ, rfl⟩
    · have h' : ∃ τ, σ τ = (starRingEnd ℂ).comp s := by
        by_contra hn
        exact hs ((h.2 s).2 hn)
      obtain ⟨τ, e⟩ := h'
      refine ⟨Sum.inr τ, ?_⟩
      show (starRingEnd ℂ).comp (σ τ) = s
      rw [e, conj_conj_comp]

theorem card_sum_eq_finrank {E Ψ : Type} [Field E] [NumberField E] [IsCMField E] [Fintype Ψ] {σ : Ψ → (𝓞 E →+* ℂ)}
    (h : IsCMFam σ) : Fintype.card (Ψ ⊕ Ψ) = Module.finrank ℚ E := by
  rw [← natCard_ringHom E, ← Nat.card_congr (Equiv.ofBijective _ (both_bijective h)), Nat.card_eq_fintype_card]

theorem eigSp_le_eigenspace {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) (θ : 𝓞 E) :
    eigSp B s ≤ Module.End.eigenspace (B θ) (s θ) := by
  intro x hx
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hx
  rw [Module.End.mem_eigenspace_iff]
  exact hx θ

theorem iSupIndep_eigSp {E V ι : Type} [Field E] [NumberField E] [AddCommGroup V] [Module ℂ V]
    (B : 𝓞 E →+* Module.End ℂ V) (σ : ι → (𝓞 E →+* ℂ)) (hσ : Function.Injective σ) :
    iSupIndep fun s => eigSp B (σ s) := by
  obtain ⟨θ, m, -, -, -, hgen⟩ := exists_integral_generator E
  have hagree : ∀ (τ : 𝓞 E →+* ℂ) (P : Polynomial ℤ), τ (Polynomial.aeval θ P) = Polynomial.aeval (τ θ) P := fun τ P =>
    (Polynomial.aeval_algHom_apply τ.toIntAlgHom θ P).symm
  have hinj : Function.Injective fun s => σ s θ := by
    intro s t hst
    apply hσ
    ext a
    obtain ⟨n, P, hn, hP⟩ := hgen a
    have h1 := hagree (σ s) P
    have h2 := hagree (σ t) P
    have hst' : σ s θ = σ t θ := hst
    rw [hst', ← h2, ← hP, map_mul, map_mul, map_intCast, map_intCast] at h1
    exact mul_left_cancel₀ (by exact_mod_cast hn) h1
  exact ((Module.End.eigenspaces_iSupIndep (B θ)).comp hinj).mono fun s => eigSp_le_eigenspace B (σ s) θ

theorem dim_eq_card_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (g j j' : ℕ) (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (σ : Ψ → (𝓞 E →+* ℂ)), IsCMFam σ → (∀ τ, Module.finrank ℂ (eigSp B (σ τ)) = j' ∧ Module.finrank ℂ (eigSp B ((starRingEnd ℂ).comp (σ τ))) = j) → g = Fintype.card Ψ * (j + j') := by
  intro E _ _ _ Ψ _ g j j' B σ hσ hdim
  classical
  have hb := both_bijective hσ
  have htop := iSup_eigSp_eq_top B (both σ) hb.1 (card_sum_eq_finrank hσ)
  have hind := iSupIndep_eigSp B (both σ) hb.1
  have hint := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap fun s => eigSp B (both σ s)) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun, Fintype.sum_sum_type] at e
  have h1 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inl τ))) = j' := fun τ => (hdim τ).1
  have h2 : ∀ τ, Module.finrank ℂ (eigSp B (both σ (Sum.inr τ))) = j := fun τ => (hdim τ).2
  simp only [h1, h2, Finset.sum_const, Finset.card_univ, smul_eq_mul] at e
  rw [← e]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.TangentDim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeRationalEmbedding
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates

open scoped TensorProduct nonZeroDivisors

theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ (k : ℕ) (b : 𝓞 E), k ≠ 0 ∧ (k : 𝓞 E) = b * a := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), b, ?_, hb.symm⟩
  rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact ha

theorem exists_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ], ∃ N : ℕ, Module.finrank ℚ E * N = Module.finrank ℤ Λ ∧ ∃ e : Λ →+ (Fin N → E), Function.Injective e ∧ (∀ (a : 𝓞 E) x, e (a • x) = (a : E) • e x) ∧ ∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v := by
  intro E _ _ _ Λ _ _ _ _
  let f : Λ →ₗ[𝓞 E] E ⊗[𝓞 E] Λ := TensorProduct.mk (𝓞 E) E Λ 1
  have hb : IsBaseChange E f := TensorProduct.isBaseChange _ _ _
  haveI h1 : IsLocalizedModule (𝓞 E)⁰ f := (isLocalizedModule_iff_isBaseChange (𝓞 E)⁰ E f).2 hb
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E :=
    IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  haveI h2 : IsLocalizedModule (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) f :=
    (isLocalizedModule_iff_isBaseChange _ E f).2 hb
  haveI h3 : IsLocalizedModule ℤ⁰ (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars _ f
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) Λ
  have hrank : Module.finrank ℚ E * Module.finrank E (E ⊗[𝓞 E] Λ) = Module.finrank ℤ Λ := by
    rw [← IsLocalizedModule.finrank_eq ℤ⁰ (f.restrictScalars ℤ) le_rfl,
      ← IsLocalization.finrank_eq ℚ ℤ⁰ le_rfl, Module.finrank_mul_finrank]
  have htors : ∀ x : Λ, f x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 E)⁰ f).1 hx
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero c)
    have hkx : (k : ℤ) • x = 0 := by
      rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), hkb, mul_smul]
      have : (c : 𝓞 E) • x = 0 := hc
      rw [this, smul_zero]
    exact (smul_eq_zero.1 hkx).resolve_left (by exact_mod_cast hk)
  let g := (Module.finBasis E (E ⊗[𝓞 E] Λ)).equivFun
  refine ⟨Module.finrank E (E ⊗[𝓞 E] Λ), hrank,
    AddMonoidHom.mk' (fun x => g (f x)) (fun x y => by simp only [map_add (f := _)]), ?_, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => htors x ?_
    exact g.map_eq_zero_iff.1 hx
  · intro a x
    change g (f (a • x)) = (a : E) • g (f x)
    rw [map_smul, ← map_smul g]
    congr 1
  · intro v
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (𝓞 E)⁰ f (g.symm v)
    obtain ⟨k, b, hk, hkb⟩ := exists_nat_eq_mul (nonZeroDivisors.coe_ne_zero s)
    refine ⟨k, b • x, hk, ?_⟩
    change g (f (b • x)) = k • v
    have hs' : (s : 𝓞 E) • g.symm v = f x := hs
    rw [map_smul, ← hs', ← mul_smul, ← hkb, Nat.cast_smul_eq_nsmul, map_nsmul, LinearEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.LatticeCoordinates
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetEqBallPotential
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot

theorem one_sub_bigZ {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    1 - (bigZ q t)ᴴ * bigZ q t = blockDiagonal fun τ =>
      fromBlocks (1 - (ballMat q t τ)ᴴ * ballMat q t τ) 0 0 (1 - ((ballMat q t τ)ᵀ)ᴴ * (ballMat q t τ)ᵀ) := by
  unfold bigZ
  rw [blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, ← blockDiagonal_sub]
  congr 1
  funext τ
  rw [Pi.sub_apply, Pi.one_apply, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]
  simp [sub_eq_add_neg]

theorem inv_blockDiagonal_fromBlocks {o a b : Type} [Fintype o] [DecidableEq o] [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (A : o → Matrix a a ℂ) (D : o → Matrix b b ℂ)
    (hA : ∀ k, (A k).det ≠ 0) (hD : ∀ k, (D k).det ≠ 0) :
    (blockDiagonal fun k => fromBlocks (A k) 0 0 (D k))⁻¹ =
      blockDiagonal fun k => fromBlocks (A k)⁻¹ 0 0 (D k)⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [← blockDiagonal_mul, ← blockDiagonal_one]
  congr 1
  funext k
  rw [fromBlocks_multiply, Pi.one_apply, ← fromBlocks_one]
  have h1 : (A k)⁻¹ * A k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hA k))
  have h2 : (D k)⁻¹ * D k = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hD k))
  simp [h1, h2]

theorem det_conj_block {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (Z : Matrix b a ℂ) :
    (1 - (Zᵀ)ᴴ * Zᵀ).det = (1 - Zᴴ * Z).det := by
  rw [Matrix.det_one_sub_mul_comm, ← Matrix.det_transpose (1 - Zᴴ * Z)]
  congr 1
  rw [transpose_sub, transpose_one, transpose_mul]
  congr 1

theorem inv_apply_inl {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ)
    (ht : t ∈ ballDom q) (τ : Ψ) (a b : Fin j') :
    (1 - (bigZ q t)ᴴ * bigZ q t)⁻¹ (Sum.inl a, τ) (Sum.inl b, τ) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹ : Matrix (Fin j') (Fin j') ℂ) a b := by
  have hA : ∀ k, (1 - (ballMat q t k)ᴴ * ballMat q t k).det ≠ 0 := fun k => (ht k).det_pos.ne'
  have hD : ∀ k, (1 - ((ballMat q t k)ᵀ)ᴴ * (ballMat q t k)ᵀ).det ≠ 0 := fun k => by
    rw [det_conj_block]; exact hA k
  rw [one_sub_bigZ, inv_blockDiagonal_fromBlocks _ _ hA hD]
  simp

theorem one_sub_bigZe {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) :
    (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹ = ((1 - (bigZ q t)ᴴ * bigZ q t)⁻¹).submatrix e.symm e.symm := by
  have h : 1 - (bigZe e q t)ᴴ * bigZe e q t = (1 - (bigZ q t)ᴴ * bigZ q t).submatrix e.symm e.symm := by
    unfold bigZe
    have h1 : (1 : Matrix (Fin g) (Fin g) ℂ) = (1 : Matrix (Ix Ψ j j') (Ix Ψ j j') ℂ).submatrix e.symm e.symm :=
      (submatrix_one_equiv e.symm).symm
    rw [conjTranspose_submatrix, submatrix_mul_equiv, h1]
    rfl
  rw [h, inv_submatrix_equiv]

theorem log_det_inv {a : Type} [Fintype a] [DecidableEq a] (A : Matrix a a ℂ) (hA : A.PosDef) :
    Real.log (A⁻¹).det.re = -Real.log A.det.re := by
  have hpos : 0 < A.det := hA.det_pos
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hpos
  have hreal : A.det = (A.det.re : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hinv : (A⁻¹).det = ((A.det.re)⁻¹ : ℝ) := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hreal]
    simp
  rw [hinv, Complex.ofReal_re, Real.log_inv]

theorem logDet_coord {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]
    {j j' n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (R : RiemLat E g Λ) (ht : t ∈ ballDom q)
    (hH : R.Hm = (1 - (bigZe e q t)ᴴ * bigZe e q t)⁻¹) :
    R.logDet (fun τ (i : Fin j') => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) = ballPot q t := by
  unfold RiemLat.logDet ballPot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hG : R.gram (fun i : Fin j' => (Pi.single (e (Sum.inl i, τ)) 1 : Fin g → ℂ)) =
      ((1 - (ballMat q t τ)ᴴ * ballMat q t τ)⁻¹)ᵀ := by
    ext a b
    have hs : star (Pi.single (e (Sum.inl a, τ)) 1 : Fin g → ℂ) = Pi.single (e (Sum.inl a, τ)) 1 := by
      ext i
      by_cases h : i = e (Sum.inl a, τ)
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    simp only [RiemLat.gram, RiemLat.ip, Matrix.of_apply, hs, transpose_apply]
    rw [Matrix.mulVec_single_one, single_one_dotProduct, hH, one_sub_bigZe]
    simp [inv_apply_inl q t ht]
  rw [hG, det_transpose, log_det_inv _ (ht τ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ.GramPot
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymmetricMatrixInBallImage
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.Cusp.Univ

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Univ

theorem exists_bigZe_eq {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {j j' n g : ℕ} (e : Ix Ψ j j' ≃ Fin g)
    (q : Ψ × Fin j × Fin j' ≃ Fin n) (Z : Matrix (Fin g) (Fin g) ℂ) (hs : Zᵀ = Z)
    (hZ : ∀ i k, Z i k ≠ 0 → (e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) :
    ∃ t, bigZe e q t = Z := by
  have hz : ∀ i k, ¬ ((e.symm i).2 = (e.symm k).2 ∧ (e.symm i).1.isLeft ≠ (e.symm k).1.isLeft) → Z i k = 0 :=
    fun i k h => by_contra fun h0 => h (hZ i k h0)
  have hsym : ∀ i k, Z i k = Z k i := fun i k => by
    have := congrFun (congrFun hs k) i
    simpa [Matrix.transpose_apply] using this
  let t : Fin n → ℂ := fun m => Z (e (Sum.inr (q.symm m).2.1, (q.symm m).1)) (e (Sum.inl (q.symm m).2.2, (q.symm m).1))
  have hb : ∀ τ a b, ballMat q t τ a b = Z (e (Sum.inr a, τ)) (e (Sum.inl b, τ)) := by
    intro τ a b
    simp [ballMat, t]
  refine ⟨t, ?_⟩
  ext i k
  obtain ⟨⟨x, τ⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨y, τ'⟩, rfl⟩ := e.surjective k
  simp only [bigZe, bigZ, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  by_cases hτ : τ = τ'
  · subst hτ
    rw [Matrix.blockDiagonal_apply_eq]
    rcases x with a | a <;> rcases y with b | b
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.transpose_apply, hb, hsym]
    · rw [Matrix.fromBlocks_apply₂₁, hb]
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]
      exact (hz _ _ (by simp)).symm
  · rw [Matrix.blockDiagonal_apply_ne _ _ _ hτ]
    exact (hz _ _ (by simp [hτ])).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.Univ
end

