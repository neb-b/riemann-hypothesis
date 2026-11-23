module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ZOrth

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

theorem zOf_eq_alg {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : zOf χ = alg (zc χ) := rfl

theorem ip_simple {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    ip V.character W.character = if V.character = W.character then 1 else 0 := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have h := FDRep.char_orthonormal V W
  rw [Nat.card_eq_fintype_card] at h
  unfold ip
  rw [h]
  by_cases hi : Nonempty (V ≅ W)
  · rw [if_pos hi, if_pos (FDRep.char_iso hi.some)]
  · rw [if_neg hi]
    by_cases hc : V.character = W.character
    · exfalso
      have h1 := FDRep.char_orthonormal V V
      rw [if_pos ⟨CategoryTheory.Iso.refl V⟩] at h1
      have h2 := FDRep.char_orthonormal V W
      rw [if_neg hi, ← hc] at h2
      rw [h1] at h2
      simp at h2
    · rw [if_neg hc]

theorem zorth : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  intro G _ _ χ χ' hχ hχ'
  obtain ⟨V, hV, hVχ⟩ := hχ
  obtain ⟨W, hW, hWχ⟩ := hχ'
  have eV : V.character = χ := funext hVχ
  have eW : W.character = χ' := funext hWχ
  subst eV eW
  obtain ⟨⟨hidem, _⟩, hcen, horth, _⟩ := GlobalTheory.BadShare.ZCalc.zc_calc G V
  refine ⟨?_, ?_, ip_simple V W⟩
  · rw [zOf_eq_alg, zOf_eq_alg, ← alg_conv]
    by_cases hc : V.character = W.character
    · rw [if_pos hc, ← hc, hidem]
    · rw [if_neg hc, horth W hc]
      unfold alg; simp
  · intro a
    rw [zOf_eq_alg, ← alg_coeff a, ← alg_conv, ← alg_conv, hcen]
end GlobalTheory.GLq.ZOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBasicOfEquiv
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem acris_basic : ∀ (l : ℕ) [Fact l.Prime], (∀ x : Formalism.Per.Acris l, ((l : ℕ) : Formalism.Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : Formalism.Per.Acris l)}) (Formalism.Per.Acris l) ∧ (∀ (k : ℕ) (x : Formalism.Per.Acris l), ∃ d : ↥(Formalism.Per.Acris0 l), x - algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k}) ∧ ∀ (k : ℕ) (d : ↥(Formalism.Per.Acris0 l)), algebraMap ↥(Formalism.Per.Acris0 l) (Formalism.Per.Acris l) d ∈ Ideal.span {((l : ℕ) : Formalism.Per.Acris l) ^ k} ↔ d ∈ Ideal.span {((l : ℕ) : ↥(Formalism.Per.Acris0 l)) ^ k} := by
  intro l _
  obtain ⟨hc, ht, hd, hv⟩ := GlobalTheory.MemLoc.acris_basic l
  refine ⟨ht, hc, fun k x => ?_, fun k d => ?_⟩
  · obtain ⟨s, z, hz⟩ := hd x k
    exact ⟨s, Ideal.mem_span_singleton.2 ⟨z, by rw [hz, add_sub_cancel_left]⟩⟩
  · rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    exact hv d k

end GlobalTheory.Per
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFieldAutActsHarishChandraCharacters
section
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.FieldAut

section Rep

variable {G : Type} [Group G]

def galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) : Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) :=
  ((Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin (Module.finrank ℂ V))).toMulEquiv.toMonoidHom).comp
    (((σ : ℂ →+* ℂ).mapMatrix (m := Fin (Module.finrank ℂ V))).toMonoidHom.comp
      (((LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)).toMulEquiv.toMonoidHom).comp V.ρ))

theorem trace_galRep (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) (x : G) :
    LinearMap.trace ℂ _ (galRep σ V x) = σ (V.character x) := by
  have h1 : galRep σ V x =
      Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).map σ) := rfl
  have h2 : V.character x =
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (V.ρ x)).trace :=
    LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (V.ρ x)
  rw [h1, Matrix.trace_toLin'_eq, h2]
  simp [Matrix.trace]

variable [Fintype G]

theorem isIrr_comp (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (h : IsIrr χ) : IsIrr (σ ∘ χ) := by
  obtain ⟨V, hs, hV⟩ := h
  have hW : ∀ x, (FDRep.of (galRep σ V)).character x = σ (V.character x) := fun x => trace_galRep σ V x
  refine ⟨FDRep.of (galRep σ V), ?_, fun x => by rw [hW, hV]; rfl⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  have h := congrArg σ ((FDRep.simple_iff_char_is_norm_one V).1 hs)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_natCast, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by rw [map_mul, hW, hW]

theorem coeff_zOf (χ : G → ℂ) (y : G) :
    (zOf χ).coeff y = χ 1 / (Fintype.card G : ℂ) * χ y⁻¹ := by
  simp only [zOf, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mapRange_zOf (σ : ℂ ≃+* ℂ) (χ : G → ℂ) :
    (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff := by
  ext y
  rw [Finsupp.mapRange_apply, coeff_zOf, coeff_zOf]
  simp only [Function.comp, map_mul, map_div₀, map_natCast]

theorem ip_comp (σ : ℂ ≃+* ℂ) (α β : G → ℂ) : ip (σ ∘ α) (σ ∘ β) = σ (ip α β) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ip, Function.comp, map_mul, map_sum, map_inv₀, map_natCast]

end Rep

variable {g : ℕ} [Fact g.Prime]

theorem hc_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) (n : ℕ) :
    hc a b (σ ∘ α) (σ ∘ β) n = σ ∘ hc a b α β n := by
  funext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hc, hcT, Function.comp, map_mul, map_sum, map_inv₀, map_natCast, apply_ite σ, map_zero]

theorem degL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) = degL L := by
  simp [degL, List.map_map, Function.comp_def]

theorem hcL_map (σ : ℂ ≃+* ℂ) (L : List (Pc g)) :
    ∀ n, hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n := by
  induction L with
  | nil =>
    intro n
    funext x
    simp [hcL_nil]
  | cons p L ih =>
    intro n
    show hc p.1 (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g))) (σ ∘ p.2)
      (hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) (degL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)))) n = _
    rw [degL_map, ih, hc_comp, hcL_cons]

theorem res_comp (σ : ℂ ≃+* ℂ) (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (h₁ : Gn g a) (h₂ : Gn g b) :
    res a b (σ ∘ χ) h₁ h₂ = σ (res a b χ h₁ h₂) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [res, Function.comp, map_mul, map_sum, map_inv₀, map_pow, map_natCast, apply_ite σ, map_zero]

theorem isCusp_comp (σ : ℂ ≃+* ℂ) {d : ℕ} {χ : Gn g d → ℂ} (h : IsCusp χ) : IsCusp (σ ∘ χ) :=
  ⟨h.1, isIrr_comp σ h.2.1, fun a ha ha' => by rw [res_comp, h.2.2 a ha ha', map_zero]⟩

end GlobalTheory.CompanionTheory.FieldAut

theorem GlobalTheory.CompanionTheory.FieldAut.action : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  intro g _ σ
  exact ⟨fun G _ _ χ => ⟨GlobalTheory.CompanionTheory.FieldAut.isIrr_comp σ, GlobalTheory.CompanionTheory.FieldAut.mapRange_zOf σ χ,
    GlobalTheory.CompanionTheory.FieldAut.ip_comp σ χ⟩, fun L n => GlobalTheory.CompanionTheory.FieldAut.hcL_map σ L n,
    fun d χ h => GlobalTheory.CompanionTheory.FieldAut.isCusp_comp σ h⟩

end
end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.complexFieldAut_acts_harishChandra_characters : ∀ (g : ℕ) [Fact g.Prime] (σ : ℂ ≃+* ℂ), (∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsIrr χ → IsIrr (σ ∘ χ)) ∧ (zOf χ).coeff.mapRange σ (map_zero σ) = (zOf (σ ∘ χ)).coeff ∧ ∀ β, ip (σ ∘ χ) (σ ∘ β) = σ (ip χ β)) ∧ (∀ (L : List (Pc g)) (n : ℕ), hcL (L.map fun p => (⟨p.1, σ ∘ p.2⟩ : Pc g)) n = σ ∘ hcL L n) ∧ ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → IsCusp (σ ∘ χ) := by
  first | exact @GlobalTheory.CompanionTheory.FieldAut.action | exact GlobalTheory.CompanionTheory.FieldAut.action | (intros; apply GlobalTheory.CompanionTheory.FieldAut.action <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMulLeftDvr
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem continuous_of_mul_left_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {a : O} (ha : a ≠ 0) {f : X → O}
    (hf : Continuous fun x => a * f x) : Continuous f := by
  obtain ⟨hopen, hbasis⟩ := isAdic_iff.1 hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm := hϖ.maximalIdeal_eq
  rw [continuous_iff_continuousAt]
  intro x0
  have h0 : Filter.Tendsto (fun x => f x - f x0) (nhds x0) (nhds 0) := by
    intro s hs
    obtain ⟨n, hn⟩ := hbasis s hs
    have h1 : Continuous fun x => (u : O) * ϖ ^ k * f x - (u : O) * ϖ ^ k * f x0 := hf.sub continuous_const
    have h2 := (h1.isOpen_preimage _ (hopen (k + n))).mem_nhds (x := x0) (by simp)
    rw [Filter.mem_map]
    filter_upwards [h2] with x hx
    apply hn
    simp only [Set.mem_preimage, SetLike.mem_coe, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
    rw [← mul_sub, pow_add, mul_assoc, u.isUnit.dvd_mul_left, mul_dvd_mul_iff_left (pow_ne_zero k hϖ.ne_zero)] at hx
    exact hx
  have := h0.add_const (f x0)
  simpa [ContinuousAt] using this

theorem continuous_of_coeff_dvr {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [TopologicalSpace X]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) {n : ℕ} {M : X → Matrix (Fin n) (Fin n) O} (hM : Continuous M)
    (L : (Fin n → FractionRing O) →ₗ[FractionRing O] FractionRing O) (v : Fin n → FractionRing O) {f : X → O}
    (hf : ∀ x, algebraMap O (FractionRing O) (f x) = L (((M x).map (algebraMap O (FractionRing O))).mulVec v)) :
    Continuous f := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
    (fun p : Fin n × Fin n => L (Pi.single p.1 1) * v p.2)
  choose d hd using hb
  refine continuous_of_mul_left_dvr hO (nonZeroDivisors.coe_ne_zero b) ?_
  have : (fun x => (b : O) * f x) = fun x => ∑ p, ∑ q, d (p, q) * M x p q := by
    funext x
    apply IsFractionRing.injective O (FractionRing O)
    rw [map_mul, hf, LinearMap.pi_apply_eq_sum_univ L]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hd, Finset.mul_sum, Matrix.mulVec, dotProduct, Matrix.map_apply, smul_eq_mul,
      Finset.sum_mul, Algebra.smul_def]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have : (fun j => if p = j then (1 : FractionRing O) else 0) = Pi.single p 1 := by
      funext j; simp [Pi.single_apply, eq_comm]
    rw [this]; ring
  rw [this]
  fun_prop

theorem mapM_twistM_mulVec {O S Γ : Type} [CommRing O] [CommRing S] [Group Γ] {k : ℕ} (f : O →+* S)
    (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) (v : Fin k → S) :
    (mapM f (twistM M χ) g).mulVec v = f (χ g : O) • (mapM f M g).mulVec v := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext p q
  simp [mapM, twistM]

theorem subTw_blocks : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GoodR D.nd i r → ∀ (π : D.nd.X i) (e : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] ((Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i))), (∀ g u, e ((mapM (toK D.nd i) (rO D.nd i r π) g).mulVec u) = ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec (e u).1, fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 c)) → ∀ Xs : Set (D.nd.X i), π ∈ Xs → SubTw i r Xs (WpO D.nd i ρ π) ∧ ∀ c ∈ Finset.Icc 1 D.R.t, SubTw i r Xs (chiRatO D.nd i c) := by
  intro D i r ρ hr π e he Xs hπ
  have hO := D.nd.O_adic i
  have hrc : Continuous fun g => rO D.nd i r π g := (hr π).1
  have hχ : ∀ c, Continuous fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) := fun c => D.nd.chi_cont i c
  have hχi : Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have := (hχ 1).comp (continuous_inv (G := GE D.nd))
    refine this.congr fun g => ?_
    simp
  have hρc : Continuous fun g => rhoO D.nd i ρ π g := by
    refine continuous_matrix fun p q => ?_
    refine continuous_of_coeff_dvr hO hrc
      ((LinearMap.proj p).comp ((LinearMap.fst _ _ _).comp e.toLinearMap)) (e.symm (Pi.single q 1, 0)) fun g => ?_
    have := congrArg (fun z => z.1 p) (he g (e.symm (Pi.single q 1, 0)))
    simp only [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at this
    exact this.symm
  refine ⟨⟨hχi.smul hρc, π, hπ, e.symm.toLinearMap.comp (LinearMap.inl _ _ _),
    e.symm.injective.comp LinearMap.inl_injective, fun g v => ?_⟩, fun c hc => ?_⟩
  · rw [WpO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul]
    congr 1
    apply e.injective
    rw [he]
    simp
    rfl
  · obtain ⟨hc1, hc2⟩ := Finset.mem_Icc.1 hc
    let c' : Fin D.R.t := ⟨c - 1, by omega⟩
    have hcc : (c' : ℕ) + 1 = c := by simp only [c']; omega
    refine ⟨?_, π, hπ, e.symm.toLinearMap.comp ((LinearMap.inr _ _ _).comp
      ((LinearMap.single _ (fun _ => KK D.nd i) c').comp (LinearMap.proj 0))), ?_, fun g v => ?_⟩
    · have : Continuous fun g => (((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) *
          (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) :=
        ((hχ c).mul hχi).smul continuous_const
      exact this
    · intro v w h
      have h1 := congrArg (fun z => (e z).2 c') h
      funext j
      rw [Subsingleton.elim j 0]
      simpa using h1
    · rw [chiRatO, rTwO, mapM_twistM_mulVec, mapM_twistM_mulVec, map_smul, MonoidHom.mul_apply, Units.val_mul,
        map_mul, mul_comm, mul_smul]
      congr 1
      apply e.injective
      rw [he, map_smul]
      ext j
      · simp
      · by_cases hj : j = c'
        · subst hj
          simp [hcc, mapM, Algebra.smul_def]
        · simp [hj]

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DeRhamSpan

open GlobalTheory.DeRhamCompare
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod)

theorem span_of_invariant {G E M : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Module.Finite E M] {n : ℕ} (hn : n = finrank E M)
    (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : Fin n → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : Fin n → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (y : M) : ∃ c : Fin n → E, ∑ i, c i • v i = y := by
  letI := hE.toField
  have h := GlobalTheory.Per.linearIndependent_of_invariant G E M (Fin n) σ ρ hρ v hv hind
  have h2 := h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; exact hn)
  exact (Submodule.mem_span_range_iff_exists_fun E).1 (h2 ▸ Submodule.mem_top)

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_DdRK [FiniteDimensional Qp LL] [FiniteDimensional LL V] (h : IsDR PD ρ) :
    FiniteDimensional K (DdRK PD ρ) ∧ finrank K (DdRK PD ρ) = finrank Qp V := by
  have := PD.finK
  have := finite_DdR PD ρ h
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (DdR PD ρ) := Module.Finite.trans LL _
  let ε : DdR PD ρ ≃ₗ[Qp] DdRK PD ρ :=
    { toFun := fun x => _root_.GlobalTheory.DeRhamCompare.toK PD ρ x x.2
      invFun := fun y => ⟨(TensorProduct.comm Qp V BdR).symm y, y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [_root_.GlobalTheory.DeRhamCompare.toK])
      map_smul' := fun a x => Subtype.ext (by simp [_root_.GlobalTheory.DeRhamCompare.toK])
      left_inv := fun x => Subtype.ext (by simp [_root_.GlobalTheory.DeRhamCompare.toK])
      right_inv := fun x => Subtype.ext (by simp [_root_.GlobalTheory.DeRhamCompare.toK]) }
  have : FiniteDimensional Qp (DdRK PD ρ) := ε.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K (DdRK PD ρ)
  have h2 := Module.finrank_mul_finrank Qp LL (DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  rw [← ε.finrank_eq, ← h2, h, mul_left_comm, h3] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem span_of_isField [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hF : IsField BdR)
    (h : IsDR PD ρ) (y : V ⊗[Qp] BdR) :
    ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR), (∀ i, d i ∈ DdR PD ρ) ∧
      y = ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) := by
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have := hF.nontrivial
  obtain ⟨_, hr⟩ := finrank_DdRK PD ρ h
  let e := Module.finBasisOfFinrankEq K _ hr
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨b, hb⟩ := span_of_invariant (M := BdR ⊗[Qp] V) hF (n := finrank Qp V)
    Module.finrank_baseChange.symm
    (fun g => (PD.actdR g : BdR →+* BdR)) (fun g => (σ g).toAddMonoidHom) hσ
    (fun k => (e k : BdR ⊗[Qp] V))
    (fun g k => by
      have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
      rw [(mem_DdR PD ρ _).1 (e k).2 g, LinearEquiv.apply_symm_apply] at h1
      exact h1)
    (fun c hcg hsum k => by
      choose a ha using fun p => PD.invdR (c p) fun g => hcg g p
      have h1 : ∑ i, a i • e i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, ← ha, algebraMap_smul]
      rw [← ha, Fintype.linearIndependent_iff.1 e.linearIndependent a h1 k, map_zero])
    (TensorProduct.comm Qp V BdR y)
  refine ⟨_, b, fun k => (TensorProduct.comm Qp V BdR).symm (e k), fun k => (e k).2, ?_⟩
  apply (TensorProduct.comm Qp V BdR).injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, comm_mp, LinearEquiv.apply_symm_apply, hb]

end General

theorem tied_deRham_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ h y
  haveI := LL.2
  exact span_of_isField (P.PD K) ρ (GlobalTheory.Per.TiedField.tied_field l P AI T).1 h y

end GlobalTheory.Per.DeRhamSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeStableTwistedPairingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_stable_twisted_pairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  first | exact @GlobalTheory.DualLat.dualLattice_exists | exact GlobalTheory.DualLat.dualLattice_exists | (intros; apply GlobalTheory.DualLat.dualLattice_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryGeneratorH2Twist
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem bijective_phi_quot_pow : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ z : H2 (twist ε O), Function.Bijective (fun a : O => a • z) → ∀ k : ℕ, Function.Bijective (phi ε z (O ⧸ IsLocalRing.maximalIdeal O ^ k)) := by
  intro p _ K O _ _ _ _ _ G _ _ hT hK hO i ε hε z hz k
  haveI : ContinuousMul G := ⟨by
    have h : (fun q : G × G => q.1 * q.2) = fun q => i.symm (i q.1 * i q.2) := by
      funext q; simp
    rw [h]
    exact i.symm.continuous.comp
      ((i.continuous.comp continuous_fst).mul (i.continuous.comp continuous_snd))⟩
  have hinj := _root_.GlobalTheory.NatQuot.phi_quot_pow_injective hO (GlobalTheory.T.continuous_cyclotomic_character_localGalois hO i hε) z hz k
  obtain ⟨_, hcard⟩ := _root_.GlobalTheory.QuotientH2Count.h2_quot_card hT hK hO i hε k
  exact hinj.bijective_of_nat_card_le hcard

end GlobalTheory.FunctorialityH2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  first | exact @GlobalTheory.HWL.exists_kappa | exact GlobalTheory.HWL.exists_kappa | (intros; apply GlobalTheory.HWL.exists_kappa <;> assumption)
end

