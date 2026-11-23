module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LinearIndependentEigProj
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0048
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0031
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0009

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeGenericAgree
section
open AlgebraicGeometry CategoryTheory Limits NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GenAgree

theorem iotaMulti_rows {K V : Type} [Field K] [AddCommGroup V] [Module K V] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (z : Fin n → V) :
    exteriorPower.ιMulti K n (fun i => ∑ j, M i j • z j) = M.det • exteriorPower.ιMulti K n z := by
  have hA : (exteriorPower.ιMulti K n).compLinearMap (Fintype.linearCombination K z) =
      (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K).smulRight
        (exteriorPower.ιMulti K n z) := by
    refine (Pi.basisFun K (Fin n)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin n) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun K (Fin n) (u i)) = (fun i => Pi.basisFun K (Fin n) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin n → K) [⋀^Fin n]→ₗ[K] K)
        (fun i => Pi.basisFun K (Fin n) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin n) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp [Fintype.linearCombination_apply, Pi.basisFun_apply]
  exact AlternatingMap.congr_fun hA M

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem det_ne_zero_of_li {M : Type} [AddCommGroup M] [Module Ω M] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent Ω v) {P : Matrix (Fin n) (Fin n) Ω}
    (h : LinearIndependent Ω fun i => ∑ j, P i j • v j) : P.det ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have h1 : ∑ i, c i • ∑ j, P i j • v j = 0 := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := congrFun hc0 j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at this
    rw [this, zero_smul]
  exact hc (funext (Fintype.linearIndependent_iff.1 h c h1))

theorem detLat_apply_eq {F : Type} [AddCommGroup F] [Module Ω F] {Λ : Lat ξ F} {n : ℕ} {u : Fin n → F}
    (hu : LinearIndependent Ω u) {x : Cpt ξ} {A₀ : Matrix (Fin n) (Fin n) Ω}
    (h : Λ.IsFrameAt (fun i => ∑ j, A₀ i j • u j) x) :
    detLat Λ u x = Submodule.span (regAt ξ x) {A₀.det} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    obtain ⟨c, hc, -, -, e⟩ := GlobalTheory.CompanionTheory.Ggeo.FrameDet.det_eq_unit_mul Ω F (regAt ξ x) n u A₀ A hu h.1 hA.1 (h.2.symm.trans hA.2)
    rw [e]
    exact Submodule.mem_span_singleton.2 ⟨⟨c, hc⟩, rfl⟩
  · exact Submodule.span_mono (by rintro _ rfl; exact ⟨A₀, h, rfl⟩)

theorem span_smul_of_unit {F : Type} [AddCommGroup F] [Module Ω F] {x : Cpt ξ} {c : Ω} (hc : c ∈ regAt ξ x)
    (hc' : c⁻¹ ∈ regAt ξ x) (h0 : c ≠ 0) (y : F) :
    Submodule.span (regAt ξ x) {c • y} = Submodule.span (regAt ξ x) {y} := by
  apply le_antisymm <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨c, hc⟩, rfl⟩
  · exact ⟨⟨c⁻¹, hc'⟩, by change c⁻¹ • c • y = y; rw [inv_smul_smul₀ h0]⟩

section Key
variable [CharZero Ω] {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module Ω V]
  [FiniteDimensional Ω V] {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {bar : 𝓞 E ≃+* 𝓞 E} {p q : ℕ}

theorem key (𝓗 : HodgeLat L ρ bar (p + q)) {σ σ' : E →+* Ω} {v : Fin p → V} {w : Fin q → V}
    {u : Fin (p + q) → V × Module.Dual Ω V} {x : Cpt ξ}
    (h1 : ∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) (h2 : ∀ a, bar (bar a) = a)
    (hreg : ∀ a : E, σ a ∈ regAt ξ x ∧ σ' a ∈ regAt ξ x)
    (hv : LinearIndependent Ω v) (hvs : Submodule.span Ω (Set.range v) = HT.eigSp ρ σ)
    (hw : LinearIndependent Ω w) (hws : Submodule.span Ω (Set.range w) = HT.eigSp ρ σ')
    (had : IsAdapted 𝓗.ρH σ v w u) {P : Matrix (Fin p) (Fin p) Ω} {Q : Matrix (Fin q) (Fin q) Ω}
    (hP : (L.inter (HT.eigSp ρ σ)).IsFrameAt (fun i => ∑ j, P i j • v j) x)
    (hQ : (L.inter (HT.eigSp ρ σ')).IsFrameAt (fun i => ∑ j, Q i j • w j) x) :
    ∃ A : Matrix (Fin (p + q)) (Fin (p + q)) Ω, (𝓗.quot σ).IsFrameAt (fun i => ∑ j, A i j • u j) x ∧
      A.det = P.det / Q.det := by
  classical
  obtain ⟨huli, husp, hinv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  obtain ⟨hq, -, hmap⟩ := GlobalTheory.CompanionTheory.Ar.Flat.QuotEig.quot_eig X Ω ξ E V L ρ bar (p + q) 𝓗 σ x (fun a => (hreg a).1)
  obtain ⟨-, hL', -⟩ := GlobalTheory.CompanionTheory.Ar.Flat.QuotEig.quot_eig X Ω ξ E V L ρ bar (p + q) 𝓗 σ' x (fun a => (hreg a).2)
  have hP0 := det_ne_zero_of_li hv hP.1
  have hQ0 := det_ne_zero_of_li hw hQ.1
  have hdual : ∀ φ : Module.Dual Ω V, ((0 : V), φ) ∈ 𝓗.HL x ↔ φ ∈ L.dual x := fun φ => by
    rw [← congrFun 𝓗.comap_inr x]
    rfl
  let C : Matrix (Fin q) (Fin q) Ω := (Q.transpose)⁻¹
  have hCQ : C * Q.transpose = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hQ0)
  have hCd : C.det * Q.det = 1 := by
    have := congrArg Matrix.det hCQ
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hC0 : C.det ≠ 0 := left_ne_zero_of_mul_eq_one hCd
  let φ : Fin q → Module.Dual Ω V := fun k => (u (Fin.natAdd p k)).2
  let ψ : Fin q → Module.Dual Ω V := fun j => ∑ k, C j k • φ k
  let b : Fin q → V := fun l => ∑ m, Q l m • w m
  let c : Fin q → V × Module.Dual Ω V := fun j => ∑ k, C j k • u (Fin.natAdd p k)
  have hc : ∀ j, c j = ((0 : V), ψ j) := fun j => by
    refine Prod.ext ?_ ?_
    · simp only [c, Prod.fst_sum, Prod.smul_fst, (had.2.2 _).1, smul_zero, Finset.sum_const_zero]
    · simp only [c, ψ, φ, Prod.snd_sum, Prod.smul_snd]
  have hceig : ∀ j, c j ∈ HT.eigSp 𝓗.ρH σ := fun j =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (had.1 _)
  have hψinv : ∀ j, ψ j ∘ₗ HT.eigProj ρ σ' = ψ j := fun j => hinv (ψ j) (hc j ▸ hceig j)
  have hψb : ∀ j l, ψ j (b l) = if j = l then 1 else 0 := fun j l => by
    have e1 : ∀ k, φ k (b l) = Q l k := fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [b, map_sum, map_smul, φ, (had.2.2 k).2, smul_eq_mul, mul_ite, mul_one, mul_zero]
      simp
    have e2 : ψ j (b l) = (C * Q.transpose) j l := by
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, e1, smul_eq_mul, Matrix.mul_apply,
        Matrix.transpose_apply]
    rw [e2, hCQ, Matrix.one_apply]
  have hbsp : Submodule.span Ω (Set.range b) = HT.eigSp ρ σ' := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hws ▸ Submodule.subset_span ⟨m, rfl⟩)
    · rw [finrank_span_eq_card hQ.1, ← hws, finrank_span_eq_card hw]
  have hbL : ∀ l, b l ∈ L x := fun l => by
    have : b l ∈ (L.inter (HT.eigSp ρ σ')) x := hQ.2 ▸ Submodule.subset_span ⟨l, rfl⟩
    exact this.1
  have hcH : ∀ j, c j ∈ 𝓗.quot σ x := fun j => by
    refine (hq _).2 ⟨?_, hceig j⟩
    rw [hc j, hdual]
    intro z hz
    have e1 : ψ j z = ψ j (HT.eigProj ρ σ' z) := (LinearMap.congr_fun (hψinv j) z).symm
    have e2 : HT.eigProj ρ σ' z ∈ (L.inter (HT.eigSp ρ σ')) x := ⟨hL' z hz, HT.LatBasic.eigProj_mem ρ σ' z⟩
    rw [hQ.2] at e2
    obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 e2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, ← hr, map_sum]
    refine sum_mem fun l _ => ?_
    have e3 : ψ j ((r l) • b l) = (r l : Ω) * ψ j (b l) := by
      change ψ j ((r l : Ω) • b l) = _
      rw [map_smul, smul_eq_mul]
    rw [e3, hψb]
    split_ifs
    · simpa using (r l).2
    · simp
  have hker : ∀ y ∈ 𝓗.quot σ x, LinearMap.fst Ω V (Module.Dual Ω V) y = 0 →
      y ∈ Submodule.span (regAt ξ x) (Set.range c) := by
    rintro ⟨y₁, θ⟩ hy hy0
    obtain rfl : y₁ = 0 := hy0
    obtain ⟨hyH, hye⟩ := (hq _).1 hy
    have hθ := hinv θ hye
    have hθL := (hdual θ).1 hyH
    have hreg' : ∀ j, θ (b j) ∈ regAt ξ x := fun j => hθL _ (hbL j)
    have e : ((0 : V), θ) = ∑ j, (⟨θ (b j), hreg' j⟩ : regAt ξ x) • c j := by
      have e0 : ∀ j, (⟨θ (b j), hreg' j⟩ : regAt ξ x) • c j = θ (b j) • c j := fun j => rfl
      simp only [e0, hc]
      refine Prod.ext ?_ ?_
      · simp [Prod.fst_sum]
      · simp only [Prod.snd_sum, Prod.smul_snd]
        refine LinearMap.ext fun z => ?_
        have hz : HT.eigProj ρ σ' z ∈ Submodule.span Ω (Set.range b) := hbsp ▸ HT.LatBasic.eigProj_mem ρ σ' z
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
        have e1 : θ z = θ (HT.eigProj ρ σ' z) := (LinearMap.congr_fun hθ z).symm
        have e2 : ∀ j, ψ j z = d j := fun j => by
          have : ψ j z = ψ j (HT.eigProj ρ σ' z) := (LinearMap.congr_fun (hψinv j) z).symm
          set_option synthInstance.maxHeartbeats 100000 in
            rw [this, ← hd, map_sum]
          simp [hψb]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [e1, ← hd, map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [LinearMap.smul_apply, map_smul, e2, smul_eq_mul]
        exact mul_comm _ _
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨A, hAd, hAl, hAs⟩ := GlobalTheory.CompanionTheory.Ggeo.ext_frame_of_quotient_kernel Ω (V × Module.Dual Ω V) V (regAt ξ x) (𝓗.quot σ x)
    (LinearMap.fst Ω V (Module.Dual Ω V)) p q u v P C huli hv (fun y hy => husp ▸ ((hq y).1 hy).2)
    (fun i => had.2.1 i) (fun j => (had.2.2 j).1) hP0 hC0 (hmap.trans hP.2) hcH hker
  refine ⟨A, ⟨hAl, hAs⟩, ?_⟩
  rw [hAd, eq_div_iff hQ0, mul_assoc, hCd, mul_one]

end Key

theorem hodge_lattice_generic_agree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (x : Cpt ξ) (t : Ω), IsCptGen ξ → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a : E, σ a ∈ regAt ξ x ∧ σ' a ∈ regAt ξ x) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → ((t ≠ 0 ∧ IsCoeffAt (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (exteriorPower.ιMulti Ω p v) (exteriorPower.ιMulti Ω q w) x t⁻¹ → (detLat (𝓗.quot σ) u).IsGenAt x t) ∧ ((∃ (n : ℕ) (b : Fin n → V), L.IsFrameAt b x) → (detLat (𝓗.quot σ) u).IsGenAt x t → t ≠ 0 ∧ IsCoeffAt (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (exteriorPower.ιMulti Ω p v) (exteriorPower.ιMulti Ω q w) x t⁻¹)) := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u x t hξ h1 h2 hreg hv hvs hw hws had
  haveI : IsLocalRing (regAt ξ x) := EigSplit.isLocalRing_regAt x
  obtain ⟨huli, husp, hinv⟩ := GlobalTheory.CompanionTheory.Ar.Flat.AdaptedSpan.adapted_span X Ω ξ E V L ρ bar p q (p + q) 𝓗 σ σ' v w u h1 h2 hv hvs hw hws had
  refine ⟨?_, ?_⟩
  · rintro ⟨ht, α, β, hα, hβ, hA, hB, e⟩
    obtain ⟨P, hPl, hPs, c, hc, hc', hc0, hPd⟩ := GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_frame Ω V (regAt ξ x) ((L.inter (HT.eigSp ρ σ)) x) p v α hv
      (fun y hy => hvs ▸ hy.2) hα hA
    obtain ⟨Q, hQl, hQs, d, hd, hd', hd0, hQd⟩ := GlobalTheory.CompanionTheory.Ar.Flat.WedgeFrame.wedge_frame Ω V (regAt ξ x) ((L.inter (HT.eigSp ρ σ')) x) q w β hw
      (fun y hy => hws ▸ hy.2) hβ hB
    obtain ⟨A, hAf, hAd⟩ := key 𝓗 h1 h2 hreg hv hvs hw hws had (P := P) (Q := Q) ⟨hPl, hPs⟩ ⟨hQl, hQs⟩
    refine ⟨ht, ?_⟩
    rw [detLat_apply_eq huli hAf]
    have e1 : A.det = (c / d) • t := by
      have : t = α / β := by rw [← e]; field_simp
      rw [hAd, hPd, hQd, this, smul_eq_mul]; field_simp
    rw [e1, span_smul_of_unit (div_eq_mul_inv c d ▸ mul_mem hc hd')
      (by rw [inv_div, div_eq_mul_inv]; exact mul_mem hd hc') (div_ne_zero hc0 hd0)]
  · rintro hfr ⟨ht, hsp⟩
    have hLσ := (GlobalTheory.CompanionTheory.Ar.Flat.QuotEig.quot_eig X Ω ξ E V L ρ bar (p + q) 𝓗 σ x (fun a => (hreg a).1)).2.1
    have hLσ' := (GlobalTheory.CompanionTheory.Ar.Flat.QuotEig.quot_eig X Ω ξ E V L ρ bar (p + q) 𝓗 σ' x (fun a => (hreg a).2)).2.1
    obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.Ar.Flat.InterFrame.exists_frame_inter X Ω ξ E V L ρ bar p (p + q) 𝓗 σ v x hLσ hv hvs hfr
    obtain ⟨Q, hQ⟩ := GlobalTheory.CompanionTheory.Ar.Flat.InterFrame.exists_frame_inter X Ω ξ E V L ρ bar q (p + q) 𝓗 σ' w x hLσ' hw hws hfr
    obtain ⟨A, hAf, hAd⟩ := key 𝓗 h1 h2 hreg hv hvs hw hws had hP hQ
    have hP0 := det_ne_zero_of_li hv hP.1
    have hQ0 := det_ne_zero_of_li hw hQ.1
    have hA0 : A.det ≠ 0 := by rw [hAd]; exact div_ne_zero hP0 hQ0
    rw [detLat_apply_eq huli hAf] at hsp
    obtain ⟨y, hy, e⟩ := ZUnit.exists_of_span_eq (p := x) ht hsp.symm
    have et : t = y * (P.det / Q.det) := by rw [e, hAd, smul_eq_mul]
    have hy0 := hy.1
    refine ⟨ht, P.det, y⁻¹ * Q.det, hP0, mul_ne_zero (inv_ne_zero hy0) hQ0, ?_, ?_, ?_⟩
    · rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ V _ p _ x hP, iotaMulti_rows]
    · rw [Lat.wedge_eq_span_of_isFrameAt X Ω ξ V _ q _ x hQ, iotaMulti_rows, mul_smul,
        span_smul_of_unit hy.2.2 (by rw [inv_inv]; exact hy.2.1) (inv_ne_zero hy0)]
    · rw [et]; field_simp

theorem generic_agree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [CharZero Ω] (E : Type) [Field E] [NumberField E] (V : Type) [AddCommGroup V] [Module Ω V] [FiniteDimensional Ω V] (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (bar : 𝓞 E ≃+* 𝓞 E) (p q : ℕ) (𝓗 : HodgeLat L ρ bar (p + q)) (σ σ' : E →+* Ω) (v : Fin p → V) (w : Fin q → V) (u : Fin (p + q) → V × Module.Dual Ω V) (x : Cpt ξ) (t : Ω), IsCptGen ξ → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → (∀ a : E, σ a ∈ regAt ξ x ∧ σ' a ∈ regAt ξ x) → LinearIndependent Ω v → Submodule.span Ω (Set.range v) = HT.eigSp ρ σ → LinearIndependent Ω w → Submodule.span Ω (Set.range w) = HT.eigSp ρ σ' → IsAdapted 𝓗.ρH σ v w u → ((detLat (𝓗.quot σ) u).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt (L.inter (HT.eigSp ρ σ)) (L.inter (HT.eigSp ρ σ')) p q (exteriorPower.ιMulti Ω p v) (exteriorPower.ιMulti Ω q w) x t⁻¹) := by
  intro X Ω _ ξ _ E _ _ V _ _ _ L ρ bar p q 𝓗 σ σ' v w u x t hξ h1 h2 hreg hv hvs hw hws had
  have h := hodge_lattice_generic_agree X Ω ξ E V L ρ bar p q 𝓗 σ σ' v w u x t hξ h1 h2 hreg hv hvs hw hws had
  obtain ⟨U, hU, b, -, hb⟩ := 𝓗.vb x trivial
  exact ⟨h.2 ⟨_, b, hb x trivial hU⟩, h.1⟩

end GlobalTheory.CompanionTheory.Ar.Flat.GenAgree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem lat_stable : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (O : Type) [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω V), M.IsActOf act.act ρ → ∀ (p : Cpt ξ) (a : O), ∀ e ∈ M.lat p, ρ a e ∈ M.lat p := by
  intro X Ω _ ξ G _ V _ _ M O _ act ρ hact p a e he
  change e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v} at he
  change ρ a e ∈ Submodule.span (regAt ξ p) {e | ∃ v, M.Extends p e v}
  induction he using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    unfold LieModel.Extends at hv
    obtain ⟨hv1, hv2⟩ := hv
    refine Submodule.subset_span ⟨v ≫ act.act a, ?_⟩
    unfold LieModel.Extends
    refine ⟨?_, ?_⟩
    · unfold IsTanAt at hv1 ⊢
      have := act.hom a
      rw [Over.comp_left, ← Category.assoc, hv1, ← Over.comp_left]
      congr 1
      simp
    · have h := hact a x
      rw [h, Over.comp_left, hv2, Over.comp_left]
      exact Category.assoc _ _ _
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

end GlobalTheory.CompanionTheory.Ar.LieStable
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackAction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieBaseAct

theorem baseChange_act : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V') (j : V →+ V') (O : Type) [CommRing O] (act : O → (G ⟶ G)) (act' : O → (G' ⟶ G')) (ρ : O →+* Module.End Ω V) (ρ' : O →+* Module.End Ω' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → (∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left) → M.IsActOf act ρ → M'.IsActOf act' ρ' → (∀ a, (act' a).left ≫ φ = φ ≫ (act a).left) → ∀ a e, ρ' a (j e) = j (ρ a e) := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' j O _ act act' ρ ρ' _ hpb hpt hM hM' hcomm a e
  apply M'.inj
  rw [hM' a (j e)]
  apply Over.OverMorphism.ext
  apply hpb.1.hom_ext
  · simp only [Over.comp_left, Category.assoc, hcomm a]
    rw [← Category.assoc, hpt e, hpt (ρ a e), hM a e, Over.comp_left]
    simp only [Category.assoc]
  · rw [Over.w, Over.w]

end GlobalTheory.CompanionTheory.Ar.LieBaseAct
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieJ

noncomputable def epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω')
    (h : y = Spec.map (CommRingCat.ofHom i) ≫ x) : epsAt y ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap i))) (by
    subst h
    have hr : (dualMap i).comp (algebraMap Ω (DualNumber Ω)) = (algebraMap Ω' (DualNumber Ω')).comp i := by
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    show Spec.map (CommRingCat.ofHom (dualMap i)) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap Ω' (DualNumber Ω'))) ≫ Spec.map (CommRingCat.ofHom i) ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, hr])

theorem isTanAt_epsOver {X : Scheme.{0}} {Ω Ω' : Type} [CommRing Ω] [CommRing Ω'] (G : Over X) [GrpObj G]
    (x : Sp Ω ⟶ X) (y : Sp Ω' ⟶ X) (i : Ω →+* Ω') (h : y = Spec.map (CommRingCat.ofHom i) ≫ x)
    (v : epsAt x ⟶ G) (hv : IsTanAt G x v) : IsTanAt G y (epsOver x y i h ≫ v) := by
  have hr : (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom.comp (dualMap i) = i.comp (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom := by
    refine RingHom.ext fun a => ?_
    simp [dualMap]
  have hone : (Over.homMk (Spec.map (CommRingCat.ofHom i)) h.symm : Over.mk y ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ G) = 1 := by
    exact MonObj.comp_one _
  have h1 := congrArg (fun w => w.left) hone
  show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω' Ω' Ω').toRingHom) ≫ Spec.map (CommRingCat.ofHom (dualMap i)) ≫ v.left = _
  rw [← h1, Over.comp_left, ← hv, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hr, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  rfl

theorem exists_map : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω' V'] (M : LieModel G ξ V) (M' : LieModel G' ξ' V'), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → ∃ j : V →+ V', ∀ e, (M'.pt (j e)).left ≫ φ = Spec.map (CommRingCat.ofHom (dualMap i)) ≫ (M.pt e).left := by
  intro X X' Ω Ω' _ _ ξ ξ' f i G G' _ _ φ V V' _ _ _ _ M M' hd hp
  obtain ⟨N, hN⟩ := (LiePull.lieModel_pullback X X' G G' f φ hp Ω' ξ' V').2 M'
  have ex : ∀ e, ∃ t, N.pt t = epsOver ξ (ξ' ≫ f) i hd ≫ M.pt e :=
    fun e => N.onto _ (isTanAt_epsOver G ξ (ξ' ≫ f) i hd _ (M.tan e))
  choose g hg using ex
  refine ⟨AddMonoidHom.mk' g fun a b => N.inj ?_, fun e => ?_⟩
  · rw [N.add, hg, hg, hg, M.add, comp_mul]
  · show (M'.pt (g e)).left ≫ φ = _
    rw [hN, hg]
    rfl

end GlobalTheory.CompanionTheory.Ar.LieJ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianAdicTorsionFour
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) :=
  @PositivityTheory.HtPt.Twfunct.tw_funct

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TwistOk

theorem twOK_obj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a :=
  @PositivityTheory.UnitarySelfGeneration.tw_ok

end GlobalTheory.CompanionTheory.Ar.TwistOk
end

