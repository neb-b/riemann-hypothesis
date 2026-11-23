module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodMatrixAtLogZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedModificationAtE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComparisonMatrixPrismCoproduct
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem map_toDisc_eq_of_dvd {l : ℕ} {A : Type} [CommRing A] (u : A) (r : ℝ≥0) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε)
    (h : ∀ j : n × n, ((l : ℕ) : A) ^ k ∣ x j.1 j.2) : ∃ y : Matrix n n A, y.map (toDisc l u r) = ε := by
  choose y hy using h
  refine ⟨Matrix.of fun i j => y (i, j), ?_⟩
  ext i j
  have e := congrFun (congrFun hx i) j
  have e2 : x i j = _ := hy (i, j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, e2, map_mul, map_pow, map_natCast] at e
  exact ((isUnit_l_disc l _ _).pow k).mul_left_cancel e

theorem IsDiscMap.map_eq_smul {l : ℕ} {A A' : Type} [CommRing A] [CommRing A'] {u : A} {u' : A'} {r r' : ℝ≥0}
    {f : A →+* A'} {F : Disc l u r →+* Disc l u' r'} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) {n : Type} (k : ℕ)
    (x : Matrix n n A) (ε : Matrix n n (Disc l u r)) (hx : x.map (toDisc l u r) = ((l : ℕ) : Disc l u r) ^ k • ε) :
    (x.map f).map (toDisc l u' r') = ((l : ℕ) : Disc l u' r') ^ k • ε.map F := by
  ext i j
  have e := congrArg F (congrFun (congrFun hx i) j)
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast] at e ⊢
  rw [← e, hF.ext]

theorem map_mul_map_eq_smul_one {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (A A' : Matrix (Fin d) (Fin d) R) (e : R) (b : ℕ) (h : A * A' = e ^ b • (1 : Matrix (Fin d) (Fin d) R)) :
    A.map f * A'.map f = f e ^ b • (1 : Matrix (Fin d) (Fin d) S) := by
  rw [← Matrix.map_mul, h]
  ext i j
  simp [Matrix.one_apply, apply_ite f]

theorem Height.dvd_at_section (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (B : Obj l ↥(OL K)) (f f' : Hom bk.prism B)
    (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f X) bk.ρ₀)) (hε : ht.Rel (BK.hf f X) f f' ε) (k : ℕ)
    (x : Matrix (Fin d) (Fin d) B.A)
    (hx : x.map (toDisc l (BK.hf f X) bk.ρ₀) = ((l : ℕ) : Disc l (BK.hf f X) bk.ρ₀) ^ k • ε)
    (g : ↥(GK K)) (σ : Hom B (ainfObj K)) (h1 : σ.comp f = bk.ι) (h2 : σ.comp f' = (ainfHom K g).comp bk.ι)
    (j : Fin d × Fin d) : ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j.1 j.2) := by
  obtain ⟨⟨F, hF⟩, hrel⟩ := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht B (ainfObj K) f f f' bk.ι σ ε hε
  have hr := hrel F hF
  rw [h1, h2] at hr
  exact GlobalTheory.T.pow_dvd_galoisComparison_matrix l K bk d ρ τ s ht hτ hρ g (ε.map F) hr k (x.map σ.f) (hF.map_eq_smul k x ε hx) j.1 j.2

theorem matrix_phi_eq_entries {R : Type} [CommRing R] (φ : R →+* R) (e e' : R) (he : Associated e e') (d a b : ℕ)
    (P Q Q' : Matrix (Fin d) (Fin d) R) (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R))
    (x : Matrix (Fin d) (Fin d) R) (hx : e' ^ a • (P * x.map φ) = e ^ a • (x * Q)) :
    ∃ (h : ℕ) (c : Fin d × Fin d → Fin d × Fin d → R),
      ∀ j : Fin d × Fin d, e ^ h * x j.1 j.2 = ∑ i : Fin d × Fin d, φ (x i.1 i.2) * c i j :=
  _root_.GlobalTheory.BSP.matrix_phi_eq_family R R (RingHom.id R) φ e e' he d d a a b P Q Q' hQ x hx

theorem Height.exists_rel_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (hτ : bk.IsPer τ) (hρ : ∀ g, IsUnit (ρ g)) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) :
    ∃ ε : Matrix (Fin d) (Fin d) En.Q.A,
      ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) := by
  have tb : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have h₁ := _root_.GlobalTheory.BSP.Height.rel_exists l K bk d ρ τ s ht En.Q (BK.hf En.inl X) En.inl En.inr
  obtain ⟨εD, hεD⟩ := h₁
  have h₂ := _root_.GlobalTheory.BSP.comparisonMatrix_bounded l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb εD hεD
  obtain ⟨k, x, hx⟩ := h₂
  have hφ := _root_.GlobalTheory.BSP.Height.phi_eq_of_rel_pow l K bk d ρ τ s ht hτ En.Q En.inl En.inr _ tb k x εD hεD hx
  have h₃ := matrix_phi_eq_entries En.Q.D.φ (BK.hf En.inl bk.E) (BK.hf En.inr bk.E)
    (_root_.GlobalTheory.BSP.hf_E_pair l K bk En.Q En.inl En.inr).2.1 d (ht.a + s.N) ht.b (ht.A.map (BK.hf En.inl))
    (ht.A.map (BK.hf En.inr)) (ht.A'.map (BK.hf En.inr))
    (map_mul_map_eq_smul_one (BK.hf En.inr) _ _ _ _ ht.A_mul) x hφ
  obtain ⟨h, c, hc⟩ := h₃
  have hdiv := _root_.GlobalTheory.envelope_dvd_lpow_of_sections l K bk En (Fin d × Fin d) c h k (fun j => x j.1 j.2) hc
    (Height.dvd_at_section l K bk d ρ τ s ht hτ hρ En.Q En.inl En.inr εD hεD k x hx)
  have h₄ := map_toDisc_eq_of_dvd (BK.hf En.inl X) bk.ρ₀ k x εD hx hdiv
  obtain ⟨y, hy⟩ := h₄
  subst hy
  exact ⟨y, hεD⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqSumBallFn
section
noncomputable section

open ValuativeRel OnePoint

namespace GlobalTheory.LocGL.ProjLine

variable {k : Type} [Field k] [ValuativeRel k]

def Stable (S : Submodule ℂ (OnePoint k → ℂ)) : Prop :=
  (∀ F ∈ S, ∀ a b : k, a ≠ 0 → ∀ F' : OnePoint k → ℂ, F' ∞ = F ∞ →
    (∀ x : k, F' x = F ((a * x + b : k) : OnePoint k)) → F' ∈ S) ∧
  ∀ F ∈ S, ∀ F' : OnePoint k → ℂ, F' ∞ = F ((0 : k) : OnePoint k) → F' ((0 : k) : OnePoint k) = F ∞ →
    (∀ x : k, x ≠ 0 → F' x = F ((x⁻¹ : k) : OnePoint k)) → F' ∈ S


open Classical in
def ballFn (a r : k) : OnePoint k → ℂ := fun x =>
  x.elim 0 fun y => if valuation k (y - a) ≤ valuation k r then 1 else 0


open Classical in
theorem ballFn_coe (a r x : k) :
    ballFn a r x = if valuation k (x - a) ≤ valuation k r then 1 else 0 := rfl

theorem Stable.ballFn_mem {S : Submodule ℂ (OnePoint k → ℂ)} (hS : Stable S) {a r : k} (hr : r ≠ 0)
    (h : ballFn a r ∈ S) (b : k) {s : k} (hs : s ≠ 0) : ballFn b s ∈ S := by
  refine hS.1 _ h (r / s) (a - r / s * b) (div_ne_zero hr hs) _ rfl fun x => ?_
  have h1 : r / s * x + (a - r / s * b) - a = r * ((x - b) / s) := by field_simp; ring
  have h2 : valuation k r ≠ 0 := by simpa using hr
  have h3 : 0 < valuation k s := zero_lt_iff.2 (by simpa using hs)
  rw [ballFn_coe, ballFn_coe, h1, map_mul, map_div₀]
  congr 1
  rw [mul_le_iff_le_one_right (zero_lt_iff.2 h2), div_le_one₀ h3]

def vball (r : k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ valuation k r}
  add_mem' {a b} hx hy := show valuation k (a + b) ≤ valuation k r from (valuation k).map_add_le hx hy
  zero_mem' := by simp
  neg_mem' hx := by simpa using hx

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_vball {r : k} (hr : r ≠ 0) : IsOpen (vball r : Set k) := by
  have ho : IsOpen (𝒪[k] : Set k) := Valuation.isOpen_integer
  have h3 : 0 < valuation k r := zero_lt_iff.2 (by simpa using hr)
  convert ho.preimage (continuous_id.div_const r) using 1
  ext x
  show valuation k x ≤ valuation k r ↔ valuation k (x / r) ≤ 1
  rw [map_div₀, div_le_one₀ h3]

theorem exists_vball_subset {U : Set k} (hU : U ∈ nhds (0 : k)) :
    ∃ r : k, r ≠ 0 ∧ ∀ x, valuation k x ≤ valuation k r → x ∈ U := by
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff U).1 hU
  obtain ⟨s, hs⟩ := valuation_surjective (γ : ValueGroupWithZero k)
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h0 : s ≠ 0 := by rintro rfl; exact γ.ne_zero (by simpa using hs.symm)
  refine ⟨ϖ * s, mul_ne_zero ϖ.ne_zero h0, fun x hx => hγ (hx.trans_lt ?_)⟩
  rw [map_mul, hs, hϖ]
  exact mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one

theorem exists_eq_sum_ballFn {r R : k} (hr : r ≠ 0) (hle : valuation k r ≤ valuation k R) :
    ∃ T : Finset k, (∀ a ∈ T, valuation k a ≤ valuation k R) ∧
      (valuation k r < valuation k R → 1 < T.card) ∧
      ∀ F : OnePoint k → ℂ, F ∞ = 0 → (∀ x : k, valuation k R < valuation k x → F x = 0) →
        (∀ x b : k, valuation k b ≤ valuation k r → F ((x + b : k) : OnePoint k) = F x) →
        F = ∑ a ∈ T, F a • ballFn a r := by
  classical
  let A : AddSubgroup k := vball R
  let B : AddSubgroup k := vball r
  have hA : IsCompact (A : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k R)
  have hB : IsOpen (B : Set k) := isOpen_vball hr
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  haveI := (B.addSubgroupOf A).quotient_finite_of_isOpen (hB.preimage continuous_subtype_val)
  haveI := Fintype.ofFinite (A ⧸ B.addSubgroupOf A)
  let o : A ⧸ B.addSubgroupOf A → k := fun q => q.out
  have ho : Function.Injective o := fun p q h => Quotient.out_injective (Subtype.ext h)
  have key : ∀ (q : A ⧸ B.addSubgroupOf A) (x : A), valuation k (x - o q) ≤ valuation k r ↔ q = x := fun q x => by
    conv_rhs => rw [← q.out_eq']
    rw [QuotientAddGroup.eq, sub_eq_neg_add]
    rfl
  refine ⟨Finset.univ.image o, fun a ha => ?_, fun h => ?_, fun F h0 h1 h2 => funext fun x => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact q.out.2
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ, Fintype.one_lt_card_iff]
    refine ⟨(0 : A), (⟨R, show valuation k R ≤ valuation k R from le_rfl⟩ : A), fun e => h.not_ge ?_⟩
    have h5 := QuotientAddGroup.eq.1 e
    have h4 : -(0 : k) + R ∈ B := h5
    rwa [neg_zero, zero_add] at h4
  · rw [Finset.sum_image ho.injOn, Finset.sum_apply]
    induction x using OnePoint.rec with
    | infty => simp [ballFn, h0]
    | coe x =>
      by_cases hx : valuation k x ≤ valuation k R
      · simp only [Pi.smul_apply, ballFn_coe, key _ ⟨x, hx⟩, smul_eq_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        exact (congrArg F (by simp)).trans (h2 _ _ ((key _ ⟨x, hx⟩).2 rfl))
      · rw [h1 x (not_le.1 hx), Finset.sum_eq_zero]
        intro q _
        rw [Pi.smul_apply, ballFn_coe, if_neg, smul_zero]
        intro h
        have h3 : x - o q + o q ∈ A := A.add_mem (h.trans hle) q.out.2
        rw [sub_add_cancel] at h3
        exact hx h3

end GlobalTheory.LocGL.ProjLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPairingDstDcrisFrobeniusFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem onB_mulLeft_mem_Dst_of_fixed {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V)
    (a : Bst P) (ha : ∀ g : ↥(GK K), actSt P (g : GQ l) a = a) (x : V ⊗[ℚ_[l]] Bst P)
    (hx : x ∈ Dst P ρ) : onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x ∈ Dst P ρ := by
  rw [mem_Dst] at hx ⊢
  intro g
  have h : stRep P ρ g * onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) =
      onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) * stRep P ρ g :=
    end_ext P fun v b => by
      simp only [End.mul_apply, onB_tmul, stRep_tmul, LinearMap.mulLeft_apply, map_mul, ha]
  rw [← End.mul_apply, h, End.mul_apply, hx]

theorem exists_pairing_Dst_Dcris_phi_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → ∃ B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) →ₗ[ℚ_[l]] ℚ_[l], (∀ x ∈ Dst P ρ, ∀ w, B (monV P ℚ_[l] V x) w = 0) ∧ (∀ x ∈ Dst P ρ, ∀ w, B ((l : ℚ_[l]) • phiV P ℚ_[l] V x) w = B x w) ∧ ∀ w, (∀ x ∈ Dst P ρ, B x w = 0) → w = 0 := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hd hs
  obtain ⟨pr, hφ, hN, hg, hmul, hnd⟩ := _root_.GlobalTheory.PMon.StPairing.exists_stPairing l P K V V' ρ ρ' m hd
  obtain ⟨lam, hlφ, hlnd⟩ := _root_.GlobalTheory.PMon.exists_phiSt_invariant_nondegenerate_linearForm l P K
  let W := Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)
  let j : ↥W →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P := (crisIncl P ℚ_[l] V') ∘ₗ W.subtype
  have hj : ∀ w : ↥W, j w = crisIncl P ℚ_[l] V' (w : V' ⊗[ℚ_[l]] P.R.B) := fun _ => rfl
  have hjg : ∀ (w : ↥W) g, stRep P ρ' g (j w) = j w := by
    intro w g
    have h1 := w.2.1
    have h2 : actVB (P.PD K) ρ' g (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := (Submodule.mem_iInf _).mp h1 g
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [hj, stRep_crisIncl, h2]
  have hjN : ∀ w : ↥W, monV P ℚ_[l] V' (j w) = 0 := fun w =>
    (_root_.GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl l P V' _).mpr ⟨_, (hj w).symm⟩
  have hjφ : ∀ w : ↥W, phiV P ℚ_[l] V' (j w) = j w := by
    intro w
    have h2 : φVB (P.PD K) (LL := ℚ_[l]) (V := V') (w : V' ⊗[ℚ_[l]] P.R.B) = w := by
      have := w.2.2
      rwa [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero] at this
    rw [hj, GlobalTheory.T.frobeniusTensor_crisToSemistable_comm l P K, h2]
  have hinv : ∀ x ∈ Dst P ρ, ∀ w : ↥W, ∃ c : ↥(K0 K), Polynomial.C P.tB * pr x (j w) =
      Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := by
    intro x hx w
    refine (_root_.GlobalTheory.PMon.stInv_iff l P AI T K _).mp fun g => ?_
    have h1 := hg g x (j w)
    rw [(mem_Dst P ρ).mp hx g, hjg] at h1
    rw [map_mul, actSt_C, localPrime_galoisAction_periodT, ← Polynomial.smul_C, smul_mul_assoc, ← mul_smul_comm, ← h1]
  let B : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] ↥W →ₗ[ℚ_[l]] ℚ_[l] :=
    (pr.compl₂ j).compr₂ (lam ∘ₗ LinearMap.mulLeft ℚ_[l] (Polynomial.C P.tB))
  have hB : ∀ x w, B x w = lam (Polynomial.C P.tB * pr x (j w)) := fun _ _ => rfl
  refine ⟨B, fun x hx w => ?_, fun x hx w => ?_, fun w hw => ?_⟩
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hN x (j w)
    rw [hjN, map_zero, add_zero] at h1
    rw [hB, h1, ← monSt_C_mul, hc, (monSt_eq_zero_iff P _).mpr ⟨_, rfl⟩, map_zero]
  · obtain ⟨c, hc⟩ := hinv x hx w
    have h1 := hφ x (j w)
    rw [hjφ] at h1
    rw [hB, hB, map_smul, LinearMap.smul_apply, h1, mul_smul_comm, ← smul_mul_assoc,
      Polynomial.smul_C, ← localPrime_frobenius_periodT, ← phiSt_C, ← map_mul, hc, hlφ]
  · have h0 : ∀ x ∈ Dst P ρ, pr x (j w) = 0 := by
      intro x hx
      obtain ⟨c, hc⟩ := hinv x hx w
      have hc0 : c = 0 := by
        refine hlnd c fun c' => ?_
        have h2 := hw _ (onB_mulLeft_mem_Dst_of_fixed P ρ _
          ((_root_.GlobalTheory.PMon.stInv_iff l P AI T K _).mpr ⟨c', rfl⟩) x hx)
        rw [hB, hmul, mul_left_comm, hc] at h2
        exact h2
      rw [hc0, map_zero, map_zero] at hc
      exact ((isUnit_tB P).map Polynomial.C).mul_right_eq_zero.mp hc
    have h1 : j w = 0 := by
      refine hnd _ fun v => ?_
      obtain ⟨k, a, x, hx, hv⟩ := _root_.GlobalTheory.Pst.Dst_spans_tensor_Bst l P AI T K V ρ hs v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hmul, h0 _ (hx i), mul_zero]
    apply Subtype.ext
    apply crisIncl_injective P (LL := ℚ_[l])
    rw [← hj, h1]
    simp

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

theorem sst_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hC d ρ hsst
  have hdr := GlobalTheory.sst_isDR l P AI T K _ (qRep ρ) hsst
  obtain ⟨H, -⟩ := GlobalTheory.T.exists_hodge_basis_deRham_lattice l K P AI T C hC (bk.ev bk.E) bk.span_ev d ρ hdr
  obtain ⟨b, c, hb, hfix, hlog⟩ := GlobalTheory.T.exists_log_teichmuller_pow_semistablePeriods l K bk P AI T C hC trivial
  obtain ⟨U, U', c₁, c₃, k, F, F', Mn, hUU', hFF', hφ, hMn, hgal⟩ := _root_.GlobalTheory.StU.period_matrix_at_zero l K bk P AI T C hC d ρ b c hb hsst
  obtain ⟨-, hInvdR⟩ := GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨lam, hlamg, hlamA⟩ := GlobalTheory.T.exists_log_uniformizerTilt_bdRPlus_cocycle l K bk P AI T C hC b c hb hfix hlog
  obtain ⟨Λ₀, hΛ₀g, hΛ₀A⟩ := GlobalTheory.T.semistable_invariant_bdRPlus_basis_approx l K bk P AI T C hC d (fun g => (ρ g).val) U k Mn c hMn hgal lam hlamg hlamA
  obtain ⟨e, m, hm, hdf⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero d) l (Fact.out : l.Prime).ne_one
  have hk₀ : ∀ i < d, ‖GlobalTheory.SstPer.ecoefQ l (e + k * d) k i‖ ≤ 1 := fun i hi => GlobalTheory.SstPer.ecoefQ_norm_le k hm hdf hi
  obtain ⟨N₀, hZ⟩ := GlobalTheory.T.semistable_periods_over_Acris l K bk P AI T C hC d (fun g => (ρ g).val) U U' hUU' c₁ F hφ k (e + k * d) Mn c hk₀ hgal
  have hUUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨N, c₂, X, X', hN, hXX', hX, hX'⟩ := _root_.GlobalTheory.BKTwist.exists_twisted_modification l K bk C hInvdR d (fun g => (ρ g).val) H (U.map C.ι) (U'.map C.ι) Λ₀ hUUι hΛ₀g hΛ₀A N₀
  obtain ⟨Z, Z', hZZ', hZφ, hZg, hZX, hZX'⟩ := hZ N hN X X' hX hX'
  refine ⟨N, c₁, c₂, c₃, e + k * d, F, F', X, X', Z, Z', fun g => GlobalTheory.SstPer.kap C bk (e + k * d) k Mn (c g), hFF', hXX', hZZ', hZφ, hZg, ?_, hZX, hZX', GlobalTheory.T.semistable_exp_cocycle_coboundary_mod_fil l K bk P AI T C hC d k (e + k * d) Mn c hk₀ hMn hlog⟩
  intro g hg
  simp only
  rw [hfix g hg]
  exact GlobalTheory.SstPer.kap_zero C bk _ k Mn

end GlobalTheory.SstPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankBlochKatoGAddELeFAddF
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

namespace GlobalTheory.HyodoDef.Count

theorem finrank_blochKato_g_add_e_le_f_add_f_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [ContinuousAdd V'] [ContinuousConstSMul ℚ_[l] V'] (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), (∀ v, Continuous fun g => ρ g v) → (∀ y, Continuous fun g => ρ' g y) → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' → IsDual1 (P.PD K) ρ ρ' m → finrank ℚ_[l] ↥(geometricCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ') ≤ finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ') := by
  intro l _ P AI hT K V _ _ _ _ _ _ _ ρ V' _ _ _ _ _ _ _ ρ' m hc hc' hdR hdR' hdual
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module ℤ_[l] V' := Module.compHom V' (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hO := GlobalTheory.Published.BlochKato.goodO_padicInt (l := l)
  have hTD := CompanionTheory.LocalTateOrthogonality.Gcoh.top_tate
  have hEC := CompanionTheory.LocalTateOrthogonality.Gcoh.top_euler
  let A : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V, ρ := ρ, cont := hc }
  let A' : GRep ↥(GK K) ℚ_[l] ℚ_[l] ℤ_[l] := { V := V', ρ := ρ', cont := hc' }
  have hdual' : IsDual1 (P.PD K) ρ' ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  obtain ⟨hfin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K ℚ_[l] ℤ_[l] hO A' A m.flip hdual'
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ) := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A hfin
  haveI : FiniteDimensional ℚ_[l] (continuousCocycles ρ') := GlobalTheory.BlochKatoAnn.finite_continuous_cocycles_localGaloisRep A' hfin'
  obtain ⟨β, hβ, -, hr⟩ : ∃ β : ↥(continuousCocycles ρ) →ₗ[ℚ_[l]] ↥(continuousCocycles ρ') →ₗ[ℚ_[l]] ℚ_[l],
      (∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL ρ' m a.1 b.1)) ∧
      (∀ a, (∀ b, β a b = 0) ↔ a.1 ∈ B1 ρ) ∧ ∀ b, (∀ a, β a b = 0) ↔ b.1 ∈ B1 ρ' :=
    GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K ℚ_[l] ℤ_[l] hO A A' m hdual
  have hann : ∀ a ∈ continuousCocycles ρ, (a ∈ finiteCocycles (P.PD K) ρ ↔
      ∀ b ∈ finiteCocycles (P.PD K) ρ', CobL (P.PD K) (cupL ρ' m a b)) :=
    (_root_.GlobalTheory.BlochKatoAnn.bkA_exact_annihilators hTD hEC l P AI hT K ℚ_[l] ℤ_[l] hO A A' m hdR hdual).1
  have horth := _root_.GlobalTheory.HyodoOrth.hyodo_orth l P AI hT K V ρ V' ρ' m hc hc' hdR' hdual
  have hg : geometricCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have he : crystallineCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hf : finiteCocycles (P.PD K) ρ ≤ continuousCocycles ρ := fun _ h => h.1
  have hf' : finiteCocycles (P.PD K) ρ' ≤ continuousCocycles ρ' := fun _ h => h.1
  have hBf : B1 ρ' ≤ finiteCocycles (P.PD K) ρ' := GlobalTheory.BlochKatoAnn.B1_le_Z1f (P.PD K) A'
  have hBe : B1 ρ' ≤ crystallineCocycles (P.PD K) ρ' := by
    intro c hcB
    refine ⟨hf' (hBf hcB), ?_⟩
    obtain ⟨x, rfl⟩ := hcB
    refine ⟨x ⊗ₜ[ℚ_[l]] 1, ?_, fun g => ?_⟩
    · simp [φVB]
    · simp [cob, actVB, sub_tmul]
  have key := GlobalTheory.HyodoDef.PairLin.finrank_add_le β
    ((geometricCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype) ((finiteCocycles (P.PD K) ρ).comap (continuousCocycles ρ).subtype)
    ((crystallineCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype) ((finiteCocycles (P.PD K) ρ').comap (continuousCocycles ρ').subtype)
    (fun b hb => ⟨hBe ((hr b).1 hb), hBf ((hr b).1 hb)⟩)
    (fun a ha b hb => (hβ a b).2 (horth a.1 ha b.1 hb))
    (fun a => by
      rw [Submodule.mem_comap, Submodule.subtype_apply, hann a.1 a.2]
      constructor
      · intro h b hb
        exact (hβ a b).2 (h b.1 hb)
      · intro h b hb
        exact (hβ a ⟨b, hf' hb⟩).1 (h ⟨b, hf' hb⟩ hb))
  rwa [(Submodule.comapSubtypeEquivOfLe hg).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe he).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf).finrank_eq,
    (Submodule.comapSubtypeEquivOfLe hf').finrank_eq] at key

end GlobalTheory.HyodoDef.Count
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratedLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.H1fGeneration


set_option maxHeartbeats 1000000 in
theorem h1fGen_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) [Fintype (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)] (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) [IsTopologicalAddGroup T.V], FiniteCohomologyGeneratorsBound (P.PD K) T.L := by
  intro l _ P AI hT K LL _ T _ hG hC hcont
  have hO := (GlobalTheory.LocalIntegers.good_integers l LL).1
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T.V T.ρ hC).1
  obtain ⟨s, hs, hcard⟩ := GlobalTheory.T.h1fT_span_card_bound l P AI hT K (↥LL.1) (↥(OL LL)) hO T hDR
  have hBK := _root_.GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l P AI hT K LL hG.1 T.V T.ρ hcont hC
  refine ⟨s, hs, ?_⟩
  have h0 : (0 : ℤ) ≤ (finrank ↥LL.1 ↥(H0V T.ρ) : ℤ) := by positivity
  set_option synthInstance.maxHeartbeats 200000 in
    have hc : ((s.card + finrank ↥LL.1 ↥(H0V T.ρ) : ℕ) : ℤ) ≤ ((finrank ↥LL.1 (FiniteCohomology (P.PD K) T.ρ) + finrank ↥LL.1 T.V : ℕ) : ℤ) := by
      exact_mod_cast hcard
    push_cast at hc
    linarith

end GlobalTheory.H1fGeneration
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolicStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.MirTower
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_series_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.lintegral_theta_unfold | exact GlobalTheory.ThetaUnfold.lintegral_theta_unfold | (intros; apply GlobalTheory.ThetaUnfold.lintegral_theta_unfold <;> assumption)
end

