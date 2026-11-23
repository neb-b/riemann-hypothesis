module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsThetaPForms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace Topology ComplexOrder
open GlobalTheory.GalLift

namespace GlobalTheory.ConjThetaIntegral

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem conjVal_one {D : D7} {σ : D.what₂.LL →+* ℂ} {a b : ℂ} (h : ConjVal σ a b) (ha : a = 1) : b = 1 := by
  obtain ⟨y, h1, h2⟩ := h
  have : y = 1 := D.what₂.embLL.injective (by rw [h1, ha, map_one])
  rw [← h2, this, map_one]

theorem ext_continuous {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (χ' : (levEnv V β L).J →* ℂˣ) (hχ : ∀ k, (levEnv V β L).χ k = 1 → χ' k = 1)
    {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J χ') : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact GlobalTheory.ThetaIntegrand.form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1
    ((GlobalTheory.ThetaIntegrand.eventually_level V β L).mono fun _ h => h.elim fun hk h1 => ⟨hk, hχ _ h1⟩) hf

theorem IsThetaP₂ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    (χ' : (levEnv S β L).J →* ℂˣ) (hχ : ∀ k, (levEnv S β L).χ k = 1 → χ' k = 1)
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] (Bridge.Gf S → c.W))
    (he : ∀ x, e x ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J χ')
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (io : TK →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) :
    ∃ thP, Lift.IsThetaP μ 𝓕 (fun g h φ => thetaKO om h g φ) (fun P => pt P) io (LinearMap.range (c.ext ∘ₗ e)) thP := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  refine GlobalTheory.ThetaIntegralLinear.exists_isThetaP_of_integrable μ 𝓕
    (fun g h => LinearMap.proj (R := ℂ) (φ := fun _ : WO S T => ℂ) 0 ∘ₗ om (h, g)) pt io _ ?_
  rintro ⟨_, x, rfl⟩ v g
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io v)
    (fun w => hpt _) _ (ext_continuous c hc β L χ' hχ (he x)) (GlobalTheory.ThetaIntegrand.ext_invariant c (he x)) μ 𝓕 hμ.1.1 hμ.2 g

end GlobalTheory.ConjThetaIntegral

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLatti
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.TraceCorrection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have h : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_symm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (form σ J x y) = form σ J y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  intro F E _ _ _ _ _ σ hσ n J L hJ hL θ hθ x y₀ hxx hy₀x hL0
  have hsa : σ (form σ J y₀ y₀) = form σ J y₀ y₀ := form_symm σ J hσ hJ y₀ y₀
  have hxw : ∀ w, form σ J x w = σ (form σ J w x) := fun w => (form_symm σ J hσ hJ w x).symm
  have hxy₀ : form σ J x y₀ = 1 := by rw [hxw, hy₀x, map_one]
  have hsθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  have hθi : IsIntegral ℤ (θ : E) := θ.isIntegral_coe
  have hA : ∀ z ∈ L, ∀ w ∈ L,
      IsIntegral ℤ (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
    intro z hz w hw
    have h := (hL _).1 (hL0 z hz) _ (hL0 w hw)
    rw [form_smul_left, form_smul_right] at h
    have k : form σ J z x * (σ (form σ J w x) * form σ J y₀ y₀) =
        form σ J y₀ y₀ * form σ J z x * σ (form σ J w x) := by ring
    rw [← k]; exact h
  refine ⟨y₀ + (-((θ : E) * form σ J y₀ y₀)) • x, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hxy₀, hy₀x,
      map_neg, map_mul, hsθ, hsa]
    ring
  · simp only [form_add_right, form_smul_right, hxx, hxy₀]
    ring
  intro z hz
  constructor
  · have e : form σ J z (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) • x =
        form σ J z y₀ • x + (σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x) • x := by
      rw [form_add_right, form_smul_right, add_smul]
    rw [e]
    refine L.add_mem ((hL _).2 fun w hw => ?_) ((hL _).2 fun w hw => ?_)
    · have h := (hL z).1 hz _ (hL0 w hw)
      rw [form_smul_right] at h
      rw [form_smul_left, hxw, mul_comm]
      exact h
    · rw [form_smul_left, hxw]
      have h := (hA z hz w hw).neg.add (hθi.mul (hA z hz w hw))
      have k : σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x * σ (form σ J w x) =
          -(form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) +
            (θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
        rw [map_neg, map_mul, hsθ, hsa]; ring
      rw [k]; exact h
  · have e : form σ J z x • (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) =
        form σ J z x • y₀ + (form σ J z x * (-((θ : E) * form σ J y₀ y₀))) • x := by
      rw [smul_add, mul_smul]
    rw [e]
    refine L.add_mem (hL0 z hz) ((hL _).2 fun w hw => ?_)
    rw [form_smul_left, hxw]
    have h := (hθi.mul (hA z hz w hw)).neg
    have k : form σ J z x * (-((θ : E) * form σ J y₀ y₀)) * σ (form σ J w x) =
        -((θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x))) := by ring
    rw [k]; exact h

end GlobalTheory.TraceCorrection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefin
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelActionCuspFormRepresentationStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_action_cusp_form_representation : ∀ {D : D7} {G : Type} [Group G] (T : CoreJ D) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (i : Fin D.R.m) (lev : G → ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) × ((T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La)), LawsJ T → ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c lev → (∀ g, ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, actLev T.Q.c lev g f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) → ∃ ρC : G →* (Cu T κ i →ₗ[T.Q.c.F] Cu T κ i), ∀ g (f : Cu T κ i), ((ρC g f : Cu T κ i) : T.R ((i : ℕ) + 1)) = actLev T.Q.c lev g (f : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.LevelRep.exists_cusp_rep | exact GlobalTheory.LevelRep.exists_cusp_rep | (intros; apply GlobalTheory.LevelRep.exists_cusp_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_place_datum_over_number_field : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_vP → ∀ (i : Fin D.R.m), VStd D i → ∀ (t : T0) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ M' : IntermediateField ℚ ℂ, M ≤ M' → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ J : Ideal (𝓞 D.host.E), (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) → ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M', PhiIs R i M'.val.toRingHom t ι (J • ⊤) φ := by
  first | exact @GlobalTheory.LevelDatum.exists_phi | exact GlobalTheory.LevelDatum.exists_phi | (intros; apply GlobalTheory.LevelDatum.exists_phi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

theorem glueL_evalT_inC (G : HTGroup p) (w : AwayP p) (c : G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (inC G (AfP p) c) =
      inC G (w.1.adicCompletion ℚ) c := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((1 : AfP p) ⊗ₜ c) = (1 : w.1.adicCompletion ℚ) ⊗ₜ c
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]

theorem glueL_evalT_starT (G : HTGroup p) (w : AwayP p) (a : AfP p ⊗[ℚ] G.C) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (starT G.star (AfP p) a).unop =
      (starT G.star (w.1.adicCompletion ℚ) (Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) a)).unop := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, starT_tmul]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem glueL_evalT_algebraMap (G : HTGroup p) (w : AwayP p) (t : AfP p) :
    Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) t) =
      algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (AfP.eval w t) := by
  simp [Algebra.TensorProduct.algebraMap_apply]

theorem glueL_compL_toAfF_fst (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (w : AwayP p) :
    ((((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
        w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
      Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) (x : AfP p ⊗[ℚ] G.C) *
        inC G (w.1.adicCompletion ℚ) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
        Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C) := by
  show Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C) ((x : AfP p ⊗[ℚ] G.C) *
    inC G (AfP p) (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) = _
  rw [map_mul, map_mul, glueL_evalT_inC]

theorem glueL_sh_inv_mul (G : HTGroup p) (c : G.Cˣ) : sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C) = 1 := by
  simp only [sh]
  rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]

theorem glueL_main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (y : grp G β) (g : G.GAf) (c Y : G.Cˣ),
    (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = c * Y * ((c⁻¹ : G.Cˣ) : G.C) → ∀ w : AwayP p,
    ∃ (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) (lam : (w.1.adicCompletion ℚ)ˣ),
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = ((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) = (((((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧
      (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * (inC G (w.1.adicCompletion ℚ) (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) *
        inC G (w.1.adicCompletion ℚ) (β : G.C)) * (starT G.star (w.1.adicCompletion ℚ) (k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))).unop = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (lam : w.1.adicCompletion ℚ) := by
  intro p _ G β x t hx y g c Y hy w
  let φ := Algebra.TensorProduct.map (AfP.eval w) (AlgHom.id ℚ G.C)
  let u : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1
  let ν : (w.1.adicCompletion ℚ)ˣ :=
    ((compL G w g : UPts G.star (w.1.adicCompletion ℚ)) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2
  let xw : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (φ : AfP p ⊗[ℚ] G.C →* w.1.adicCompletion ℚ ⊗[ℚ] G.C) x
  let ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom c
  let mY : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  let tw : (w.1.adicCompletion ℚ)ˣ := Units.map (AfP.eval w : AfP p →* w.1.adicCompletion ℚ) t
  have hT : ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = xw * (ci * mY * ci⁻¹) * xw⁻¹ := by
    apply Units.ext
    rw [glueL_compL_toAfF_fst]
    have hy' : ((y : G.Cˣ × ℚˣ).1 : G.Cˣ) = c * Y * c⁻¹ := Units.ext (by rw [hy]; rfl)
    rw [hy', ← map_inv, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have E : ((compL G w (g⁻¹ * toAfF G β x t hx y * g) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 = (u⁻¹ * xw * ci) * mY * (u⁻¹ * xw * ci)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    change u⁻¹ * ((compL G w (toAfF G β x t hx y) : UPts G.star (w.1.adicCompletion ℚ)) :
      (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 * u = _
    rw [hT]
    group
  refine ⟨u⁻¹ * xw * ci, tw * ν⁻¹, ?_, ?_, ?_⟩
  · rw [E]; rfl
  · rw [E, show (u⁻¹ * xw * ci * mY * (u⁻¹ * xw * ci)⁻¹)⁻¹ = (u⁻¹ * xw * ci) * mY⁻¹ * (u⁻¹ * xw * ci)⁻¹ by group]
    rfl
  · have hu : ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
        (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) ((ν⁻¹ : (w.1.adicCompletion ℚ)ˣ) : w.1.adicCompletion ℚ) :=
      ((compL G w g)⁻¹).2
    have hxw : φ (x : AfP p ⊗[ℚ] G.C) * inC G (w.1.adicCompletion ℚ) (β : G.C) *
        (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop =
        algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) := by
      have h := congrArg φ hx
      rw [map_mul, map_mul, glueL_evalT_inC, glueL_evalT_starT, glueL_evalT_algebraMap] at h
      exact h
    have hs : ∀ z : G.C, (starT G.star (w.1.adicCompletion ℚ) (inC G (w.1.adicCompletion ℚ) z)).unop =
        inC G (w.1.adicCompletion ℚ) (sh G z) := fun z => starT_tmul G.star _ 1 z
    have hC : (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
        sh G (c : G.C) = β := by
      calc (c : G.C) * (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β *
            sh G (c : G.C)
          = ((c : G.C) * ((c⁻¹ : G.Cˣ) : G.C)) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) *
              (((β⁻¹ : G.Cˣ) : G.C) * β) * sh G (c : G.C) := by simp only [mul_assoc]
        _ = β * (sh G ((c⁻¹ : G.Cˣ) : G.C) * sh G (c : G.C)) := by
            rw [Units.mul_inv, Units.inv_mul, one_mul, mul_one, mul_assoc]
        _ = β := by rw [glueL_sh_inv_mul, mul_one]
    have hk : (((u⁻¹ * xw * ci : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ)) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) =
        ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) * φ (x : AfP p ⊗[ℚ] G.C) *
          inC G (w.1.adicCompletion ℚ) (c : G.C) := rfl
    rw [hk, RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)), RingHom.map_mul (starT G.star (w.1.adicCompletion ℚ)),
      MulOpposite.unop_mul, MulOpposite.unop_mul, hs]
    calc _ = ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (φ (x : AfP p ⊗[ℚ] G.C) * (inC G (w.1.adicCompletion ℚ) ((c : G.C) *
            (((c⁻¹ : G.Cˣ) : G.C) * β * sh G ((c⁻¹ : G.Cˣ) : G.C) * ((β⁻¹ : G.Cˣ) : G.C)) * β * sh G (c : G.C))) *
          (starT G.star (w.1.adicCompletion ℚ) (φ (x : AfP p ⊗[ℚ] G.C))).unop) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop := by
          simp only [map_mul, mul_assoc]
      _ = algebraMap (w.1.adicCompletion ℚ) (w.1.adicCompletion ℚ ⊗[ℚ] G.C) (tw : w.1.adicCompletion ℚ) *
          (((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) *
          (starT G.star (w.1.adicCompletion ℚ) ((u⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C)).unop) := by
          rw [hC, hxw, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = _ := by rw [hu, ← map_mul, Units.val_mul]

end GlobalTheory.FinClsLoc
end
end

