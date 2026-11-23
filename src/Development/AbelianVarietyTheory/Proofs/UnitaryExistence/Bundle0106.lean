module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConjugateComponentAdelic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028
public import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AutConjTranslatesDetCharacterMarkings
section
namespace GlobalTheory.DetTranslate

section Adelic

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_int {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (G : Matrix (Fin n) (Fin n) (RA F E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), G *ᵥ z ∈ hat F (L : Set (Fin n → E))) :
    G.det ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  let k : Matrix (Fin n) (Fin n) (RA F E) := Q * G * P
  have hPk : P * k = G * P := by
    simp only [k, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : k.det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [k, Matrix.det_mul]
    linear_combination G.det * this
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hg _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  have hd := det_mem_adelicCompletionOfElementSet F cI (fun j => (cI j)⁻¹) k hk
  rw [← Finset.prod_mul_distrib, Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i), hkdet] at hd
  have e1 : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rwa [e1] at hd


omit [NumberField E] in
theorem int_mul_mem (I : Ideal (𝓞 E)) {x y : RA F E} (hx : x ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (hy : y ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))) :
    x * y ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  refine mul_mem_adelicCompletionOfElementSet_of_mul_mem F ?_ hx hy
  rintro _ ⟨a, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨a * b, I.mul_mem_left a hb, map_mul _ _ _⟩


omit [NumberField E] in
theorem exists_nsmul_of_mem (M : ℕ) {x : RA F E}
    (hx : x ∈ hat1 F (algebraMap (𝓞 E) E '' (Ideal.span {(M : 𝓞 E)} : Ideal (𝓞 E)))) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), x = M • w := by
  induction hx using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩ := hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.1 hb
    refine ⟨_, tmul_mem_adelicCompletion_of_integral F ha ⟨t, rfl⟩, ?_⟩
    rw [map_mul, map_natCast, ← nsmul_eq_mul, TensorProduct.tmul_smul]
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨u + w, add_mem hu hw, (smul_add _ _ _).symm⟩
  | neg x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨-u, neg_mem hu, (smul_neg _ _).symm⟩


omit [NumberField E] in
theorem quot_cong_one (c : E ≃ₐ[F] E) (M : ℕ) (I I' : Ideal (𝓞 E)) (hsup : I ⊔ I' = ⊤)
    (hmul : I * I' = Ideal.span {(M : 𝓞 E)}) (hc : ∀ b ∈ I, ∃ b' ∈ I', ((b' : 𝓞 E) : E) = c (b : E))
    (d₁ d₂ S : RA F E) (h₁ : d₁ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (h₂ : d₂ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)))
    (n₁ : d₁ * sg (FiniteAdeleRing (𝓞 F) F) c d₁ = 1) (n₂ : d₂ * sg (FiniteAdeleRing (𝓞 F) F) c d₂ = 1)
    (s₁ : d₁ * S - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))))
    (s₂ : d₂ * S - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E)))) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), d₁ * sg (FiniteAdeleRing (𝓞 F) F) c d₂ - 1 = M • w := by
  have hO : ∀ x ∈ Set.range (algebraMap (𝓞 E) E), c x ∈ Set.range (algebraMap (𝓞 E) E) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩
  have h₂' := galoisAut_mem_adelicCompletionOfElementSet F c hO h₂
  set s := sg (FiniteAdeleRing (𝓞 F) F) c with hs
  have he : d₁ * s d₂ ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)) :=
    mul_mem_adelicCompletionOfElementSet_of_mul_mem F (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) h₁ h₂'
  have hI : d₁ * s d₂ - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
    have := int_mul_mem F I h₂' (sub_mem (int_mul_mem F I h₂ s₁) (int_mul_mem F I h₁ s₂))
    convert this using 1
    linear_combination n₂
  have hI' : d₁ * s d₂ - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I' : Set (𝓞 E))) := by
    have h3 : s (d₁ * s d₂ - 1) ∈ hat1 F (algebraMap (𝓞 E) E '' (I' : Set (𝓞 E))) := by
      refine galoisAut_mem_adelicCompletionOfElementSet F c ?_ hI
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨b', hb', e⟩ := hc b hb
      exact ⟨b', hb', e⟩
    have n₃ := congrArg s n₂
    rw [map_mul, map_one] at n₃
    have := neg_mem (int_mul_mem F I' he h3)
    convert this using 1
    rw [map_sub, map_mul, map_one]
    linear_combination (s d₂ * s (s d₂)) * n₁ + n₃
  obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  have hβ : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) +
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b' : E) = 1 := by
    rw [← TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
    congr 1
    have := congrArg (fun x : 𝓞 E => (x : E)) hbb
    simpa using this
  apply exists_nsmul_of_mem F M
  rw [← hmul]
  have hK : ∀ x ∈ algebraMap (𝓞 E) E '' (I : Set (𝓞 E)), ∀ y ∈ algebraMap (𝓞 E) E '' (I' : Set (𝓞 E)),
      x * y ∈ algebraMap (𝓞 E) E '' ((I * I' : Ideal (𝓞 E)) : Set (𝓞 E)) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x * y, Ideal.mul_mem_mul hx hy, map_mul _ _ _⟩
  have t₁ := mul_mem_adelicCompletionOfElementSet_of_mul_mem F hK (one_tmul_mem_adelicCompletionOfElementSet F ⟨b, hb, rfl⟩) hI'
  have t₂ := mul_mem_adelicCompletionOfElementSet_of_mul_mem F hK hI (one_tmul_mem_adelicCompletionOfElementSet F ⟨b', hb', rfl⟩)
  convert add_mem t₁ t₂ using 1
  linear_combination (1 - d₁ * s d₂) * hβ

end Adelic

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem gLat_mul {D : D7} (V : HSp D) (u v : GA D V) :
    gLat V (u * v) = (finHom V u).1.mulVec '' gLat V v := by
  unfold gLat
  rw [Set.image_image, map_mul, Units.val_mul]
  exact Set.image_congr fun z _ => (Matrix.mulVec_mulVec _ _ _).symm

theorem gLat_one {D : D7} (V : HSp D) : gLat V 1 = latHat V := by
  unfold gLat
  rw [map_one, Units.val_one]
  exact (Set.image_congr fun z _ => Matrix.one_mulVec z).trans (Set.image_id' _)

theorem gLat_mul_inv {D : D7} (V : HSp D) {u v : GA D V} (hu : gLat V u = latHat V) (hv : gLat V v = latHat V) :
    gLat V (u * v⁻¹) = latHat V := by
  have h : gLat V v⁻¹ = latHat V := by
    have h1 := gLat_mul V v⁻¹ v
    rw [inv_mul_cancel, gLat_one, hv] at h1
    exact h1.symm
  rw [gLat_mul, h]
  exact hu

theorem det_int_of_gLat {D : D7} (V : HSp D) {u : GA D V} (hu : gLat V u = latHat V) :
    (finHom V u).1.det ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  obtain ⟨h1, -, h2, h3, -⟩ := latHat_eq_hat_and_gram D V
  refine det_mem_int D.host.F (latC V) _ h2 h3 fun z hz => ?_
  rw [← h1] at hz ⊢
  have : (finHom V u).1 *ᵥ z ∈ gLat V u := ⟨z, hz, rfl⟩
  rw [hu] at this
  exact this


set_option maxHeartbeats 1600000 in
theorem conj_translates_det : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → FixesCurve H τ 1 → ∀ π : Fin C.F.n → Fin C.F.n, ConjugationPermutesPeriods C.F τ π → ∀ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, (∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (l.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V (u))) = 1) → (∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V (γ))) = 1) → ∃ κ : ℂˣ, (∃ u : GA D V, κ = xi (Matrix.GeneralLinearGroup.det (finHom V (u)))) ∧ ∀ h γ k h' γ', C.Mark h k γ → C.Mark h' (π k) γ' → xi (Matrix.GeneralLinearGroup.det (finHom V (γ' * h'))) = κ * xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) := by
  intro D H Dw l Xo c σ V r C hC hpq τ hτ hfix π hπ xi hK hQ
  obtain ⟨Cv, io, hio, -⟩ := hfix
  obtain ⟨⟨s, hs⟩, -⟩ := _root_.GlobalTheory.CompRat.Acts.main D.host.E H Cv τ hτ io hio l.M (lt_of_lt_of_le (by norm_num) l.three_le)
  have step := _root_.GlobalTheory.ConjMark.marking_of_conjugate D H Dw l Xo c σ V r C hC hpq τ hτ Cv io s π hs hπ
  by_cases hex : ∃ h γ k h' γ', C.Mark h k γ ∧ C.Mark h' (π k) γ'
  · obtain ⟨h₀, γ₀, k₀, h₀', γ₀', m₀, m₀'⟩ := hex
    obtain ⟨-, -, u₀, hu₀, -, hd₀⟩ := step _ _ _ _ _ m₀ m₀'
    refine ⟨_, ⟨u₀⁻¹, rfl⟩, fun h γ k h' γ' m m' => ?_⟩
    obtain ⟨δ, hδ, u, hu, he, hd⟩ := step _ _ _ _ _ m m'
    have n₀ := (finHom_herm_det D V u₀).2.1
    have hq := quot_cong_one D.host.F (cF D) l.M l.Mb _ l.coprime l.prod
      (fun b hb => ⟨H.bar b, Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) hb, H.bar_eq b⟩)
      _ _ _ (det_int_of_gLat V hu) (det_int_of_gLat V hu₀) (finHom_herm_det D V u).2.1 n₀ hd hd₀
    have hinv : (((Matrix.GeneralLinearGroup.det (finHom V u₀))⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) = GlobalTheory.AdLat.sg (Af D.host.F) (cF D) (finHom V u₀).1.det :=
      Units.inv_eq_of_mul_eq_one_right n₀
    have h1 := hK (u * u₀⁻¹) (gLat_mul_inv V hu hu₀) (by
      rw [map_mul, map_inv, map_mul, map_inv, Units.val_mul, hinv]
      exact hq)
    have h2 := congrArg (fun g => xi (Matrix.GeneralLinearGroup.det g)) he
    have h3 := hQ δ hδ
    generalize finHom V (γ' * h') = A at h2 ⊢
    generalize finHom V (γ * h) = B at h2 ⊢
    simp only [map_mul, map_inv] at h1 h2 ⊢
    rw [h3, one_mul] at h2
    rw [← h2, mul_inv_eq_one.1 h1, mul_comm, mul_inv_cancel_right]
  · refine ⟨_, ⟨1, rfl⟩, fun h γ k h' γ' m m' => (hex ⟨h, γ, k, h', γ', m, m'⟩).elim⟩

end GlobalTheory.DetTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoeffFieldAlgClosedFunctionFieldOfTorsionDefined
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem fnAlgClosed_of_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l), 1 ≤ D.p + D.q → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → CurveOver H c.F l.M → FnAlgClosed (Xo := Xo) (c := c) := by
  intro E _ _ _ H D l Xo c hD hA hsig hC
  have hex : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty := by
    classical
    let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then D.p else D.q
    let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
    have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
      rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
        (Equiv.sigmaSubtype τ))]
      simp
    exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩
  obtain ⟨g, ty, hty⟩ := hex
  obtain ⟨F⟩ := GlobalTheory.closing_of_abelianSchemeLaws E H D l Xo (algebraMap (KA l) ℂ) g ty hD rfl hty
  refine GlobalTheory.T.coefficientField_algClosed_in_functionFields_of_periodSpaces E H D l Xo _ g ty F hD rfl hty hA c fun τ hτ => ?_
  have h1 : H.rt0 ∈ KA l := IntermediateField.subset_adjoin _ _ (by simp)
  exact _root_.GlobalTheory.CompRat.permutes_id_of_fixesCurve E H D l Xo _ g ty F hD rfl hty hA hsig τ (hτ _ (c.le h1)) (hC τ hτ)

end GlobalTheory.CompRat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphic
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DatUniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem polAt_of_unif {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (U : PELUnif I t) :
    GlobalTheory.LN.PolAt t (jK R) := by
  have := U.U.gen_hom
  have gp : IsGrpPullback ((Over.pullback (jK R)).obj t.G) U.A.A (𝟙 _) U.U.gen.hom.left :=
    isGrpPullback_of_iso U.U.gen
  have hw : LBIso (U.A.L.pull U.U.gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK R))) := U.bundle ▸ U.U.ext
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) gp.1 U.A.isAb.proper,
    amplePt _ _ _ _ _ _ gp _ _ U.A.isLB (LB.isLB_pull t.PP.isLB _) hw.symm U.A.ample U.A.ktriv⟩

theorem polAt_pull {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f)
    {K K' : Type} [Field K] [Field K'] {j : Sp K ⟶ S} (hp : GlobalTheory.LN.PolAt t j) (j' : Sp K' ⟶ S') (g : Sp K' ⟶ Sp K)
    (h : g ≫ j = j' ≫ f) : GlobalTheory.LN.PolAt t' j' := by
  have g₁ : IsGrpPullback ((Over.pullback j').obj t'.G) t.G (j' ≫ f) (pullback.fst t'.G.hom j' ≫ m.φ) :=
    (isGrpPullback_pullback t'.G j').comp m.cart
  have g₀ := isGrpPullback_pullback t.G j
  have w : (pullback.fst t'.G.hom j' ≫ m.φ) ≫ t.G.hom = (pullback.snd t'.G.hom j' ≫ g) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t'.G.hom j' ⟶ pullback t.G.hom j,
      ψ ≫ pullback.fst _ _ = pullback.fst t'.G.hom j' ≫ m.φ ∧ ψ ≫ pullback.snd _ _ = pullback.snd t'.G.hom j' ≫ g :=
    ⟨pullback.lift _ _ w, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have g₂ : IsGrpPullback ((Over.pullback j').obj t'.G) ((Over.pullback j).obj t.G) g ψ :=
    g₀.cancel (g₁.congr h.symm h₁.symm) h₂
  have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom j)
  have hL' := LB.isLB_pull t'.PP.isLB (pullback.fst t'.G.hom j')
  have e : LBIso (t'.PP.L.pull (pullback.fst t'.G.hom j')) ((t.PP.L.pull (pullback.fst t.G.hom j)).pull ψ) :=
    LBIso.trans hL' (LB.isLB_pull t.PP.isLB _) (LB.isLB_pull hL _)
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl)
      (GlobalTheory.LN.GenericPoint.lbIso_pull ⟨Geo.Tor.idIso _, idIso_isGen hL⟩ _ h₁.symm).symm
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp.1,
    amplePt _ _ g _ _ ψ g₂ _ _ hL hL' e hp.2.1 hp.2.2⟩

theorem norm_unit {R C : Type} [CommRing R] [NormedField C] (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (u : Rˣ) :
    ‖f u‖ = 1 := by
  have h : ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ = 1 := by rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm (hf _) ?_
  calc (1 : ℝ) = ‖f u‖ * ‖f (u⁻¹ : Rˣ)‖ := h.symm
    _ ≤ ‖f u‖ * 1 := mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
    _ = _ := mul_one _

theorem vPsiAt_eq {R C : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] [NormedField C]
    (hR : IsIntegrallyClosed R) (D : DegData R (maximalIdeal R)) (f : R →+* C) (hf : ∀ a, ‖f a‖ ≤ 1) (p : ℕ)
    {χ : D.toPre.X} {r : R} (hr : PsiCoord D.toPre χ r) : vPsiAt D.toPre f p χ = -Real.logb p ‖f r‖ := by
  have h : ∃ r, PsiCoord D.toPre χ r := ⟨r, hr⟩
  obtain ⟨u, hu⟩ := (GlobalTheory.PsiCoordLocal.main R D hR χ).2.1 r _ hr h.choose_spec
  rw [vPsiAt, dite_eq_left h, hu, map_mul, norm_mul, norm_unit f hf, one_mul]

variable {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β} {p : ℕ} {C : SCF p} {P : PointsOfFlagModel.PtC Y C}

theorem locus_eq (A : DatAt Y P) : A.ι ⁻¹' abLocus Y.t.G = abLocus A.t.G :=
  Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x

theorem isOpen_locus (A : DatAt Y P) : IsOpen (A.ι ⁻¹' abLocus Y.t.G) := by
  rw [locus_eq]; exact AbLocusOpen.isOpen_abLocus_local _ A.t.semi

theorem ker_mem (A : DatAt Y P) (q : PrimeSpectrum A.R)
    (hq : q.asIdeal = RingHom.ker ((intO ↥C.S).subtype.comp A.f)) : q ∈ A.ι ⁻¹' abLocus Y.t.G := by
  have z : Sp ↥C.S := (default : PrimeSpectrum ↥C.S)
  have e : spMap ((intO ↥C.S).subtype.comp A.f) ≫ A.ι = P.y ≫ Y.j := by
    rw [spMap_comp, Category.assoc, A.fac, P.ext]
  have hz : spMap ((intO ↥C.S).subtype.comp A.f) z = q := by
    refine PrimeSpectrum.ext ?_
    have := PrimeSpectrum.isPrime z
    rw [hq, RingHom.ker_eq_comap_bot, ← Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z)]
    rfl
  have h₁ : Y.jQ (P.y z) ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨_, rfl⟩
  have h₂ : A.ι q = Y.j (P.y z) := by
    rw [← hz, ← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  show A.ι q ∈ abLocus Y.t.G
  rw [h₂]
  exact h₁

theorem exists_pull (A : DatAt Y P) (S : Subring ↥C.S) [IsLocalRing S] (hN : IsNoetherianRing S)
    (hI : IsIntegrallyClosed S) (hc : IsAdicComplete (maximalIdeal S) S) (h1 : ∀ z : S, ‖(z : ↥C.S)‖ ≤ 1)
    (hm : ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : ↥C.S)‖ < 1) (φ : A.R →+* S)
    (hφ : S.subtype.comp φ = (intO ↥C.S).subtype.comp A.f) (t : SAB H (Sp S)) (m : SABMap t A.t (spMap φ))
    (hp : GlobalTheory.LN.PolAt t (jK S)) :
    ∃ (U : PELUnif (maximalIdeal S) t) (e : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X),
      ∀ χ, vPsiAt U.D.toPre S.subtype p (e χ) = vPsiAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p χ := by
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H S t hp
  have hφ' : ∀ a, ((φ a : S) : ↥C.S) = ((A.f a : intO ↥C.S) : ↥C.S) := fun a => RingHom.congr_fun hφ a
  obtain ⟨U, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H A.R S φ A.t t m A.U _ A.noeth A.normal A.complete
    hN hI hc (fun a ha => (hm _).2 (hφ' a ▸ A.f_loc a ha)) (isOpen_locus A) (locus_eq A).le A.unitOn
    (ker_mem A _ (by rw [← hφ, RingHom.ker_comp_of_injective φ S.subtype_injective])) ⟨B, gen, hg, hw⟩
  refine ⟨U, e, fun χ => ?_⟩
  obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main A.R A.U.D A.normal χ).1
  obtain ⟨u, hu⟩ := he χ r hr
  rw [vPsiAt_eq hI U.D S.subtype h1 p hu, vPsiAt_eq A.normal A.U.D _ (fun a => (A.f a).2) p hr, map_mul, norm_mul,
    norm_unit S.subtype h1, one_mul, ← hφ]
  rfl

theorem exists_equiv (hp : p.Prime) (A A₀ : DatAt Y P) [IsDiscreteValuationRing A₀.R] (hfin : Finite (ResidueField A₀.R))
    (hinj : Function.Injective A₀.f) :
    ∃ e : A.Ylat ≃ₗ[𝓞 E] A₀.Ylat, ∀ a b, A₀.beta (e a) (e b) = A.beta a b := by
  have := A₀.complete
  have hpn : ‖(p : ↥C.S)‖ < 1 := by
    rw [C.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  obtain ⟨S, _, hN, hI, hc, hf, hg, h1, hm⟩ := GlobalTheory.exists_complete_normal_subring_join A.R { V := A₀.R } ↥C.S
    ((intO ↥C.S).subtype.comp A.f) ((intO ↥C.S).subtype.comp A₀.f) p hp hpn hfin A.noeth A.complete
    (fun a => (A.f a).2) A.f_loc (fun a => (A₀.f a).2) A₀.f_loc
  let φ : A.R →+* S := ((intO ↥C.S).subtype.comp A.f).codRestrict S hf
  let φ₀ : A₀.R →+* S := ((intO ↥C.S).subtype.comp A₀.f).codRestrict S hg
  let i : S →+* intO ↥C.S := S.subtype.codRestrict (intO ↥C.S) h1
  have hi : Function.Injective i := fun a b h => Subtype.ext (congrArg (fun z : intO ↥C.S => (z : ↥C.S)) h)
  have hdom : IsDominant (spMap i) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2
      (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)
    exact this
  have hpr : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hsep : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have hξ : spMap φ ≫ A.ι = spMap φ₀ ≫ A₀.ι := by
    refine ext_of_isDominant (spMap i) ?_
    rw [← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp]
    exact A.fac.trans A₀.fac.symm
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp S), Nonempty (SABMap t Y.t (spMap φ ≫ A.ι)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ ≫ A.ι) Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨n, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ A.m m
  obtain ⟨n₀, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ A₀.m (hξ ▸ m)
  obtain ⟨k, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ (𝟙 _) n ((Category.id_comp (spMap φ)).symm ▸ n)
  obtain ⟨gam, hsq⟩ := GlobalTheory.UnifAfterExt.exists_generic_square φ₀ fun a b h =>
    hinj (Subtype.ext (congrArg (fun z : S => (z : ↥C.S)) h))
  have hpol := polAt_pull n₀ (polAt_of_unif A₀.U) (jK S) gam hsq.symm
  obtain ⟨U, e, he⟩ := exists_pull A S hN hI hc h1 hm φ rfl t n hpol
  obtain ⟨U₀, e₀, he₀⟩ := exists_pull A₀ S hN hI hc h1 hm φ₀ rfl t n₀ hpol
  obtain ⟨d, hd⟩ := GlobalTheory.SameCoord.exists_equiv_psiCoord E H S t t k U U₀ hN hI hc
  have key : ∀ χ, vPsiAt A₀.U.D.toPre ((intO ↥C.S).subtype.comp A₀.f) p (((e.trans d).trans e₀.symm) χ) =
      vPsiAt A.U.D.toPre ((intO ↥C.S).subtype.comp A.f) p χ := fun χ => by
    rw [← he, ← he₀, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.trans_apply]
    obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main S U.D hI (e χ)).1
    obtain ⟨u, hu⟩ := hd _ r hr
    rw [vPsiAt_eq hI U₀.D S.subtype h1 p hu, vPsiAt_eq hI U.D S.subtype h1 p hr, map_mul, norm_mul,
      norm_unit S.subtype h1, one_mul]
  refine ⟨(e.trans d).trans e₀.symm, fun a b => ?_⟩
  rw [DatAt.beta, DatAt.beta, betaAt, betaAt, ← map_add (f := _), key, key, key]

theorem coord_ne_zero_and_exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ) (C : SCF p) (P : PointsOfFlagModel.PtC Y C), p.Prime → ∀ (T : CDVR) (g : T.V →+* intO ↥C.S) (ιT : Sp T.V ⟶ Y.X), T.FinRes → Function.Injective g → (∀ a ∈ maximalIdeal T.V, ‖((g a : intO ↥C.S) : ↥C.S)‖ < 1) → spMap g ≫ ιT = P.yt → ∀ A A' : DatAt Y P, (∀ χ r, PsiCoord A.U.D.toPre χ r → ((A.f r : intO ↥C.S) : ↥C.S) ≠ 0) ∧ ∃ e : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (e a) (e b) = A.beta a b := by
  intro E _ _ _ H Dw l Xo c O _ β Y p C P hp T g ιT hT hg hl hfac A A'
  refine ⟨fun χ r hr => (GlobalTheory.PsiCoordLocal.main A.R A.U.D A.normal χ).2.2 _
    ⟨RingHom.ker ((intO ↥C.S).subtype.comp A.f), RingHom.ker_isPrime _⟩ (isOpen_locus A) (ker_mem A _ rfl)
    (A.unitOn χ) r hr, ?_⟩
  obtain ⟨A₀, ⟨_, hfin⟩, hinj, -⟩ := GlobalTheory.DatAtPoint.exists_datAt E H Dw l Xo c O β Y p C P hp T g ιT hT hg hl hfac
  obtain ⟨e, he⟩ := exists_equiv hp A A₀ hfin hinj
  obtain ⟨e', he'⟩ := exists_equiv hp A' A₀ hfin hinj
  refine ⟨e.trans e'.symm, fun a b => ?_⟩
  rw [← he, ← he', LinearEquiv.trans_apply, LinearEquiv.trans_apply, e'.apply_symm_apply, e'.apply_symm_apply]

end GlobalTheory.DatUniq
end

