module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormIntegralIffLatticeUnimodular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquivStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'), IsClosed (twCent θ δ : Set G) → IsClosed (twCent θ' δ' : Set G') → ∀ (e : twCent θ δ ≃ₜ* twCent θ' δ'), (∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') → mass θ Γ δ = mass θ' Γ' δ' := by
  first | exact @GlobalTheory.MassTor.mass_eq_of_equiv | exact GlobalTheory.MassTor.mass_eq_of_equiv | (intros; apply GlobalTheory.MassTor.mass_eq_of_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjIffMulNormInvAlg
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

theorem invT_invT (h : GLw m w) : invT m _ (invT m _ h) = h :=
  Units.ext (by change (h.val)ᵀᵀ = h.val; exact transpose_transpose _)

theorem invT_injective : Function.Injective (invT m (w.adicCompletion E)) := fun x y hxy => by
  rw [← invT_invT x, hxy, invT_invT]

theorem dlt_eq_iff (hw : ¬ IsSplitAt w) (β β' : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (hβ' : IsUnit (GlobalTheory.TwLat.gram e b β'))
    (g : GLw m w) :
    GlobalTheory.TwLat.dlt e b β' = g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ↔ g.valᵀ * GlobalTheory.TwLat.gram e b β * g.val.map (cj w) = GlobalTheory.TwLat.gram e b β' := by
  unfold GlobalTheory.TwLat.dlt
  rw [dite_eq_left hβ, dite_eq_left hβ']
  have hth : thL m w g = PhiU m _ * invT m _ (GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    simp only [thL, if_neg hw]; rfl
  have hinv : g⁻¹ = invT m _ (invT m _ g⁻¹) := (invT_invT _).symm
  have key : g⁻¹ * (invT m _ hβ.unit * (PhiU m _)⁻¹) * thL m w g =
      invT m _ (invT m _ g⁻¹ * hβ.unit * GeneralLinearGroup.map (cj w) g) * (PhiU m _)⁻¹ := by
    rw [hth, map_mul, map_mul, ← hinv]; group
  rw [key, mul_left_inj, invT_injective.eq_iff, Units.ext_iff, eq_comm]
  rfl

theorem herm_sum_left (β z : B.A) (f : Fin m → B.A) : B.herm β (∑ i, f i) z = ∑ i, B.herm β (f i) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (β y : B.A) (f : Fin m → B.A) : B.herm β y (∑ i, f i) = ∑ i, B.herm β y (f i) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_sub_left (β y y' z : B.A) : B.herm β (y - y') z = B.herm β y z - B.herm β y' z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_sub, sub_mul, map_sub]

theorem herm_crd (he : ∀ x, e (K.c x) = cj w (e x)) (β y z : B.A) :
    e (B.herm β y z) = crd e b y ⬝ᵥ (GlobalTheory.TwLat.gram e b β *ᵥ fun l => cj w (crd e b z l)) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, map_sum,
    map_mul, he]
  simp only [dotProduct, mulVec, crd, GlobalTheory.TwLat.gram, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem cj_cj (he : ∀ x, e (K.c x) = cj w (e x)) (z : w.adicCompletion E) : cj w (cj w z) = z := by
  obtain ⟨k, rfl⟩ := e.surjective z
  rw [← he, ← he, K.c_c]

theorem eq_zero_of_herm (he : ∀ x, e (K.c x) = cj w (e x)) (β : B.A) (hβ : IsUnit (GlobalTheory.TwLat.gram e b β)) (d : B.A)
    (hd : ∀ t, B.herm β d t = 0) : d = 0 := by
  have h1 : ∀ v, (crd e b d ᵥ* GlobalTheory.TwLat.gram e b β) ⬝ᵥ v = 0 := by
    intro v
    have h := congrArg e (hd (ofCrd e b fun l => cj w (v l)))
    rw [herm_crd e b he, map_zero, dotProduct_mulVec] at h
    have hv : (fun l => cj w (crd e b (ofCrd e b fun l => cj w (v l)) l)) = v := by
      funext l; rw [crd_ofCrd, cj_cj e he]
    rwa [hv] at h
  have h2 : crd e b d ᵥ* GlobalTheory.TwLat.gram e b β = 0 := by
    funext j
    have := h1 (Pi.single j 1)
    simpa [dotProduct_single] using this
  have h3 : crd e b d = 0 := by
    have : crd e b d = (crd e b d ᵥ* (hβ.unit : Matrix (Fin m) (Fin m) (w.adicCompletion E))) ᵥ*
        ((hβ.unit⁻¹ : (Matrix (Fin m) (Fin m) (w.adicCompletion E))ˣ) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
    rw [this, IsUnit.unit_spec, h2, zero_vecMul]
  apply crd_injective e b
  rw [h3]; funext i; simp [crd]

end GlobalTheory.TwLatInj

namespace GlobalTheory.TwLatInj

open GlobalTheory.TwOrbLat GlobalTheory.TwLat

theorem dlt_twConj_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) →
    ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ u : B.A,
    Algebra.adjoin K.E {u} = ⊤ → ∀ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * ((-1) ^ (m - 1) * u) →
    (∀ x : B.Aˣ, IsUnit (GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x))) → ∀ x x' : B.Aˣ, B.σ (x : B.A) = x →
    B.σ (x' : B.A) = x' →
    ((∃ g : GLw m w, GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x') = g⁻¹ * GlobalTheory.TwLat.dlt e b ((β₀ : B.A) * x) * thL m w g) ↔
      ∃ a : B.Aˣ, (x' : B.A) = x * (a * B.σ a)) := by
  intro E _ _ _ _ w hw K e he _ _ B m b u hu β₀ hβ₀ hG x x' hx hx'
  obtain ⟨ε, hε⟩ : ∃ ε : B.A, ε = (-1) ^ (m - 1) := ⟨_, rfl⟩
  rw [← hε] at hβ₀
  have hε2 : ε * ε = 1 := by rw [hε, ← mul_pow]; simp
  have hεa : ε = algebraMap K.E B.A ((-1) ^ (m - 1)) := by rw [hε]; simp

  have hasym : ∀ t : B.A, B.σ t = t → ∀ y z, K.c (B.herm ((β₀ : B.A) * t) y z) =
      B.herm ((β₀ : B.A) * t) (ε * u * z) y := by
    intro t ht y z
    unfold GlobalTheory.UnitLemma.InvAlg.herm
    rw [← GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, map_mul B.σ, hβ₀, ht, B.σ_σ]
    congr 1; ring
  constructor
  · rintro ⟨g, hg⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x') g] at hg
    let φ : B.A → B.A := fun a => ofCrd e b (g.val *ᵥ crd e b a)
    have hcφ : ∀ a, crd e b (φ a) = g.val *ᵥ crd e b a := fun a => crd_ofCrd e b _
    have hφs : ∀ (k : K.E) (a : B.A), φ (k • a) = k • φ a := by
      intro k a; apply crd_injective e b; rw [hcφ, crd_smul, crd_smul, hcφ, mulVec_smul]
    have hφadd : ∀ a a', φ (a + a') = φ a + φ a' := by
      intro a a'; apply crd_injective e b; rw [hcφ, crd_add, crd_add, hcφ, hcφ, mulVec_add]
    have hφsurj : ∀ t, φ (ofCrd e b ((g⁻¹ : GLw m w).val *ᵥ crd e b t)) = t := by
      intro t; apply crd_injective e b
      rw [hcφ, crd_ofCrd, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

    have hiso : ∀ y z, B.herm ((β₀ : B.A) * x) (φ y) (φ z) = B.herm ((β₀ : B.A) * x') y z := by
      intro y z; apply e.injective
      rw [herm_crd e b he, herm_crd e b he, hcφ, hcφ, ← hg]
      have hc : (fun l => cj w ((g.val *ᵥ crd e b z) l)) = g.val.map (cj w) *ᵥ fun l => cj w (crd e b z l) := by
        funext l; exact RingHom.map_mulVec (cj w) g.val (crd e b z) l
      have ht : g.val *ᵥ crd e b y = crd e b y ᵥ* g.valᵀ := (vecMul_transpose _ _).symm
      rw [hc, ht]
      simp only [dotProduct_mulVec, vecMul_vecMul]

    have hv : ∀ z, φ (ε * u * z) = ε * u * φ z := by
      intro z
      have key : ∀ y, B.herm ((β₀ : B.A) * x) (φ (ε * u * z) - ε * u * φ z) (φ y) = 0 := by
        intro y
        rw [herm_sub_left, hiso, ← hasym x' hx', ← hiso, hasym x hx, sub_self]
      exact sub_eq_zero.1 (eq_zero_of_herm e b he _ (hG x) _ fun t => by rw [← hφsurj t]; exact key _)
    have hφu : ∀ z, φ (u * z) = u * φ z := by
      intro z
      have h1 : φ (ε * u * z) = ε * φ (u * z) := by
        rw [mul_assoc, hεa, ← Algebra.smul_def, ← Algebra.smul_def, hφs]
      have h2 := (hv z).symm.trans h1
      linear_combination (-ε) * h2 - (φ (u * z) - u * φ z) * hε2
    have hφmul : ∀ a c, φ (a * c) = a * φ c := by
      intro a
      have ha : a ∈ Algebra.adjoin K.E {u} := by rw [hu]; trivial
      induction ha using Algebra.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff] at hz; subst hz; exact hφu
      | algebraMap r =>
        intro c; rw [← Algebra.smul_def, ← Algebra.smul_def, hφs]
      | add a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [add_mul, hφadd, h₁, h₂, add_mul]
      | mul a₁ a₂ _ _ h₁ h₂ =>
        intro c; rw [mul_assoc, h₁, h₂, mul_assoc]
    have hφ : ∀ a, φ a = a * φ 1 := fun a => by rw [← hφmul, mul_one]
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, φ a₀ = 1 := ⟨_, hφsurj 1⟩
    let c : B.Aˣ := ⟨φ 1, a₀, by rw [mul_comm, ← hφ, ha₀], by rw [← hφ, ha₀]⟩
    refine ⟨c, ?_⟩
    have hc : (c : B.A) = φ 1 := rfl
    have hxx : (x : B.A) * ((x⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv x
    have hd : ∀ t, B.herm ((β₀ : B.A) * x) (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) t = 0 := by
      intro t
      have h1 := hiso 1 t
      rw [hφ t, ← hc] at h1
      unfold GlobalTheory.UnitLemma.InvAlg.herm at h1 ⊢
      have h3 : (β₀ : B.A) * x * (((x⁻¹ : B.Aˣ) : B.A) * (x' - x * (c * B.σ c))) * B.σ t =
          (β₀ : B.A) * x' * 1 * B.σ t - (β₀ : B.A) * x * c * B.σ (t * c) := by
        rw [map_mul B.σ]
        linear_combination ((β₀ : B.A) * (x' - x * (c * B.σ c)) * B.σ t) * hxx
      rw [h3, map_sub, h1, sub_self]
    have h0 := eq_zero_of_herm e b he _ (hG x) _ hd
    have : (x' : B.A) - x * (c * B.σ c) = 0 := by
      rw [← one_mul ((x' : B.A) - _), ← hxx, mul_assoc, h0, mul_zero]
    exact sub_eq_zero.1 this
  · rintro ⟨a, ha⟩
    refine ⟨mulGL e b a, ?_⟩
    rw [dlt_eq_iff e b hw _ _ (hG x) (hG x')]
    ext i j
    have h1 : GlobalTheory.TwLat.gram e b ((β₀ : B.A) * x') i j = e (B.herm ((β₀ : B.A) * x) (a * b i) (a * b j)) := by
      simp only [GlobalTheory.TwLat.gram, Matrix.of_apply]
      rw [ha, ← mul_assoc, GlobalTheory.UnitLemma.Basic.herm_norm]
    rw [h1, herm_crd e b he]
    have hcol : ∀ i, crd e b ((a : B.A) * b i) = fun k => (mulGL e b a).val k i := by
      intro i; funext k; rw [mulGL_val, ← mulHom_eq, mulHom_apply]; rfl
    rw [hcol, hcol]
    congr 1
    simp only [dotProduct, mulVec, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

end GlobalTheory.TwLatInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegular
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtReg

theorem exists_ne_of_avg_ne {H : Type} [Group H] {u : H → ℂ} (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [avg, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem exists_ne_of_hint_ne {H : Type} [Group H] {K : Subgroup H} {u : H → ℂ} (h : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [hint, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem charpoly_conj_GL {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (k g : GL ι R) :
    ((k⁻¹ * g * k : GL ι R) : Matrix ι ι R).charpoly = (g : Matrix ι ι R).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem ctMu_regAt2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf m hm
  have hct : ct h w (fun y => f (toSub _ y)) m ≠ 0 := by
    intro h0; apply hm; rw [ctMu, h0, mul_zero]
  rw [ct] at hct
  obtain ⟨X, hX⟩ := exists_ne_of_hint_ne (right_ne_zero_of_mul hct)
  obtain ⟨k, hk⟩ := exists_ne_of_avg_ne hX
  have hsep := hf _ hk
  have hmem : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k) ∈ UL n w := by
    rw [UL, if_pos hw]; exact Subgroup.mem_top _
  have e0 : (toSub (UL n w) ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)).1 =
      (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k := by
    rw [toSub, dite_eq_left hmem]
  rw [e0, charpoly_conj_GL, blk_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁] at hsep
  have e1 : nrmL a w m.1 = m.1 := by rw [nrmL, if_pos hw]
  have e2 : nrmL b w m.2 = m.2 := by rw [nrmL, if_pos hw]
  rw [e1, e2]
  exact hsep

end GlobalTheory.BCT.CtReg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormIntegralIffLatticeUnimodularStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedNorm_integral_iff_lattice_unimodular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ β : B.A, IsUnit (GlobalTheory.TwLat.gram e b β) → ∀ g : GLw m w, (g⁻¹ * GlobalTheory.TwLat.dlt e b β * thL m w g ∈ GlobalTheory.LFun.KGL w (n := m) ↔ ∀ z, z ∈ GlobalTheory.TwLat.lat e b g ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.herm β y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.TwLat.Unimod.unimodular_iff | exact GlobalTheory.TwLat.Unimod.unimodular_iff | (intros; apply GlobalTheory.TwLat.Unimod.unimodular_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UNInjective
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviFubini

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev parB {a b n : ℕ} (h : a + b = n) (w : Pl E) : Subgroup (GLw n w) :=
  GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h))

def levH {a b n : ℕ} (h : a + b = n) (w : Pl E) : parB h w →* GLw a w × GLw b w :=
  (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)).symm.toMonoidHom.comp
    (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)))

theorem blk_mem {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : blk h w m X ∈ parB h w := by
  rw [GlobalTheory.SmGL.mem_parab_two]
  intro j i
  rw [CtLevel.blk_val]
  show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
    (CtLevel.blkEq h (Sum.inr j)) (CtLevel.blkEq h (Sum.inl i)) = 0
  simp

theorem blk_mul_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m m' : GLw a w × GLw b w)
    (X X' : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    blk h w m X * blk h w m' X' = blk h w (m * m') (X' + (m'.1⁻¹).val * X * m'.2.val) := by
  ext1
  rw [Units.val_mul, CtLevel.blk_val, CtLevel.blk_val, CtLevel.blk_val, reindex_apply, reindex_apply, reindex_apply,
    submatrix_mul_equiv, fromBlocks_multiply]
  congr 1
  simp only [Prod.fst_mul, Prod.snd_mul, Units.val_mul, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add,
    Matrix.mul_add]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (m'.1.val) ((m'.1⁻¹ : GLw a w).val), Units.mul_inv, Matrix.one_mul]

theorem blk_one_zero {a b n : ℕ} (h : a + b = n) (w : Pl E) : blk h w 1 0 = 1 := by
  ext1
  rw [CtLevel.blk_val, Prod.fst_one, Prod.snd_one, Units.val_one, Units.val_one, Matrix.mul_zero, fromBlocks_one,
    reindex_apply, submatrix_one_equiv]
  rfl

def sM {a b n : ℕ} (h : a + b = n) (w : Pl E) : GLw a w × GLw b w →* parB h w where
  toFun m := ⟨blk h w m 0, blk_mem h w m 0⟩
  map_one' := Subtype.ext (blk_one_zero h w)
  map_mul' m m' := Subtype.ext (by simp [blk_mul_blk])

def uN {a b n : ℕ} (h : a + b = n) (w : Pl E) : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) →* parB h w where
  toFun X := ⟨blk h w 1 (Multiplicative.toAdd X), blk_mem h w 1 _⟩
  map_one' := Subtype.ext (by simpa using blk_one_zero h w)
  map_mul' X Y := Subtype.ext (by simp [blk_mul_blk, add_comm])

theorem sM_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) :
    (sM h w m : GLw n w) = blk h w m 0 := rfl

theorem uN_val {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    (uN h w X : GLw n w) = blk h w 1 (Multiplicative.toAdd X) := rfl

theorem sM_mul_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    ((sM h w m * uN h w X : parB h w) : GLw n w) = blk h w m (Multiplicative.toAdd X) := by
  rw [Subgroup.coe_mul, sM_val, uN_val, blk_mul_blk]
  simp

theorem levH_blk {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : levH h w ⟨blk h w m X, blk_mem h w m X⟩ = m := by
  have key : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ x :
        GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j = ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m x : GL (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [GlobalTheory.SmGL.leviProj_apply, CtLevel.blk_val]
    cases x
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inl i)) (CtLevel.blkEq h (Sum.inl j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
    · show (reindex (CtLevel.blkEq h) (CtLevel.blkEq h) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val))
        (CtLevel.blkEq h (Sum.inr i)) (CtLevel.blkEq h (Sum.inr j)) = _
      simp [GlobalTheory.SmGL.leviTwo]
  have : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) ⟨blk h w m X, blk_mem h w m X⟩ =
      GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m := by
    funext x; exact Units.ext (Matrix.ext fun i j => key x i j)
  simp only [levH, MonoidHom.coe_comp, Function.comp_apply, this]
  simp

theorem levH_sM {a b n : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) : levH h w (sM h w m) = m :=
  levH_blk h w m 0

theorem levH_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :
    levH h w (uN h w X) = 1 :=
  levH_blk h w 1 _

theorem uN_injective {a b n : ℕ} (h : a + b = n) (w : Pl E) : Function.Injective (uN h w) := by
  intro X Y hXY
  have h1 := congrArg (fun p : parB h w => ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hXY
  simp only [uN_val, CtLevel.blk_val] at h1
  have h2 := congrArg (fun M => M.toBlocks₁₂) ((reindex (CtLevel.blkEq h) (CtLevel.blkEq h)).injective h1)
  simpa using h2

theorem exists_uN {a b n : ℕ} (h : a + b = n) (w : Pl E) (p : parB h w) (hp : levH h w p = 1) :
    ∃ X, uN h w X = p := by
  have hl : GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h)) p = 1 := by
    have := congrArg (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b)) hp
    simpa [levH] using this
  have hd : ∀ (x : Bool) (i j : GlobalTheory.SmGL.Two (Fin a) (Fin b) x),
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, i⟩) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) ⟨x, j⟩) =
        (1 : Matrix (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (GlobalTheory.SmGL.Two (Fin a) (Fin b) x) (w.adicCompletion E)) i j := by
    intro x i j
    rw [← GlobalTheory.SmGL.leviProj_apply, hl]
    rfl
  have h0 := (GlobalTheory.SmGL.mem_parab_two _).1 p.2
  refine ⟨Multiplicative.ofAdd
    ((((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)).submatrix (CtLevel.blkEq h) (CtLevel.blkEq h)).toBlocks₁₂),
    Subtype.ext (Units.ext ?_)⟩
  rw [uN_val, CtLevel.blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (CtLevel.blkEq h).surjective i
  obtain ⟨j, rfl⟩ := (CtLevel.blkEq h).surjective j
  rw [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j
  · rw [fromBlocks_apply₁₁]
    exact (hd false i j).symm
  · simp [toBlocks₁₂]
  · rw [fromBlocks_apply₂₁]
    exact (h0 i j).symm
  · rw [fromBlocks_apply₂₂]
    exact (hd true i j).symm

end GlobalTheory.LeviFubini
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SplitChar

theorem locK_mul_locK_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  intro E _ _ _ μ e h w u hne hunder k
  have hc : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv u w := by
    have hw : w ∈ aboveF (L := E) (maximalRealSubfield E) (u.under (𝓞 (maximalRealSubfield E))) := by
      simp [aboveF, hunder]
    exact ((GlobalTheory.CuspRep.NormTriv.mem_aboveF_iff u w).1 hw).resolve_left (Ne.symm hne)
  have h1 := GlobalTheory.CuspRep.NormTriv.normFin_loc _ μ hc k
  refine (Eq.trans ?_ h1.symm).trans ?_
  · rfl
  · rw [GlobalTheory.CuspRep.NormTriv.normFin, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MonoidHom.mul_apply, MonoidHom.id_apply, map_mul, GlobalTheory.BCT.MuProps.finId_conjFin, ← GlobalTheory.PolChar.ideleConj_eq]
    rw [map_mul]
    exact GlobalTheory.BCT.MuProps.mu_mul_conj h _

end GlobalTheory.BCT.SplitChar
end

