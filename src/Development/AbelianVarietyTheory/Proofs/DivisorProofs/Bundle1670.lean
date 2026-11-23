module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1400
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0962
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairOfPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnip

theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ b : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add (f := _)]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (q : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

end GlobalTheory.MixXUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerTwoFactorDecomposition
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertTwoFac

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mul_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {g h : UA σ W.J}
    (hg : g ∈ GlobalTheory.InertSph.KAt σ W v) (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : g * h ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e : mat (g * h) = mat g * mat h := rfl
  have e' : mat (g * h)⁻¹ = mat h⁻¹ * mat g⁻¹ := by rw [mul_inv_rev]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h1 : u • (mat g - 1) = 0 := hg.1 u hu
    have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by rw [e]; noncomm_ring
    rw [this, smul_add, ← Matrix.smul_mul, h1, h2, Matrix.zero_mul, add_zero]
  · rw [e, e', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 z hz).1).1, (hh.2 _ (hg.2 z hz).2).2⟩

theorem inv_mem_KAt {σ : E →ₐ[F] E} {d : ℕ} {W : Spc F E d} {v : Pl (F := F)} {h : UA σ W.J}
    (hh : h ∈ GlobalTheory.InertSph.KAt σ W v) : h⁻¹ ∈ GlobalTheory.InertSph.KAt σ W v := by
  have e1 : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · have h2 : u • (mat h - 1) = 0 := hh.1 u hu
    have : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by rw [Matrix.mul_sub, e1]; noncomm_ring
    rw [this, smul_neg, ← Matrix.mul_smul, h2, Matrix.mul_zero, neg_zero]
  · rw [inv_inv]; exact ⟨(hh.2 z hz).2, (hh.2 z hz).1⟩

theorem twoFac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₁ ∈ GlobalTheory.InertSph.KAt σ G.W v, ∃ k₂ ∈ GlobalTheory.InertSph.KAt σ G.W v,
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₁) * M = 1 ∧ M * (1 + mat k₁) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧
    (∃ M : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), (1 + mat k₂) * M = 1 ∧ M * (1 + mat k₂) = 1 ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, M *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) ∧ k = k₁ * k₂ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin k hk
  obtain ⟨Y, hYat, hYint, hYskew, ⟨Np, hNp1, hNp2, hNpi⟩, hm, ⟨ND, hND1, hND2, hNDi⟩⟩ :=
    GlobalTheory.T.exists_skew_cayley_inertPlace_stabilizer F E σ B a a' G X om om' hT v w hin k hk
  obtain ⟨h, hh, hhY⟩ := GlobalTheory.T.cayleyTransform_mem_unitaryLatticeStabilizer F E σ (a + a') G.W v Y hYat hYint hYskew ⟨Np, hNp1, hNp2, hNpi⟩ hm
  have h2 : (2 : 𝓞 F) ∉ v.asIdeal := (hT.base.inert v w hin).1
  have eH : mat h = (1 - Y) * Np := by rw [← hhY, Matrix.mul_assoc, hNp1, Matrix.mul_one]
  have eH' : (1 + Y) * mat h = 1 - Y := by
    rw [eH, ← Matrix.mul_assoc, show (1 + Y) * (1 - Y) = (1 - Y) * (1 + Y) by noncomm_ring, Matrix.mul_assoc, hNp1,
      Matrix.mul_one]
  have eI : mat h⁻¹ * mat h = 1 := by
    show mat (h⁻¹ * h) = 1
    rw [inv_mul_cancel]; rfl
  have intY1 : ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (1 + Y) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v := fun z hz => by
    rw [Matrix.add_mulVec, Matrix.one_mulVec]; exact add_mem hz (hYint z hz)
  refine ⟨k * h, mul_mem_KAt hk hh, h⁻¹, inv_mem_KAt hh, ?_, ?_, by group⟩
  · have e : mat (k * h) = mat k * mat h := rfl
    have h1 : (1 + mat (k * h)) * ((1 + Y) * ND) = 1 := by
      have : (1 + mat k * mat h) * (1 + Y) = 1 + Y + mat k * (1 - Y) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hhY]
      rw [e, ← Matrix.mul_assoc, this, hND1]
    refine ⟨(1 + Y) * ND, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [← Matrix.mulVec_mulVec]; exact intY1 _ (hNDi z hz)
  · have h1 : (1 + mat h⁻¹) * ((⅟(2 : AF F)) • ((1 + Y) * mat h)) = 1 := by
      rw [Matrix.mul_smul]
      have : (1 + mat h⁻¹) * ((1 + Y) * mat h) = (2 : AF F) • (1 : Matrix (Fin (a + a')) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) := by
        have c : (1 + Y) * mat h = mat h * (1 + Y) := eH'.trans hhY.symm
        rw [Matrix.add_mul, Matrix.one_mul, c, ← Matrix.mul_assoc, eI, Matrix.one_mul, hhY, two_smul]
        abel
      rw [this, smul_smul, invOf_mul_self, one_smul]
    refine ⟨_, h1, mul_eq_one_comm.1 h1, fun z hz => ?_⟩
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace F E (a + a') G.W v h2 _ (intY1 _ (hh.2 z hz).1)

end GlobalTheory.InertTwoFac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceUnimodularHermitianFrameCoordinatesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_unimodular_hermitianFrame_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a'), B.IsGood σ → G.IsGood B → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)),
    Formalism.UG.IsInertAt F E v w →
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σL : L →+* L) (q : ℕ)
      (δ : L) (ψL : AddChar L ℂ) (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Formalism.UG.IsUnramInv ϖ σL q → Odd q → (Valued.v δ = 1 ∧ σL δ = -δ) → Function.Injective ι →
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, ι (σL x) = cA σ (ι x)) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      (∀ x, B.ψ (Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (ι x)) = ψL (x + σL x)) →
      ∃ (JS : GL (Fin a) L) (JT : GL (Fin (a + a')) L)
        (Xm : Matrix (Fin (a + a')) (Fin a) L →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
        (iV : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L) →* UA σ G.V.J)
        (iW : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
        JS ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
        (∀ i j, σL ((JS : Matrix (Fin a) (Fin a) L) i j) = (JS : Matrix (Fin a) (Fin a) L) j i) ∧
        (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
        (∀ x y, B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (Xm x) (Xm y)) =
          ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2)) ∧
        (∀ z : Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ↔ ∃ x, Xm x = z) ∧
        (∀ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) → Xm u ∈ latAtV G.V G.W v) ∧
        (∀ z ∈ latAtV G.V G.W v, ∃ u : Matrix (Fin (a + a')) (Fin a) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧ Xm u = z) ∧
        (∀ g h x, actAB (cA σ) (iV g, iW h) (Xm x) =
          Xm (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
            (((g : GL (Fin a) L)⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) ∧
        (∀ g, iV g ∈ UAt σ G.V (evFin F v)) ∧ (∀ h, iW h ∈ UAt σ G.W (evFin F v)) ∧
        (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a) (Fin a) L), (g : GL (Fin a) L) ∈ Formalism.UG.GLint (Fin a) (Formalism.UG.intL L) →
          iV g ∈ GlobalTheory.InertSph.KAt σ G.V v) ∧
        (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
          (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → iW h ∈ GlobalTheory.InertSph.KAt σ G.W v) := by
  first | exact @GlobalTheory.InertLocFrame.frame | exact GlobalTheory.InertLocFrame.frame | (intros; apply GlobalTheory.InertLocFrame.frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IoExtCore
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.IoExtCore
open GlobalTheory.AdTh.IoExtPf

theorem ioExt_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → (∀ i, VStd D i) → (∀ i, LowSm (R.MW i (sg0 D A)) ∧ ExtLine (R.MW i (sg0 D A))) → IoExt R := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hV hM i
  obtain ⟨hs, hl⟩ := hM i
  obtain ⟨-, hK, v, w, hv1, hw1, hio⟩ := hR.thP.ioP i A.μ0
  obtain ⟨hth, hvac, hcW, hcV, hbW⟩ := GlobalTheory.AdTh.VecFockCore.vec_fock_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core D G Pl0 T0 A Ks R F hR i A.μ0 (hV i)).1
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hP.weil.std hP.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    hcV hcW (hR.models.BV i) hbW hP.sigV hP.sigW _ hth hvac
    (GlobalTheory.AdTh.VecNeCore.thetaVector_ne_zero_core D G Pl0 T0 A Ks R F hR i (hV i))
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
    (R.vP i A.μ0)
  let f : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ) := pt ∘ₗ (R.ioP i).flip w
  have hf : ∀ x, f x = R.ptP i A.μ0 (R.ioP i x w) := fun x => rfl
  have hv0 : f (PiTensorProduct.tprod ℂ v) ≠ 0 := by
    rw [hf, hio]
    exact fun h => Delta_ne i (hinj (h.trans (map_zero pt).symm))
  refine ⟨fun ρ => v ρ, fun τ => ⟨hv1 τ, (v τ).2, fun a ha => ?_⟩, v, w, fun _ => rfl, hw1, hio⟩
  have hm := GlobalTheory.LowKProj.lowKSub_stable _ _ _ _ ha _ (v τ).2
  let u : lowT (R.MW i (sg0 D A)) τ := ⟨⟨_, hs τ hm⟩, hm⟩
  have h1 := hK τ _ ha v u rfl w
  rw [hio, _root_.GlobalTheory.AdTh.MinorWeightCore.delta_extremal_weight_core D G Pl0 T0 A Ks R F hR i (hV i) τ a A.μ0, ← hio, ← hf, ← hf] at h1
  have h2 := inj_factor (R.MW i (sg0 D A)) hs hl τ f
    (fun k => R.ωP i A.μ0 (1, atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)))
    (fun k hk v u hu => hK τ k hk v u hu w) v hv0
    (u - cexp (((∑ j, extWt (R.MW i (sg0 D A)) τ j * a j : ℝ) : ℂ) * I) • v τ) (by
      rw [MultilinearMap.map_update_sub, MultilinearMap.map_update_smul, Function.update_eq_self, map_sub, map_smul, ← h1]
      simp)
  exact congrArg (fun y : lowT (R.MW i (sg0 D A)) τ => ((y : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ))
    (sub_eq_zero.1 h2)

end GlobalTheory.AdTh.IoExtCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixFrameCompletedStandardLattice
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

open scoped TensorProduct

namespace GlobalTheory.StdRead

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem int_of_mem_hatL_pi {z : Fin n → E ⊗[F] Formalism.L2.Herm.Af F}
    (hz : z ∈ Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) (i : Fin n) :
    z i ∈ Formalism.L2.Herm.intAf F E := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS at hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hy i (Set.mem_univ i))
    exact Subring.subset_closure (Or.inl ⟨⟨y i, b, hb⟩, rfl⟩)
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact mul_mem a.2 hx

theorem single_mem_hatL_pi (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
      Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS
  refine Submodule.subset_span ⟨Pi.single j 1, fun i _ => ?_, funext fun i => ?_⟩
  · by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  · by_cases h : i = j
    · subst h
      simp only [Pi.single_eq_same, map_one]
    · simp only [Pi.single_eq_of_ne h, map_zero]

theorem entries_int_of_isFrame_pi (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hβ : Formalism.L2.DIV.IsFrame β (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E))) :
    (∀ i j, β.val i j ∈ Formalism.L2.Herm.intAf F E) ∧ ∀ i j, (β⁻¹).val i j ∈ Formalism.L2.Herm.intAf F E := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h1 : Matrix.mulVec β.1 (Pi.single j 1 : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) ∈
        Formalism.L2.Herm.hatL (F := F) (Submodule.pi Set.univ fun _ : Fin n => (1 : Submodule (𝓞 E) E)) := by
      refine (hβ _).2 fun l => ?_
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact int_of_mem_hatL_pi (single_mem_hatL_pi j) l
    have h2 := int_of_mem_hatL_pi h1 i
    rwa [Matrix.mulVec_single_one] at h2
  · have h2 := (hβ _).1 (single_mem_hatL_pi j) i
    rwa [Matrix.mulVec_single_one] at h2

end Gen

theorem isIntM_of_isFrame_stdL : ∀ {D : D7} {n : ℕ} (β : GL (Fin n) (EAf D)),
    Formalism.L2.DIV.IsFrame β (stdL D n) → IsIntM β.val ∧ IsIntM (β⁻¹).val :=
  fun β hβ => entries_int_of_isFrame_pi β hβ

end GlobalTheory.StdRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeWeightMemConeOverLowestKType
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.kType_weight_in_cone_over_lowK : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε H _ _ σ D E lam hP hC hDS hK μ S hS
  have hcomp : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) σ := hDS.2.2.1
  have hI : IsIrredOn (UJset ε) σ := hDS.2.2.2.1
  obtain ⟨w, hw0, -, hwH⟩ := hK.hw μ S hS
  have key : ∃ T : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) T ∧ ∃ x ∈ T.comap D.subtype,
      ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 := by
    by_contra hne
    let Q : Submodule ℂ D :=
      { carrier := {x | ∀ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) →
          ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ = 0}
        add_mem' := by
          intro a b ha hb l hl
          rw [map_add (f := _), inner_add_right, ha l hl, hb l hl, add_zero]
        zero_mem' := by
          intro l hl
          rw [map_zero, inner_zero_right]
        smul_mem' := by
          intro c a ha l hl
          rw [map_smul, inner_smul_right, ha l hl, mul_zero] }
    have hT : ∀ T ∈ {S : Submodule ℂ H | IsKTypeOf ε σ (lowK ε lam) S}, T ≤ Q.map D.subtype := by
      intro T hT y hy
      have hTD := (_root_.GlobalTheory.kTypeInKFinite n ε H σ D E hcomp hU hI hK _ T hT).1
      refine ⟨⟨y, hTD hy⟩, ?_, rfl⟩
      intro l hl
      by_contra h
      exact hne ⟨T, hT, ⟨y, hTD hy⟩, hy, l, hl, h⟩
    have hlow : lowKSub ε lam σ ≤ Q.map D.subtype := sSup_le hT
    have hspan := _root_.GlobalTheory.kfin_span_raising_words_lowK n ε H σ D E lam hP hC hDS hK
    have hle : Submodule.span ℂ {y : D | ∃ l : List (Fin n × Fin n), (∀ p ∈ l, ε p.1 = true ∧ ε p.2 = false) ∧
        ∃ x ∈ (lowKSub ε lam σ).comap D.subtype, y = (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x} ≤
        (ℂ ∙ w)ᗮ := by
      rw [Submodule.span_le]
      rintro y ⟨l, hl, x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨x', hx', hxx⟩ := hlow hx
      have : x' = x := Subtype.ext hxx
      subst this
      exact hx' l hl
    rw [hspan] at hle
    have hw : w ∈ (ℂ ∙ w)ᗮ := hle Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hw
    exact hw0 hw
  obtain ⟨T, hT, x, hx, l, hl, hne⟩ := key
  have hadj := _root_.GlobalTheory.SignInnerAdjoint.main n ε D E hK.unit l w x hne
  obtain ⟨-, hfd, hstab, hhw⟩ := _root_.GlobalTheory.kTypeInKFinite n ε H σ D E hcomp hU hI hK _ T hT
  have hl' : ∀ p ∈ l.reverse.map Prod.swap, ε p.1 = false ∧ ε p.2 = true := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [List.mem_reverse] at hq
    exact ⟨(hl q hq).2, (hl q hq).1⟩
  have hKU : KUnit ε E := fun a b hab y z => Formalism.REAL.isUnitary_kUnit ε E hK.unit a b hab y z
  obtain ⟨l', -, hl'ty, hsum⟩ := _root_.GlobalTheory.HdStep.main n ε D E hK.gl hKU (T.comap D.subtype) hfd hstab (lowK ε lam) hhw
    μ w hwH false true _ hl' x hx hadj
  exact GlobalTheory.root_word_count_letters n ε μ (lowK ε lam) l' hl'ty hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowRow

theorem l6m_le_log_lam3_base_place {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ∀ b : ℝ, R.WeakCharacterisation F → R.PThmA → R.PPos → LowTop R.toRealDat b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p, (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p A3.A.v0) := by
  intro b hC hA hP hL hB j p
  by_cases hW : R.Wp3 j p = ⊥
  · rw [hC.scal.abs0 j A3.A.μ0 p hW, Real.log_exp]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hpos : 0 < R.lam3 j A3.A.μ0 p A3.A.v0 := hP.2 j A3.A.μ0 p A3.A.v0
    have heig := hA j A3.A.μ0 p x hx
    exact (hB j).trans (hL j _ x hx0 hpos heig)

end GlobalTheory.LowRow
end

