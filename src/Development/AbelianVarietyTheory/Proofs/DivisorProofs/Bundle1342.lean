module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelVanishingFiltrationDeepestStepSpan
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort

theorem totFil_deepest : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K), X.IsGood s → IsNef K X.LA → IsBig K X.LA → X.MulStable → totFil X s (X.T - X.D) = ⨆ α : MonoDeg (Fin X.D) (X.T - X.D), (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) := by
  intro hF K _ _ X s hs hn hb hm
  have hP := filP hF K X s hs hn hb
  have hVT : spaceP X s ≤ X.V X.T := le_sup_right.trans (mulPow_mem_and_spaceV_le K X s hm).2
  have hL : totFil X s (X.T - X.D) = (spaceP X s).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    show ((Fil (X.ideal s) (X.T - X.D) (spaceV X s)).comap (X.V X.T).subtype).map
        (LinearMap.single K _ X.T ∘ₗ (X.V X.T).subtype) = _
    rw [hP, Submodule.map_comp, Submodule.map_comap_subtype, inf_of_le_right hVT]
  have hR : ∀ α : MonoDeg (Fin X.D) (X.T - X.D),
      (LinearMap.range (incl X X.D)).map (pw (shift X.toGeo) s α.1) =
        ((X.V X.D).map (mulPow X.toGeo s (add_sub_D X) α)).map (LinearMap.single K (fun j => X.Sec j) X.T) := by
    intro α
    have he : pw (shift X.toGeo) s α.1 ∘ₗ LinearMap.single K (fun j => X.Sec j) X.D =
        LinearMap.single K (fun j => X.Sec j) X.T ∘ₗ mulPow X.toGeo s (add_sub_D X) α := by
      refine LinearMap.ext fun m => ?_
      simp only [LinearMap.comp_apply, LinearMap.coe_single]
      exact (_root_.GlobalTheory.HSShort.shift_comm_single_mono K X.toGeo).2.2 s (X.T - X.D) X.D X.T (add_sub_D X) α m
    rw [show incl X X.D = LinearMap.single K (fun j => X.Sec j) X.D ∘ₗ (X.V X.D).subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype, ← Submodule.map_comp, he, Submodule.map_comp]
  rw [hL, iSup_congr hR, ← Submodule.map_iSup]
  rfl

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
noncomputable section

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR_eq (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_cA_eq (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem incM_mulVec_incV_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  ext i; simp [incM, incV, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem cA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (x : Fin n → E) :
    (fun i => cA σ (incV F x i)) = incV F (fun i => σ (x i)) := by
  funext i; simp [incV, cA_inclR_eq]

theorem hA_incV_eq (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    hA σ J (incV F a) (incV F b) = inclR (AF F) (form σ J a b) := by
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [form, incV, dotProduct, map_sum, map_mul]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hA_add_l (v v' w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J (v + v') w = hA σ J v w + hA σ J v' w := by
  simp [hA, add_dotProduct]

theorem hA_smul_l (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J (a • v) w = a * hA σ J v w := by
  simp [hA, smul_dotProduct]

theorem hA_add_r (v w w' : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J v (w + w') = hA σ J v w + hA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_add, dotProduct_add]; rfl

theorem hA_smul_r (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  have : (fun i => cA σ ((a • w) i)) = cA σ a • (fun i => cA σ (w i)) := by
    funext i; simp
  rw [hA, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem hA_skew_eq (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    hA σ J w v = -cA σ (hA σ J v w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hA, dotProduct, Matrix.mulVec, incM, Matrix.map_apply, map_sum, map_mul, cA_cA_eq σ hσ, cA_inclR_eq,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; simp only [map_neg]; ring

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_mat_eq (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (mat g) v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg]

theorem hA_ι_incV_eq (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (ι : Matrix (Fin d) (Fin d₁) E)
    (w : Fin d → E) (h : ∀ u, form σ J (ι *ᵥ u) w = 0) (z : Fin d₁ → AE F E) :
    hA σ J (incM F ι *ᵥ z) (incV F w) = 0 := by
  have hq : ιᵀ *ᵥ (J *ᵥ fun i => σ (w i)) = 0 := by
    funext k
    have := h (Pi.single k 1)
    rw [form, Matrix.mulVec_single_one] at this
    exact this
  rw [hA, cA_incV_eq, incM_mulVec_incV_eq, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    show (incM F ι)ᵀ = incM F ιᵀ from rfl, incM_mulVec_incV_eq, hq]
  have : incV F (0 : Fin d₁ → E) = 0 := by funext i; simp [incV]
  rw [this, dotProduct_zero]

theorem incV_add_eq {n : ℕ} (a b : Fin n → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul_eq {n : ℕ} (s : E) (a : Fin n → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem decomp_eq {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hdec : ∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • x + ι *ᵥ u + t • y) (v : Fin d → AE F E) :
    ∃ (s t : AE F E) (z : Fin d₁ → AE F E), v = s • incV F x + incM F ι *ᵥ z + t • incV F y := by
  choose s t u hu using fun i => hdec (Pi.single i 1)
  have he : ∀ i, incV F (Pi.single i (1 : E)) =
      inclR (F := F) (AF F) (s i) • incV F x + incM F ι *ᵥ incV F (u i) + inclR (F := F) (AF F) (t i) • incV F y := by
    intro i
    rw [hu i, incV_add_eq, incV_add_eq, incV_smul_eq, incV_smul_eq, incM_mulVec_incV_eq]
  have hv : v = ∑ i, v i • incV F (Pi.single i (1 : E)) := by
    funext k; simp [incV, Finset.sum_apply, Pi.single_apply]
  refine ⟨∑ i, v i * inclR (F := F) (AF F) (s i), ∑ i, v i * inclR (F := F) (AF F) (t i), ∑ i, v i • incV F (u i), ?_⟩
  calc v = ∑ i, v i • incV F (Pi.single i (1 : E)) := hv
    _ = _ := by
      simp only [he, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem mem_unip_std (σ : E →ₐ[F] E) {d d₁ : ℕ} (W : Spc F E d) (H' : Plane E d d₁) (g : UA σ W.J)
    (hg : g ∈ unip σ W H') :
    mat g *ᵥ incV F H'.x = incV F H'.x ∧
      ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x := by
  unfold unip at hg
  induction hg using Subgroup.closure_induction with
  | mem u hu => exact hu
  | one => exact ⟨by simp [mat], fun z => ⟨0, by simp [mat]⟩⟩
  | mul u v _ _ hu hv =>
    have hm : mat (u * v) = mat u * mat v := rfl
    refine ⟨?_, fun z => ?_⟩
    · rw [hm, ← Matrix.mulVec_mulVec, hv.1, hu.1]
    · obtain ⟨a, ha⟩ := hv.2 z
      obtain ⟨b, hb⟩ := hu.2 z
      refine ⟨b + a, ?_⟩
      rw [hm, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hu.1, add_smul]
      abel
  | inv u _ hu =>
    have h1 : mat u⁻¹ * mat u = 1 := by
      rw [show mat u⁻¹ * mat u = mat (u⁻¹ * u) from rfl, inv_mul_cancel]; rfl
    have hx : mat u⁻¹ *ᵥ incV F H'.x = incV F H'.x := by
      conv_lhs => rw [← hu.1]
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    refine ⟨hx, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hu.2 z
    have key : mat u⁻¹ *ᵥ (incM F H'.ι *ᵥ z + a • incV F H'.x) = incM F H'.ι *ᵥ z := by
      rw [← ha, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx] at key
    refine ⟨-a, ?_⟩
    rw [eq_sub_of_add_eq key, neg_smul, sub_eq_add_neg]

end GlobalTheory.UnipMass.StdMat

namespace GlobalTheory.UnipMass.StdMat

theorem unip_eq_nmat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (d d₁ : ℕ) (W : Spc F E d) (H' : Plane E d d₁), (∀ i j, σ (W.J j i) = -W.J i j) → form σ W.J H'.x H'.x = 0 → form σ W.J H'.y H'.y = 0 → form σ W.J H'.x H'.y = 1 → (∀ u, form σ W.J (H'.ι *ᵥ u) H'.x = 0 ∧ form σ W.J (H'.ι *ᵥ u) H'.y = 0) → (∀ v : Fin d → E, ∃ (s t : E) (u : Fin d₁ → E), v = s • H'.x + H'.ι *ᵥ u + t • H'.y) → ∀ g ∈ unip σ W H', ∃ (b : Fin d₁ → AE F E) (c : AE F E), c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ b) (incM F H'.ι *ᵥ b) ∧ mat g = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ b) c := by
  intro F E _ _ _ _ _ σ hσ d d₁ W H' hJ hxx hyy hxy horth hdec g hg
  have hXX : hA σ W.J (incV F H'.x) (incV F H'.x) = 0 := by rw [hA_incV_eq, hxx, map_zero]
  have hYY : hA σ W.J (incV F H'.y) (incV F H'.y) = 0 := by rw [hA_incV_eq, hyy, map_zero]
  have hXY : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV_eq, hxy, map_one]
  have hYX : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
    rw [hA_skew_eq σ W.J hσ hJ, hXY, map_one]
  have hιX : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.x (fun u => (horth u).1)
  have hιY : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.y) = 0 :=
    hA_ι_incV_eq σ W.J H'.ι H'.y (fun u => (horth u).2)
  have hXι : ∀ z, hA σ W.J (incV F H'.x) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιX, map_zero, neg_zero]
  have hYι : ∀ z, hA σ W.J (incV F H'.y) (incM F H'.ι *ᵥ z) = 0 := fun z => by
    rw [hA_skew_eq σ W.J hσ hJ, hιY, map_zero, neg_zero]
  obtain ⟨hgX, hgι⟩ := mem_unip_std σ W H' g hg
  have inv : ∀ v w, hA σ W.J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ W.J v w := hA_mat_eq σ g
  have dec := decomp_eq (F := F) H'.x H'.y H'.ι hdec
  obtain ⟨α, γ, β, hgY⟩ := dec (mat g *ᵥ incV F H'.y)
  have hγ : γ = 1 := by
    have h := inv (incV F H'.y) (incV F H'.x)
    rw [hgX, hgY] at h
    simp only [hA_add_l, hA_smul_l, hXX, hιX, hYX] at h
    linear_combination -h
  subst hγ
  have ha : ∀ z (a : AE F E), mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x →
      a = -hA σ W.J (incM F H'.ι *ᵥ z) (incM F H'.ι *ᵥ β) := by
    intro z a h
    have h2 := inv (incM F H'.ι *ᵥ z) (incV F H'.y)
    rw [h, hgY] at h2
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hιX, hιY, hXι, mul_zero, mul_one, zero_add,
      add_zero, one_smul] at h2
    linear_combination h2
  have hα : α - cA σ α = -hA σ W.J (incM F H'.ι *ᵥ β) (incM F H'.ι *ᵥ β) := by
    have h3 := inv (incV F H'.y) (incV F H'.y)
    rw [hgY] at h3
    simp only [hA_add_l, hA_add_r, hA_smul_l, hA_smul_r, hXX, hXY, hYX, hYY, hιX, hιY, hXι, hYι, mul_zero, mul_one,
      zero_add, add_zero, one_smul, one_mul] at h3
    linear_combination h3
  refine ⟨β, α, hα, ?_⟩
  have key : ∀ v, mat g *ᵥ v = nmat σ W.J (incV F H'.x) (incM F H'.ι *ᵥ β) α *ᵥ v := by
    intro v
    obtain ⟨s, t, z, rfl⟩ := dec v
    obtain ⟨a, hz⟩ := hgι z
    have ha' := ha z a hz
    rw [nmat_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hgX, hz, hgY, hA_add_l, hA_smul_l, hXX, hιX, hYX, hXι, hYι,
      mul_zero, zero_add, add_zero, one_smul]
    rw [ha']
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  ext i j
  have h4 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h4

end GlobalTheory.UnipMass.StdMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLatticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  first | exact @GlobalTheory.TransferHyp.cj_mem_hyp_iff | exact GlobalTheory.TransferHyp.cj_mem_hyp_iff | (intros; apply GlobalTheory.TransferHyp.cj_mem_hyp_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocGL.LExist

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ Δ : Segment k, ∃ x : IrrGL (k := k), IsLSeg Δ x.rep) →
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep := by
  intro k _ _ _ _ _ hS hL 𝔪
  obtain ⟨Δ, hΔ⟩ := ((precedes_and_orderedForms k).1.2.2) 𝔪
  choose y hy using hL
  let x : Fin 𝔪.card → IrrGL (k := k) := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := hS k 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

end GlobalTheory.LocGL.LExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTerSide
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CoordinateEmbeddingMaps

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ball (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (C : ℝ) (hC : 0 ≤ C) : AddSubgroup (Fv F v) where
  carrier := {c | ‖c‖ ≤ C}
  zero_mem' := by simpa using hC
  add_mem' := by
    intro a b ha hb
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := by
    intro a ha
    simpa using ha

theorem norm_le_one_of_mem {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    ‖a‖ ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.mpr h

def coordE (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (n : ℕ) (x : (_ : Fin n) × Fin (Module.finrank F E)) :
    (Fin n → E) →+ Fv F v where
  toFun y := algebraMap F (Fv F v) ((Module.finBasis F E).repr (y x.1) x.2)
  map_zero' := by simp
  map_add' := by intro a b; simp

theorem main : (let d1 : (F E : Type) → [inst : Field F] → [inst_1 : NumberField F] → [inst_2 : Field E] → [NumberField E] → [inst_4 : Algebra F E] → (n : ℕ) → Module.Basis ((_ : Fin n) × Fin (Module.finrank F E)) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := @(fun (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) ↦ Pi.basis fun (x : Fin n) ↦ Module.Basis.baseChange (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (Module.finBasis F E)); ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n), Submodule.FG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.L W) → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∃ (C : ℝ), ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ (x : (_ : Fin n) × Fin (Module.finrank F E)), ‖(GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (((Module.Basis.repr (d1 F E n) : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (_ : Fin n) × Fin (Module.finrank F E) →₀ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) z : (_ : Fin n) × Fin (Module.finrank F E) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x)‖ ≤ C) := by
  intro d1 F E _ _ _ _ _ n W hL v
  obtain ⟨s, hs⟩ := (hL.restrictScalars : (W.L.restrictScalars ℤ).FG)
  set C : ℝ := ∑ x : (_ : Fin n) × Fin (Module.finrank F E), ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ with hCdef
  have hC : 0 ≤ C := by positivity
  refine ⟨C, ?_⟩

  have hLb : ∀ x, ∀ y ∈ W.L, ‖coordE (F := F) (E := E) v n x y‖ ≤ C := by
    intro x y hy
    have hle : W.L.restrictScalars ℤ ≤ ((ball v C hC).comap (coordE (F := F) (E := E) v n x)).toIntSubmodule := by
      rw [← hs, Submodule.span_le]
      intro g hg
      show ‖coordE (F := F) (E := E) v n x g‖ ≤ C
      calc ‖coordE (F := F) (E := E) v n x g‖
          ≤ ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖ :=
            Finset.single_le_sum (f := fun g => ‖coordE (F := F) (E := E) v n x g‖) (fun _ _ => norm_nonneg _) hg
        _ ≤ C := Finset.single_le_sum (f := fun x => ∑ g ∈ s, ‖coordE (F := F) (E := E) v n x g‖)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ x)
    exact hle hy
  intro z hz x

  let φ : (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) →+ Fv F v :=
    (GlobalTheory.AdelicU.evFin F v).toAddMonoidHom.comp
      ((Finsupp.applyAddHom x).comp (d1 F E n).repr.toLinearMap.toAddMonoidHom)
  have hφ : ∀ z, φ z = GlobalTheory.AdelicU.evFin F v ((d1 F E n).repr z x) := fun z => rfl
  have key : GlobalTheory.InertSph.latAt W v ≤ (ball v C hC).comap φ := by
    unfold GlobalTheory.InertSph.latAt
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, y, hy, rfl⟩
    show ‖φ _‖ ≤ C
    rw [hφ]
    have : (d1 F E n).repr (a • fun i => inclR (F := F) (AF F) (y i)) x
        = a * algebraMap F (AF F) ((Module.finBasis F E).repr (y x.1) x.2) := by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      congr 1
      simp only [d1, Pi.basis_repr]
      show ((Module.finBasis F E).baseChange (AF F)).repr ((1 : AF F) ⊗ₜ[F] y x.1) x.2 = _
      rw [Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
    rw [this, map_mul, AlgHom.commutes, norm_mul]
    have h1 := norm_le_one_of_mem _ ha
    have h2 := hLb x y hy
    calc _ ≤ 1 * C := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  exact key hz

end GlobalTheory.CoordinateEmbeddingMaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundAll
section
open scoped Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

namespace GlobalTheory.IdxAll

theorem eq_or_eq_comp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e τ : E →+* ℂ) (heτ : e.comp (algebraMap F E) = τ.comp (algebraMap F E)) :
    τ = e ∨ ∀ x, τ x = star (e x) := by
  obtain ⟨-, hc, h2, hσ⟩ := h
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨g, hg⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) e τ heτ
  have hσσ : ∀ x, σ (σ x) = x := fun x => e.injective (by rw [hσ, hσ, star_star])
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσσ) (AlgHom.ext hσσ)
  have hs : s ≠ 1 := by
    intro h1
    refine IsTotallyComplex.complexEmbedding_not_isReal e ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have : σ x = x := congrArg (fun t : E ≃ₐ[F] E => t x) h1
    have h3 := hσ e x
    rw [this] at h3
    exact h3.symm
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  by_cases hg1 : g.symm = 1
  · left
    rw [← hg, hg1]
    rfl
  · right
    intro x
    rw [← hg, (hy _ hg1).trans (hy _ hs).symm]
    exact hσ e x

end GlobalTheory.IdxAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.BlockForms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)

structure IsAdapted (C : GL (Fin n) E) : Prop where
  le : 2 * r ≤ n
  colX : ∀ (i : Fin n) (j : Fin r), i.val = j.val → ∀ k, C.1 k i = X k j
  columnBlock : ∀ (i : Fin n) (j : Fin r), i.val + j.val + 1 = n → ∀ k, C.1 k i = Y k j
  perpX : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) X * J) *ᵥ (fun k => C.1 k i) = 0
  perpY : ∀ i : Fin n, r ≤ i.val → i.val + r < n → (cT (σ : E →+* E) Y * J) *ᵥ (fun k => C.1 k i) = 0

def blkCols {l d : ℕ} (h : l + d ≤ r) (Z : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin d) E :=
  Z.submatrix id fun j => ⟨l + j.val, by omega⟩

def IsBlockEmb {l d : ℕ} (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J) : Prop :=
  ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
    Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
    (∀ z, Φ z = (j (GlobalTheory.LFun.infTens F E z), GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E z))) ∧
    ∀ g : GlobalTheory.CuspRep.GA E d, (matHom _ σ J (ι g)).1 =
      1 + adMat F (blkCols h X) * (g.1.map Φ.symm - 1) * adMat F (cT (σ : E →+* E) (blkCols h Y) * J) +
        adMat F (blkCols h Y) * (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm) - 1) *
          adMat F (cT (σ : E →+* E) (blkCols h X) * J)


end GlobalTheory.BlockForms

end
end

