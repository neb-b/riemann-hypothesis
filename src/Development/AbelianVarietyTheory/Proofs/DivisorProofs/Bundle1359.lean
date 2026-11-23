module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1311
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1300
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalIntegralIntegralNormCongruen
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.StTwLevel

theorem finsum_const_mul {ι : Type} (c : ℂ) (g : ι → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases h : (Function.support g).Finite
  · exact (mul_finsum _ _).symm
  · have hs : Function.support (fun i => c * g i) = Function.support g := by
      ext i; simp [hc]
    rw [finsum_of_infinite_support h, mul_zero, finsum_of_infinite_support (by rwa [hs])]

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun h => c * u h) = c * avg u := by
  by_cases hc : c = 0
  · simp [hc, avg]
  have hR : rStab (fun h => c * u h) = rStab u := by
    ext k
    simp only [GlobalTheory.TwOrbConj.mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hR, finsum_const_mul]
  ring

theorem twOrb_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  simp_rw [avg_const_mul]
  rw [← finsum_const_mul]
  refine finsum_congr fun q => ?_
  ring

theorem clSum_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt : G → ℂ) (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← finsum_const_mul]
  refine finsum_congr fun d => ?_
  split_ifs
  · rw [twOrb_const_mul]; ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stTw2_const_mul (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ)
    (φ : GLw a w × GLw b w → ℂ) : stTw2 a b w Q₁ Q₂ (fun y => c * φ y) = c * stTw2 a b w Q₁ Q₂ φ := by
  unfold stTw2
  exact clSum_const_mul _ _ _ _ _ _

def lev (n : ℕ) (w : Pl E) (k : ℕ) (y : GLw n w) : ℂ :=
  if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ GlobalTheory.PrincCong.congSub w n k then 1 else 0

theorem nrm_eq {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (y : GLw n w) : nrmL n w y = y * thL n w y := by
  unfold nrmL thL
  rw [if_neg hw, if_neg hw]

theorem thL_KGL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) :
    thL n w g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  obtain ⟨h, rfl⟩ := hg
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (GlobalTheory.PrincCong.cj_mem_Ov w)
  exact ⟨thetaGL n c' h, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩

theorem conj_mem_congSub {w : Pl E} {n k : ℕ} {h g : GLw n w} (hh : h ∈ GlobalTheory.LFun.KGL w (n := n))
    (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) : h * g * h⁻¹ ∈ GlobalTheory.PrincCong.congSub w n k := by
  obtain ⟨h', rfl⟩ := hh
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨h' * g' * h'⁻¹, (MonoidHom.normal_ker _).conj_mem g' hg' h', by simp only [map_mul, map_inv]⟩

end GlobalTheory.BCT.StTwLevel

namespace GlobalTheory.BCT.StTwLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le {w : Pl E} {n k : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) :
    g ∈ GlobalTheory.LFun.KGL w (n := n) := ((GlobalTheory.PrincCong.mem_congSub_iff w n k g).1 hg).1

theorem lev_level {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.PrincCong.congSub w n k) :=
  ⟨GlobalTheory.PrincCong.isOpen_congSub w n k, fun _ hg => congSub_le hg, GlobalTheory.PrincCong.thL_mem_congSub w hw n k⟩

theorem lev_hecke {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsHecke (GlobalTheory.PrincCong.congSub w n k) (lev n w k) := by
  refine ⟨?_, fun x hx y => ⟨?_, ?_⟩⟩
  · have hc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
    refine HasCompactSupport.intro' hc.2 (Subgroup.isClosed_of_isOpen _ hc.1) fun y hy => ?_
    unfold lev
    exact if_neg fun h => hy h.1
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : x * y ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hxK hy
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * thL n w x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hθx
      have e : nrmL n w (x * y) = x * nrmL n w y * ((thL n w y)⁻¹ * thL n w x * thL n w y) := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ hx]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : x * y ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem (inv_mem hxK) h)
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w (n := n)
    · have hxy : y * x ∈ GlobalTheory.LFun.KGL w (n := n) := mul_mem hy hxK
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hx
      have e : nrmL n w (y * x) = nrmL n w y * ((thL n w y)⁻¹ * x * thL n w y) * thL n w x := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hθx, Subgroup.mul_mem_cancel_right _ hm]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : y * x ∉ GlobalTheory.LFun.KGL w (n := n) := fun h => hy (by simpa using mul_mem h (inv_mem hxK))
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩

theorem lev_eq {w : Pl E} (n k : ℕ) :
    (fun y : GLw n w => if y ∈ GlobalTheory.LFun.KGL w (n := n) ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j,
      Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}
      then (1 : ℂ) else 0) = lev n w k := by
  funext y
  unfold lev
  exact if_congr (and_congr Iff.rfl (GlobalTheory.PrincCong.mem_congSub_iff w n k _).symm) rfl rfl

theorem stTw2_lev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ w hw a b k Q₁ Q₂ c _ _ _ _ _
  rw [lev_eq a k, lev_eq b k]
  have e : (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then (1 : ℂ) else 0)) =
      fun y => c * GlobalTheory.BCT.tens (lev a w k) (lev b w k) y := by
    funext y
    congr 1
    have h1 := congrFun (lev_eq (w := w) a k) y.1
    have h2 := congrFun (lev_eq (w := w) b k) y.2
    rw [GlobalTheory.BCT.tens, ← h1, ← h2, ite_zero_mul_ite_zero, mul_one]
    exact if_congr and_assoc.symm rfl rfl
  rw [e, stTw2_const_mul, GlobalTheory.BCT.StTwTens.stTw2_tens E a b w Q₁ Q₂ _ _ _ _ (lev_level hw a k) (lev_level hw b k)
    (lev_hecke hw a k) (lev_hecke hw b k)]

end GlobalTheory.BCT.StTwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelic
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem symplectic_isotropic_embedded_vanishes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁),
    (∀ u, form σ JW (H'.ι *ᵥ u) H'.x = 0) → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
        symp (cA σ) (-1) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) u = 0 := by
  intro F E _ _ _ _ _ σ n d d₁ JX JW H' hH u hu z
  obtain ⟨y, rfl⟩ := hu
  have hm : ∀ m, ∑ j, ∑ l, H'.ι j m * JW j l * σ (H'.x l) = 0 := by
    intro m
    have := hH (Pi.single m 1)
    simp only [form, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  have hm' : ∀ m, ∑ j, ∑ l, inclR (F := F) (AF F) (H'.ι j m) * inclR (F := F) (AF F) (JW j l) * inclR (F := F) (AF F) (σ (H'.x l)) = 0 := fun m => by
    have := congrArg (inclR (F := F) (AF F)) (hm m)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_mul, map_zero] using this
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => by simp [cA, inclR]
  have h1 : (incM F (1 : Matrix (Fin n) (Fin n) E)) = 1 := by simp [incM]
  unfold symp
  suffices h : hTens (cA σ) (incM F JX) (incM F JW) (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) (Matrix.vecMulVec y (incV F H'.x)) = 0 by
    rw [h, mul_zero, map_zero]
  rw [h1, Matrix.one_mul]
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, incV, map_mul, hc]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  calc _ = ∑ m, (z i m * inclR (F := F) (AF F) (JX i k) * cA σ (y k)) *
        ∑ j, ∑ l, inclR (F := F) (AF F) (H'.ι j m) * inclR (F := F) (AF F) (JW j l) * inclR (F := F) (AF F) (σ (H'.x l)) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        ring
    _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hm' m, mul_zero]
end GlobalTheory.MixedLagr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem hTens_vecMulVec {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symplectic_isotropic_plane_vanishes (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d d₁ : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) :
    form σ JW H'.x H'.x = 0 → ∀ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))),
      ∀ u' ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), symp (cA σ) (-1) (incM F JX) (incM F JW) u u' = 0 := by
  rintro h0 u ⟨a, rfl⟩ u' ⟨a', rfl⟩
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have h : ∑ j, ∑ l, incV F H'.x j * incM F JW j l * cA σ (incV F H'.x l) = 0 := by
    have h1 := congrArg (inclR (F := F) (AF F)) h0
    rw [map_zero] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]
  rw [symp, hTens_vecMulVec, h, mul_zero, mul_zero, map_zero]

end GlobalTheory.MixedLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingBlockReduction
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WeilM

theorem symp_fromBlocks_hyperbolic :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  intro R S _ _ _ c ξ α β _ _ _ _ r₀ J₀ K z z'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symp, hTens, ← map_add (f := _), ← map_sum, ← mul_add, ← Finset.mul_sum]
  congr 2
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.one_apply]

end GlobalTheory.WeilM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameConjMap
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

open scoped Classical

namespace GlobalTheory.DoublingEv.ConjTame

def conjSch {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℂ →SL[starRingEnd ℂ] SchwartzMap D ℂ :=
  SchwartzMap.mkCLM (𝕜 := ℂ) (𝕜' := ℂ) (σ := starRingEnd ℂ) (fun f x => star (f x))
    (fun f g x => by simp [star_add])
    (fun a f x => by simp [smul_eq_mul, mul_comm])
    (fun f => Complex.conjCLE.contDiff.comp (f.smooth ⊤))
    (fun n => ⟨{n}, 1, zero_le_one, fun f x => by
      have h : (fun x => star (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := rfl
      rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Finset.sup_singleton, one_mul]
      exact SchwartzMap.le_seminorm ℂ n.1 n.2 f x⟩)

theorem conjSch_apply {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] (f : SchwartzMap D ℂ) (x : D) :
    conjSch f x = star (f x) := rfl

theorem star_mem_SB {X : Type} [TopologicalSpace X] {g : X → ℂ} (hg : g ∈ SB X) : star g ∈ SB X :=
  ⟨hg.1.comp star, hg.2.comp_left (g := star) (star_zero ℂ)⟩

variable {F : Type} [Field F] [NumberField F]

theorem star_pureA {κ : Type} [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    star (pureA F (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
  funext x
  simp [pureA, conjSch_apply, star_mul', Pi.star_apply]

end GlobalTheory.DoublingEv.ConjTame


open GlobalTheory.DoublingEv.ConjTame in
theorem GlobalTheory.DoublingEv.isTame_conjMap : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)), IsTame F T → IsTame F (conjMap T) := by
  intro F _ _ κ κ' _ _ T hT g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT (star g) (star_mem_SB hg)
  let Q : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ :=
    fun j => (conjSch.comp (P j)).comp conjSch
  refine ⟨ι, inferInstance, Q, fun j => star (g' j), fun j => star_mem_SB (hg' j), fun f => ?_⟩
  have hs : star (pureA F (f : _ → ℂ) g) = pureA F (conjSch f : _ → ℂ) (star g) := by
    rw [star_pureA]
  rw [conjMap_apply, hs, hP, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_pureA]
  rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameInvariantKilledSmoothSpaceCentreMem
section
open NumberField GlobalTheory.CuspRep GlobalTheory.AutGrowth

namespace GlobalTheory.CapKilled

theorem zalg_mem_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ)
    (L : Subgroup (GL (Fin b) (Af E))) (W : Submodule ℂ (Kinf E b → ℂ)), FiniteDimensional ℂ W →
    ∀ (q : (E →+* ℂ) → ℂ → Polynomial ℂ) (z : Module.End ℂ (Sm E b)), z ∈ Zalg E b →
    ∀ ψ ∈ GlobalTheory.CapKilled.space E b L W q, z ψ ∈ GlobalTheory.CapKilled.space E b L W q := by
  intro E _ _ _ b L W hW q z hz ψ hψ
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_space.1 hψ
  refine mem_space.2 ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Zalg_stable (V := leftInv E b) (fun X _ h => lie_mem_leftInv X h) hz ψ h1
  · exact Zalg_stable (V := fixL E b L) (fun X _ h => lie_mem_fixL L X h) hz ψ h2
  · intro g
    obtain ⟨s, c, hc⟩ := GlobalTheory.HCFct.exists_interp W hW
    have hk : ∀ k : Kinf E b, cptRep E b k ψ = ∑ i : s, (c i).1 k • cptRep E b i.1 ψ := by
      intro k
      apply Subtype.ext
      funext h
      have := hc _ (h3 h) k
      rw [this]
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    have e : (fun k : Kinf E b => (cptRep E b k (z ψ)).1 g) =
        ∑ i : s, (z (cptRep E b i.1 ψ)).1 g • (c i).1 := by
      funext k
      have hcomm := LinearMap.congr_fun (GlobalTheory.ZalgCpt.zalg_comm_cptRep E b k z hz) ψ
      simp only [Module.End.mul_apply] at hcomm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hcomm, hk k, map_sum]
      simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [e]
    exact W.sum_mem fun i _ => W.smul_mem _ (c i).2
  · intro τ u
    have hcap : cap (a := b) τ u ∈ Zalg E b := Algebra.subset_adjoin ⟨τ, u, rfl⟩
    have hp : Polynomial.aeval (cap (a := b) τ u) (q τ u) ∈ Zalg E b := Algebra.adjoin_le (Set.singleton_subset_iff.2 hcap) (Polynomial.aeval_mem_adjoin_singleton ℂ _)
    have hcomm := (KilledFin.Zalg_commute hz hp).eq
    have := LinearMap.congr_fun hcomm ψ
    simp only [Module.End.mul_apply] at this
    rw [← this, h4 τ u, map_zero]
  · exact Zalg_stable (V := tame E b) (fun X _ h => lie_mem_tame X h) hz ψ h5

end GlobalTheory.CapKilled
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionDeterminantRoot
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem weil_twist_base : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.Char F → ∀ (i : Fin D.R.m) (t : T0) (k : GA D (Wc D i)) (x : (AE D)ˣ), IsDetRoot (Wc D i) k x → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → R.ωP i t (1, k) f = ((R.xi t x : Circle) : ℂ) • R.ωP i A.μ0 (1, k) f := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t k x hx f hf
  have h := GlobalTheory.TwistFactorProof.frame_ratio R (_root_.GlobalTheory.WeilUniq.weilDatum_unique D) (_root_.GlobalTheory.WeilChange.exists_weilDatum_twist D) hR.thP.ωP i A.μ0 t hx hf
  rw [GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hR.lev.xi_base ▸ hR.lev.xi A.μ0) x, Circle.coe_one, one_smul] at h
  exact h

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem exists_den_traceDual_ringOfIntegers :
    ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F,
      (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _
  refine ⟨(NumberField.discr F).natAbs, Int.natAbs_pos.mpr (NumberField.discr_ne_zero F), ?_⟩
  intro ξ hξ
  have hint := GlobalTheory.discr_mul_isIntegral_of_traceDual F ξ hξ
  have hint' : IsIntegral ℤ (((NumberField.discr F).natAbs : F) * ξ) := by
    rcases Int.natAbs_eq (NumberField.discr F) with h | h
    · have : ((NumberField.discr F).natAbs : F) = (NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = NumberField.discr F := by omega
        rw [← Int.cast_natCast, h']
      rw [this]; exact hint
    · have : ((NumberField.discr F).natAbs : F) = -(NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = -(NumberField.discr F) := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

end GlobalTheory
end

