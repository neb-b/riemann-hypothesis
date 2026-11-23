module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsGlIsometryCompEqOfNondegenerate
public import Formalism.LocalRingCardinality.DataLevel
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatHatStabiliserIffComplementFrameRel
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

noncomputable section

namespace GlobalTheory.StabFrame

section Lin

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_mulVec_eq (σ : E →ₐ[F] E) {M M' : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E) (hN : N * B = 1) (x : Fin M → E)
    (hM : M' + 1 = M) (hB : ∀ j, hE σ J x (fun i => B i j) = 0) (hx : hE σ J x x ≠ 0) :
    (∀ z, hE σ J x (B *ᵥ z) = 0) ∧ ∀ y, hE σ J x y = 0 → B *ᵥ (N *ᵥ y) = y := by
  let φ : (Fin M → E) →ₗ[E] E :=
    { toFun := fun y => hE σ J x y
      map_add' := fun y z => by
        simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring }
  have hle : LinearMap.range B.mulVecLin ≤ LinearMap.ker φ := by
    rw [Matrix.range_mulVecLin, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hB j
  have hinj : Function.Injective B.mulVecLin := fun z w h => by
    have := congrArg (N *ᵥ ·) h
    simpa [Matrix.mulVec_mulVec, hN] using this
  have h1 : Module.finrank E (LinearMap.range B.mulVecLin) = M' := by
    rw [LinearMap.finrank_range_of_inj hinj]; simp
  have hlt : LinearMap.ker φ < ⊤ := lt_top_iff_ne_top.2 fun h => hx (by
    have : x ∈ LinearMap.ker φ := h ▸ Submodule.mem_top
    exact this)
  have h2 := Submodule.finrank_lt_finrank_of_lt hlt
  rw [finrank_top, Module.finrank_fin_fun] at h2
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨fun z => hle ⟨z, rfl⟩, fun y hy => ?_⟩
  have : y ∈ LinearMap.range B.mulVecLin := heq ▸ hy
  obtain ⟨z, rfl⟩ := this
  simp [Matrix.mulVec_mulVec, hN]

theorem map_mulVec_tmul (R : Type) [CommRing R] [Algebra F R] {m n : ℕ} (C : Matrix (Fin m) (Fin n) E)
    (a : R) (z : Fin n → E) :
    C.map (inclR (F := F) R) *ᵥ (fun i => a ⊗ₜ[F] z i) = fun i => a ⊗ₜ[F] (C *ᵥ z) i := by
  funext i
  simp [Matrix.mulVec, dotProduct, inclR, TensorProduct.tmul_sum]

variable [NumberField F]

theorem mulVec_mem_latHat {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) {S : Set (Fin n → E)}
    {T : Set (Fin m → E)} (h : ∀ z ∈ S, C *ᵥ z ∈ T) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y ∈ latHat F E T := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h z hz, map_mulVec_tmul _ C a z⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Matrix.mulVec_add]; exact add_mem hy hz
  | neg y _ hy => rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_eq_of_mem_latHat {n : ℕ} (C : Matrix (Fin n) (Fin n) E) {S : Set (Fin n → E)}
    (h : ∀ z ∈ S, C *ᵥ z = z) {y : Fin n → Af F ⊗[F] E} (hy : y ∈ latHat F E S) :
    C.map (inclR (F := F) (Af F)) *ᵥ y = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hy
    rw [map_mulVec_tmul, h z hz]
  | zero => rw [Matrix.mulVec_zero]
  | add y z _ _ hy hz => rw [Matrix.mulVec_add, hy, hz]
  | neg y _ hy => rw [Matrix.mulVec_neg, hy]

theorem stabHat_iff {M M' : ℕ} (B : Matrix (Fin M) (Fin M') E) (N : Matrix (Fin M') (Fin M) E)
    (hN : N * B = 1) {P : Set (Fin M → E)} {L' : Set (Fin M' → E)} (h1 : ∀ z, z ∈ L' ↔ B *ᵥ z ∈ P)
    (h2 : ∀ y ∈ P, B *ᵥ (N *ᵥ y) = y) (a b : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (a' b' : Matrix (Fin M') (Fin M') (Af F ⊗[F] E)) (hb : b * a = 1) (hb' : a' * b' = 1)
    (hr : a * B.map (inclR (F := F) (Af F)) = B.map (inclR (F := F) (Af F)) * a') :
    StabHat F P a ↔ StabHat F L' a' := by
  set Bf := B.map (inclR (F := F) (Af F)) with hBf
  set Nf := N.map (inclR (F := F) (Af F)) with hNf
  have hNB : Nf * Bf = 1 := by
    rw [hBf, hNf, ← Matrix.map_mul, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBm : ∀ z ∈ latHat F E L', Bf *ᵥ z ∈ latHat F E P := fun z hz =>
    mulVec_mem_latHat B (fun w hw => (h1 w).1 hw) hz
  have hNm : ∀ y ∈ latHat F E P, Nf *ᵥ y ∈ latHat F E L' := fun y hy =>
    mulVec_mem_latHat N (fun w hw => (h1 _).2 (by rw [h2 w hw]; exact hw)) hy
  have hBN : ∀ y ∈ latHat F E P, Bf *ᵥ (Nf *ᵥ y) = y := fun y hy => by
    rw [Matrix.mulVec_mulVec, hBf, hNf, ← Matrix.map_mul]
    exact mulVec_eq_of_mem_latHat _ (fun w hw => by rw [← Matrix.mulVec_mulVec]; exact h2 w hw) hy
  have hiff : ∀ z, z ∈ latHat F E L' ↔ Bf *ᵥ z ∈ latHat F E P := fun z =>
    ⟨hBm z, fun hz => by simpa [Matrix.mulVec_mulVec, hNB] using hNm _ hz⟩
  have hcomm : ∀ z, a *ᵥ (Bf *ᵥ z) = Bf *ᵥ (a' *ᵥ z) := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hr]
  refine ⟨fun h z => ?_, fun h y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [hiff, hiff, ← hcomm]
    exact h _
  · rw [← hBN y hy, hcomm]
    exact hBm _ ((h _).1 (hNm y hy))
  · have e1 : a' *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) = Nf *ᵥ (a *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, hb', Matrix.one_mulVec]
    have e2 : y = Bf *ᵥ (b' *ᵥ (Nf *ᵥ (a *ᵥ y))) := by
      have := congrArg (b *ᵥ ·) (hcomm (b' *ᵥ (Nf *ᵥ (a *ᵥ y))))
      simp only [e1, hBN _ hy] at this
      rw [Matrix.mulVec_mulVec _ b a, Matrix.mulVec_mulVec _ b a, hb, Matrix.one_mulVec,
        Matrix.one_mulVec] at this
      exact this.symm
    rw [e2]
    exact hBm _ ((h _).2 (by rw [e1]; exact hNm _ hy))

def finPt (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA (AF F) σ J) : HA (Af F) σ J :=
  (⟨Formalism.UG.bc (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom (HA.mat (AF F) σ J g), by
    have hg : Formalism.UG.cT (sigR (AF F) σ) (HA.mat (AF F) σ J g).1 * JR (AF F) J * (HA.mat (AF F) σ J g).1 =
      JR (AF F) J := (show HR (AF F) σ J from g).2
    have := GlobalTheory.UnitarySplit.map_cond _ _ _ (GlobalTheory.UnitarySplit.map_sig (sndA F) σ) (JR (AF F) J)
      (HA.mat (AF F) σ J g).1
    rw [hg, GlobalTheory.UnitarySplit.map_JR] at this
    exact this.symm⟩ : HR (Af F) σ J)

theorem map_snd_incl {m n : ℕ} (C : Matrix (Fin m) (Fin n) E) :
    (C.map (inclR (F := F) (AF F))).map (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom =
      C.map (inclR (F := F) (Af F)) := by
  ext i j
  simp [inclR]

end Lin

theorem stab_iff_of_frameRel : StabTransitive → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E → ∀ (M M' : ℕ) (J : Matrix (Fin M) (Fin M) E) (J' : Matrix (Fin M') (Fin M') E) (B : Matrix (Fin M) (Fin M') E) (x : Fin 1 → Fin M → E), M' + 1 = M → IsHermND σ J → IsHermND σ J' → Formalism.UG.cT (σ : E →+* E) B * J * B = J' → (∀ j, hE σ J (x 0) (fun i => B i j) = 0) → hE σ J (x 0) (x 0) ≠ 0 → ∀ (L : Submodule (𝓞 E) (Fin M → E)) (L' : Set (Fin M' → E)), IsSelfDualLat σ J L → ∀ β : F, (β = 1 ∨ β = -1) → x 0 ∈ L → hE σ J (x 0) (x 0) = algebraMap F E β → (∀ y, y ∈ L' ↔ B *ᵥ y ∈ L) → ∀ (g : HA (AF F) σ J) (g' : HA (AF F) σ J'), g ∈ Hstab (AF F) σ J x → FrameRel J J' B g g' → (g ∈ stab σ J (L : Set (Fin M → E)) ↔ g' ∈ stab σ J' L') := by
  intro H F E _ _ _ _ _ σ hCM hu M M' J J' B x hM hJ hJ' hBJ hB hx L L' hL β hβ hxL hq hL' g g' hg hr
  let p := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom
  have hN : (J'⁻¹ * (Formalism.UG.cT (σ : E →+* E) B * J)) * B = 1 := by
    rw [Matrix.mul_assoc, hBJ, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ'.2)]
  obtain ⟨k1, k2⟩ := exists_mulVec_eq σ J B _ hN (x 0) hM hB hx
  have h3 := (H F E σ hCM hu M J hJ L hL β hβ (x 0) hxL hq).2.2
  have hgf : finPt σ J g ∈ Hstab (Af F) σ J (fun _ => x 0) := by
    have e : (HA.mat (AF F) σ J g).1 *ᵥ (fun i => inclR (AF F) (x 0 i)) = fun i => inclR (AF F) (x 0 i) :=
      congrFun (MulAction.mem_stabilizer_iff.1 hg) 0
    have e' : (p ∘ fun i => inclR (AF F) (x 0 i)) = fun i => inclR (Af F) (x 0 i) := by
      funext i
      simp [p, inclR]
    refine MulAction.mem_stabilizer_iff.2 (funext fun _ => funext fun i => ?_)
    have := RingHom.map_mulVec p (HA.mat (AF F) σ J g).1 (fun i => inclR (AF F) (x 0 i)) i
    rw [e, e'] at this
    exact this.symm.trans (congrFun e' i)
  have h4 : StabHat F (L : Set (Fin M → E)) (finMat σ J g) ↔
      StabHat F (perpIn σ J L (x 0)) (finMat σ J g) := by
    have := SetLike.ext_iff.1 h3 (finPt σ J g)
    rw [Subgroup.mem_inf, Subgroup.mem_inf, and_iff_left hgf, and_iff_left hgf] at this
    exact this
  refine h4.trans (stabHat_iff (P := perpIn σ J L (x 0)) B _ hN (fun z => (hL' z).trans ⟨fun h => ⟨h, k1 z⟩, fun h => h.1⟩)
    (fun y hy => k2 y hy.2) _ (finMat σ J g⁻¹) _ (finMat σ J' g'⁻¹) ?_ ?_ ?_)
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, inv_mul_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · rw [← Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_mul, mul_inv_cancel, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.finMat_one]
  · have : ((HA.mat (AF F) σ J g).1 * B.map (inclR (AF F))).map p =
        (B.map (inclR (AF F)) * (HA.mat (AF F) σ J' g').1).map p := congrArg (fun X => Matrix.map X p) hr
    have := (Matrix.map_mul (f := p)).symm.trans (this.trans (Matrix.map_mul (f := p)))
    rw [map_snd_incl] at this
    exact this

end GlobalTheory.StabFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsSameLengthOneUnitaryOrbit
section
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

namespace GlobalTheory.RatOrbit

theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J : Matrix n n A) (a b : n → A) :
    Formalism.UG.hform s J a b = b ⬝ᵥ Jᵀ *ᵥ (⇑s ∘ a) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, transpose_apply, Function.comp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_mem {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (s : A →+* A) (J : Matrix n n A)
    (g : GL n A) (hg : g ∈ Formalism.UG.UJ s J) (a b : n → A) :
    Formalism.UG.hform s J ((g : Matrix n n A) *ᵥ a) ((g : Matrix n n A) *ᵥ b) = Formalism.UG.hform s J a b := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  have h1 : ⇑s ∘ ((g : Matrix n n A) *ᵥ a) = ((g : Matrix n n A).map s) *ᵥ (⇑s ∘ a) := by
    funext i
    exact RingHom.map_mulVec s _ _ i
  rw [hform_eq, hform_eq, h1]
  conv_rhs => rw [← h]
  simp only [Formalism.UG.cT, transpose_mul, transpose_transpose, ← mulVec_mulVec]
  rw [mulVec_transpose (g : Matrix n n A), dotProduct_comm b, ← dotProduct_mulVec, dotProduct_comm]

theorem bc_mem {R A : Type} [CommRing R] [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (p : R →+* A) (s : R →+* R) (t : A →+* A) (hp : ∀ x, p (s x) = t (p x)) (J : Matrix n n R)
    (g : GL n R) (hg : g ∈ Formalism.UG.UJ s J) : Formalism.UG.bc p g ∈ Formalism.UG.UJ t (J.map p) := by
  have h : Formalism.UG.cT s (g : Matrix n n R) * J * (g : Matrix n n R) = J := hg
  show Formalism.UG.cT t ((g : Matrix n n R).map p) * J.map p * (g : Matrix n n R).map p = J.map p
  rw [← GlobalTheory.UnitarySplit.map_cond p s t hp, h]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem inclR_injective (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem smul_ratTup {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (γ : HA R σ J) (g : GL (Fin M) E)
    (hg : Formalism.UG.bc (inclR (F := F) R) g = (γ : HR R σ J).1) (x : Fin n → Fin M → E) :
    γ • ratTup (F := F) R x = ratTup (F := F) R (fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a) := by
  funext a i
  show (((γ : HR R σ J).1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ (ratTup (F := F) R x a)) i = _
  rw [← hg]
  exact (RingHom.map_mulVec (inclR (F := F) R) _ _ i).symm

theorem rational_sphere_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ x : Fin 1 → Fin M → E, hE σ J (x 0) (x 0) ≠ 0 → Function.Injective (ratTup (F := F) (AF F) : (Fin 1 → Fin M → E) → _) ∧ ∀ y : Fin 1 → Fin M → AF F ⊗[F] E, (∃ x' : Fin 1 → Fin M → E, hE σ J (x' 0) (x' 0) = hE σ J (x 0) (x 0) ∧ ratTup (F := F) (AF F) x' = y) ↔ ∃ γ ∈ ratPts (AF F) σ J, γ • ratTup (F := F) (AF F) x = y := by
  intro F E _ _ _ _ _ σ hCM M J hJ x hx
  refine ⟨?_, fun y => ⟨?_, ?_⟩⟩
  · intro a b hab
    funext k i
    exact inclR_injective F E (congrFun (congrFun hab k) i)
  · rintro ⟨x', hx', rfl⟩
    simp only [hE, hform_eq] at hx hx'
    obtain ⟨g, hg, hgx, -⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mulVec_eq (c := (σ : E →+* E))
      (G := Jᵀ) two_ne_zero (sigma_sigma σ hCM) (fun a b => hJ.1 a b) hx'.symm hx
    have hU : g ∈ Formalism.UG.UJ (σ : E →+* E) J :=
      GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun z w => by rw [hform_eq, hform_eq, hg]
    have hH : Formalism.UG.bc (inclR (F := F) (AF F)) g ∈ HR (AF F) σ J :=
      bc_mem (inclR (F := F) (AF F)) (σ : E →+* E) (sigR (AF F) σ) (fun t => by
        simp [inclR, sigR]) J g hU
    refine ⟨(⟨_, hH⟩ : HR (AF F) σ J), ⟨g, hU, rfl⟩, ?_⟩
    refine (smul_ratTup (AF F) σ J (⟨_, hH⟩ : HR (AF F) σ J) g rfl x).trans ?_
    congr 1
    funext a
    obtain rfl : a = 0 := Subsingleton.elim _ _
    exact hgx
  · rintro ⟨γ, ⟨g, hU, hg⟩, rfl⟩
    exact ⟨fun a => (g : Matrix (Fin M) (Fin M) E) *ᵥ x a, hform_mem _ J g hU _ _,
      (smul_ratTup (AF F) σ J γ g hg x).symm⟩

end GlobalTheory.RatOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelIndexConjLevelVL
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped TensorProduct
open MeasureTheory

namespace GlobalTheory.StabConjIndex

theorem relIndex_conj_comm {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (hmod : ∀ h : H, Measure.modularCharacter h = 1) (K : Subgroup H) (ho : IsOpen (K : Set H))
    (hc : IsCompact (K : Set H)) (g : H) :
    (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'
  let μ : Measure H := Measure.haar
  haveI : μ.IsMulRightInvariant := ⟨fun g => by
    rw [GlobalTheory.AdelicUnimod.map_mul_right_eq, hmod, one_smul]⟩
  have e : (K' : Set H) = (fun x => g⁻¹ * x) ⁻¹' ((fun x => x * g) ⁻¹' (K : Set H)) := by
    ext x
    simp only [hK', SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by simp [mul_assoc]⟩
  have ho' : IsOpen (K' : Set H) := by
    rw [e]
    exact (ho.preimage (continuous_mul_const g)).preimage (continuous_const_mul g⁻¹)
  have hc' : IsCompact (K' : Set H) := by
    rw [hK', Subgroup.coe_map]
    exact hc.image (f := fun x => g * x * g⁻¹) (by fun_prop)
  have hμ : μ K' = μ K := by rw [e, measure_preimage_mul, measure_preimage_mul_right]
  have hoi : IsOpen ((K ⊓ K' : Subgroup H) : Set H) := ho.inter ho'
  have key : ∀ L : Subgroup H, IsCompact (L : Set H) → K ⊓ K' ≤ L →
      ((K ⊓ K').relIndex L : ENNReal) * μ (K ⊓ K' : Subgroup H) = μ L := fun L hL hle => by
    haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
    haveI : Finite (L ⧸ (K ⊓ K').subgroupOf L) :=
      Subgroup.quotient_finite_of_isOpen _ (hoi.preimage continuous_subtype_val)
    haveI : ((K ⊓ K').subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact GlobalTheory.BaseModule.relIndex_mul_measure' _ _ hle hoi.measurableSet μ
  have h1 := key K hc inf_le_left
  have h2 := key K' hc' inf_le_right
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right, hμ, ← h1] at h2
  have h0 : μ (K ⊓ K' : Subgroup H) ≠ 0 := (hoi.measure_pos μ ⟨1, one_mem _⟩).ne'
  have ht : μ (K ⊓ K' : Subgroup H) ≠ ⊤ :=
    ((measure_mono (show ((K ⊓ K' : Subgroup H) : Set H) ⊆ K from inf_le_left (a := K))).trans_lt
      hc.measure_lt_top).ne
  exact_mod_cast ((ENNReal.mul_left_inj h0 ht).1 h2).symm

section Transport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

noncomputable def swap : (v.adicCompletion F ⊗[F] E) ≃+* (E ⊗[F] v.adicCompletion F) :=
  (Algebra.TensorProduct.comm F _ _).toRingEquiv

omit [NumberField E] in
theorem swap_tmul (a : v.adicCompletion F) (x : E) : swap v (a ⊗ₜ[F] x) = x ⊗ₜ[F] a := rfl

theorem swap_mem_int (y : v.adicCompletion F ⊗[F] E) : y ∈ GlobalTheory.AdelicU.intLoc F E v ↔
    swap v y ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring := by
  constructor
  · refine GlobalTheory.AdelicU.intLoc_induction (p := fun y => swap v y ∈
      tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) (fun a ha x => ?_)
      (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
      (fun y hy => by rw [map_neg]; exact neg_mem hy)
    have : swap v (a ⊗ₜ[F] (x : E)) = ((x : E) ⊗ₜ[F] (1 : v.adicCompletion F)) * ((1 : E) ⊗ₜ[F] a) := by
      rw [swap_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact mul_mem (Subring.subset_closure (Or.inl ⟨⟨x, x, rfl⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩))
  · intro h
    have : tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ≤
        (GlobalTheory.AdelicU.intLoc F E v).comap (swap (E := E) v).symm.toRingHom := by
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨_, x, rfl⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩)
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc (one_mem _) x
      · exact GlobalTheory.AdelicU.tmul_mem_intLoc ha 1
    simpa using this h

theorem swap_mem_lat (N : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → v.adicCompletion F ⊗[F] E) :
    y ∈ GlobalTheory.AdelicU.latLoc F N v ↔ (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N := by
  constructor
  · refine GlobalTheory.AdelicU.latLoc_induction (p := fun y => (fun i => swap v (y i)) ∈ latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
      (fun a ha x hx => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_)
    · have h := Submodule.smul_mem (latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N)
        ⟨(1 : E) ⊗ₜ[F] a, Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)⟩ (Submodule.subset_span ⟨x, hx, rfl⟩)
      convert h using 1
      funext i
      change x i ⊗ₜ[F] a = ((1 : E) ⊗ₜ[F] a) * (x i ⊗ₜ[F] (1 : v.adicCompletion F))
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    · convert Submodule.zero_mem _ using 1
      funext i
      exact map_zero _
    · convert add_mem hy hz using 1
      funext i
      exact map_add _ _ _
    · convert neg_mem hy using 1
      funext i
      exact map_neg _ _
  · intro h
    have : ∀ z ∈ latS (F := F) (v.adicCompletion F)
        (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N,
        (fun i => (swap v).symm (z i)) ∈ GlobalTheory.AdelicU.latLoc F N v := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        exact GlobalTheory.AdelicU.tmul_mem_latLoc (one_mem _) hx
      | zero =>
        convert Submodule.zero_mem _ using 1
        funext i
        exact map_zero _
      | add y z _ _ hy hz =>
        convert add_mem hy hz using 1
        funext i
        exact map_add _ _ _
      | smul c y _ hy =>
        have := (GlobalTheory.AdelicU.latLoc F N v).smul_mem
          ⟨(swap v).symm c.1, (swap_mem_int v _).2 (by simpa using c.2)⟩ hy
        convert this using 1
        funext i
        exact map_mul (swap v).symm c.1 (y i)
    simpa using this _ h

omit [NumberField E] in
theorem mem_UPts_swap (g : GL (Fin n) (v.adicCompletion F ⊗[F] E)) :
    bc (swap (E := E) v).toRingHom g ∈ UPts σ J (v.adicCompletion F) ↔ g ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (v.adicCompletion F) σ J := by
  have hs : ∀ x, sigR σ (v.adicCompletion F) (swap v x) = swap v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 : cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) =
      (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (swap (E := E) v).toRingHom := by
    ext i j
    exact hs _
  have h2 : J.map (inclE (F := F) (v.adicCompletion F)) =
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (v.adicCompletion F) J).map (swap (E := E) v).toRingHom := rfl
  change cT (sigR σ (v.adicCompletion F)) (g.1.map (swap (E := E) v).toRingHom) * _ * g.1.map (swap (E := E) v).toRingHom = _ ↔
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1 * _ * g.1 = _
  rw [h1, h2, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective (swap v).injective).eq_iff

noncomputable def toGL : GlobalTheory.AdelicU.GLoc σ J v →* GL (Fin n) (E ⊗[F] v.adicCompletion F) :=
  (bc (swap (E := E) v).toRingHom).comp (GlobalTheory.AdelicU.matHom _ σ J)

omit [NumberField E] in
theorem toGL_injective : Function.Injective (toGL σ J v) := fun _ _ h =>
  GlobalTheory.AdelicU.matHom_injective _ σ J
    (Units.ext (Matrix.map_injective (swap v).injective (congrArg Units.val h)))

omit [NumberField E] in
theorem exists_toGL {γ : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (h : γ ∈ UPts σ J (v.adicCompletion F)) :
    ∃ g, toGL σ J v g = γ := by
  have e : bc (swap (E := E) v).toRingHom (bc (swap (E := E) v).symm.toRingHom γ) = γ := by
    ext i j
    exact (swap v).apply_symm_apply _
  exact ⟨⟨bc (swap (E := E) v).symm.toRingHom γ, (mem_UPts_swap σ J v _).1 (e.symm ▸ h)⟩, e⟩

theorem map_stabLoc (N : Submodule (𝓞 E) (Fin n → E)) :
    (GlobalTheory.AdelicU.stabLoc σ J N v).map (toGL σ J v) = levelVL σ J v N := by
  have key : ∀ g, g ∈ GlobalTheory.AdelicU.stabLoc σ J N v ↔ toGL σ J v g ∈ stabGL (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) N) := fun g => by
    have hm : ∀ y : Fin n → v.adicCompletion F ⊗[F] E,
        (fun i => swap v (((GlobalTheory.AdelicU.matHom _ σ J g).1 *ᵥ y) i)) =
          (toGL σ J v g).1 *ᵥ fun i => swap v (y i) := fun y =>
      funext fun i => RingHom.map_mulVec (swap (E := E) v).toRingHom _ y i
    rw [GlobalTheory.AdelicU.mem_stabLoc]
    simp only [swap_mem_lat, hm]
    refine ⟨fun h x => ?_, fun h y => h _⟩
    simpa using h fun i => (swap v).symm (x i)
  ext γ
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨(mem_UPts_swap σ J v _).2 g.2, (key g).1 hg⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨g, rfl⟩ := exists_toGL σ J v h1
    exact ⟨g, (key g).2 h2, rfl⟩

end Transport

theorem relIndex_conj_levelVL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (hc.sig : E →+* E) J → IsUnit J.det → ∀ (N : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) N → Submodule.span E (N : Set (Fin n → E)) = ⊤ → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ γ ∈ UPts hc.sig J (v.adicCompletion F), ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom).relIndex (levelVL hc.sig J v N) = (levelVL hc.sig J v N).relIndex ((levelVL hc.sig J v N).map (MulAut.conj γ).toMonoidHom) := by
  intro F E _ _ _ _ _ _ hc n J hJ hd N hN hspan v γ hγ
  obtain ⟨δ, hδ, hσδ⟩ : ∃ δ : E, δ ≠ 0 ∧ hc.sig δ = -δ := by
    by_contra! h
    have hs : Function.Surjective (algebraMap F E) := fun a => (hc.fixed a).1 (by
      by_contra hne
      exact h (star a - a) (sub_ne_zero.2 hne) (by show star _ = _; simp))
    have := (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hs⟩).finrank_eq
    rw [hc.deg2, Module.finrank_self] at this
    omega
  haveI : Submodule.IsLattice E N := Submodule.IsLattice.of_fg E (Module.Finite.iff_fg.1 hN)
  haveI : Submodule.IsFullLattice E N := ⟨hspan⟩
  obtain ⟨g, rfl⟩ := exists_toGL hc.sig J v hγ
  have h := relIndex_conj_comm (GlobalTheory.HeckeDual.modular_eq_one hc.sig J (fun x => star_star x) hδ hσδ
    ⟨fun i j => congrFun (congrFun hJ i) j, hd.ne_zero⟩ v) _ (GlobalTheory.AdelicU.isOpen_stabLoc hc.sig J N v)
    (GlobalTheory.AdelicU.isCompact_stabLoc hc.sig J N v) g
  have e : ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (toGL hc.sig J v)).map
      (MulAut.conj (toGL hc.sig J v g)).toMonoidHom =
      ((GlobalTheory.AdelicU.stabLoc hc.sig J N v).map (MulAut.conj g).toMonoidHom).map (toGL hc.sig J v) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext1 x
    simp
  rw [← map_stabLoc, e, Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _),
    Subgroup.relIndex_map_map_of_injective _ _ (toGL_injective _ _ _), h]

end GlobalTheory.StabConjIndex
end

