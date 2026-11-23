module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SingleMulSingle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceAdjointMatrixIsCoordinateEquivariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor.AdjCoord

variable {D : D7} {v : FinPl D}

def conjProj (φ : SplitProj D v) : SplitProj D v :=
  φ.comp (Algebra.TensorProduct.map (AlgHom.id (Fv D.host.F v) (Fv D.host.F v)) D.sp.cm.sig)

theorem rdA_conjProj (φ : SplitProj D v) (a : AE D) : rdA (conjProj φ) a = rdA φ (cA D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [_root_.map_zero]
  | tmul x y =>
    simp only [rdA, conjProj, RingHom.comp_apply, cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, GlobalTheory.AdelicU.compFin,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]

theorem isIdemOf_conjProj {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : IsIdemOf (conjProj φ) (cA D e) := by
  have hcc : ∀ x : AE D, cA D (cA D x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]
    | tmul a y =>
      simp only [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact star_star y
    | add x y hx hy => simp only [_root_.map_add (f := _), hx, hy]
  refine ⟨GlobalTheory.SplitScalar.isSplitIdem_conj he.1, ?_, ?_⟩
  · rw [hcc, add_comm]; exact he.2.1
  · rw [rdA_conjProj, hcc]; exact he.2.2

def trHomeo {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {m n : ℕ}
    (A A' : Matrix (Fin n) (Fin n) K) (B B' : Matrix (Fin m) (Fin m) K) (hA : A' * A = 1) (hB : B * B' = 1) :
    Matrix (Fin m) (Fin n) K ≃ₜ Matrix (Fin n) (Fin m) K where
  toFun y := A * yᵀ * B
  invFun z := (A' * z * B')ᵀ
  left_inv y := by
    have : A' * (A * yᵀ * B) * B' = (A' * A) * yᵀ * (B * B') := by simp only [Matrix.mul_assoc]
    simp only [this, hA, hB, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_transpose]
  right_inv z := by
    have : A * (A' * z * B') * B = (A * A') * z * (B' * B) := by simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_transpose, this, mul_eq_one_comm.1 hA, mul_eq_one_comm.1 hB, Matrix.one_mul,
      Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const
  continuous_invFun := ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_transpose

theorem isCoord_comp {S T : HSp D} {m n : ℕ} {a : AE D} {Λ : AddSubgroup (WO S T)}
    {κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)} (h : IsCoord a Λ κ)
    (A A' : Matrix (Fin n) (Fin n) (Fv D.host.F v)) (B B' : Matrix (Fin m) (Fin m) (Fv D.host.F v))
    (hA : A' * A = 1) (hB : B * B' = 1) : IsCoord a Λ (fun t => A * (κ t)ᵀ * B) := by
  have e : (fun t => A * (κ t)ᵀ * B) = ⇑(trHomeo A A' B B' hA hB) ∘ κ := rfl
  refine ⟨fun x y => ?_, ?_, ?_, ?_⟩
  · simp only [h.1 x y, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  · rw [e]; exact (Set.bijOn_univ.2 (trHomeo A A' B B' hA hB).bijective).comp h.2.1
  · rw [e, Set.image_comp]; exact (trHomeo A A' B B' hA hB).isOpenMap _ h.2.2.1
  · rw [e, Set.image_comp]; exact h.2.2.2.image (trHomeo A A' B B' hA hB).continuous

theorem gram_inv_mul (V : HSp D) : (V.gram⁻¹).map (incA D) * V.gram.map (incA D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V)]
  exact Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)

theorem adj_mul {A : Type} [CommRing A] (σ : A →+* A) {a b : ℕ} (G G' k k' : Matrix (Fin a) (Fin a) A)
    (H m m' : Matrix (Fin b) (Fin b) A) (x : Matrix (Fin b) (Fin a) A) (h1 : G' * G = 1)
    (hk : Formalism.UG.cT σ k * G * k = G) (hm : Formalism.UG.cT σ m * H * m = H) (hk' : k * k' = 1) (hm' : m * m' = 1) :
    G' * Formalism.UG.cT σ (m * x * k) * H = k' * (G' * Formalism.UG.cT σ x * H) * m' := by
  have hG : G * G' = 1 := mul_eq_one_comm.1 h1
  have s1 : Formalism.UG.cT σ k * G = G * k' := calc
    Formalism.UG.cT σ k * G = Formalism.UG.cT σ k * G * (k * k') := by rw [hk', Matrix.mul_one]
    _ = (Formalism.UG.cT σ k * G * k) * k' := by simp only [Matrix.mul_assoc]
    _ = G * k' := by rw [hk]
  have e1 : G' * Formalism.UG.cT σ k = k' * G' := calc
    G' * Formalism.UG.cT σ k = G' * (Formalism.UG.cT σ k * (G * G')) := by rw [hG, Matrix.mul_one]
    _ = G' * ((Formalism.UG.cT σ k * G) * G') := by simp only [Matrix.mul_assoc]
    _ = (G' * G) * k' * G' := by rw [s1]; simp only [Matrix.mul_assoc]
    _ = k' * G' := by rw [h1, Matrix.one_mul]
  have e2 : Formalism.UG.cT σ m * H = H * m' := calc
    Formalism.UG.cT σ m * H = Formalism.UG.cT σ m * H * (m * m') := by rw [hm', Matrix.mul_one]
    _ = (Formalism.UG.cT σ m * H * m) * m' := by simp only [Matrix.mul_assoc]
    _ = H * m' := by rw [hm]
  unfold Formalism.UG.cT at *
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  calc G' * ((k.map σ)ᵀ * ((x.map σ)ᵀ * (m.map σ)ᵀ)) * H
      = (G' * (k.map σ)ᵀ) * (x.map σ)ᵀ * ((m.map σ)ᵀ * H) := by simp only [Matrix.mul_assoc]
    _ = k' * (G' * (x.map σ)ᵀ * H) * m' := by rw [e1, e2]; simp only [Matrix.mul_assoc]

theorem map_mul_conj {A K : Type} [CommRing A] [CommRing K] (π : A →+* K) {a b : ℕ} (P : GL (Fin a) K) (Q : GL (Fin b) K)
    (k : Matrix (Fin a) (Fin a) A) (m : Matrix (Fin b) (Fin b) A) (X Y : Matrix (Fin a) (Fin b) A) (h : Y = k * X * m) :
    (P⁻¹).val * Y.map π * Q.val =
      ((P⁻¹).val * k.map π * P.val) * ((P⁻¹).val * X.map π * Q.val) * ((Q⁻¹).val * m.map π * Q.val) := by
  subst h
  simp only [Matrix.map_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  first
  | rw [Units.mul_inv_cancel_left]
  | rw [← Matrix.mul_assoc (P : Matrix (Fin a) (Fin a) K), Units.mul_inv, Matrix.one_mul]

theorem mt_mul_mt_inv (V : HSp D) (g : GA D V) : Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← _root_.map_mul, _root_.mul_inv_cancel, _root_.map_one, Units.val_one]

theorem grpCo_val (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g).val = (B⁻¹).val * (Formalism.L2.Theta.mt V g).map (rdA φ) * B.val := rfl

theorem grpCo_inv (φ : SplitProj D v) (V : HSp D) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    (grpCo φ V B g)⁻¹ = grpCo φ V B g⁻¹ := by
  simp only [grpCo, _root_.mul_inv_rev, _root_.inv_inv, _root_.map_inv, _root_.mul_assoc]

theorem adjCo_actO (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (g : GA D S) (h : GA D T) (t : WO S T) :
    adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  have hm' : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simpa only [_root_.inv_inv] using mt_mul_mt_inv T h⁻¹
  have key := adj_mul (cA D) (S.gram.map (incA D)) ((S.gram⁻¹).map (incA D)) (Formalism.L2.Theta.mt S g)
    (Formalism.L2.Theta.mt S g⁻¹) (T.gram.map (incA D)) (Formalism.L2.Theta.mt T h⁻¹) (Formalism.L2.Theta.mt T h)
    (t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (gram_inv_mul S) (by exact g.2) (by exact h⁻¹.2)
    (mt_mul_mt_inv S g) hm'
  unfold Formalism.UG.cT at key
  have hact : (actO S T g⁻¹ h⁻¹ t : Matrix (Fin T.rank) (Fin S.rank) (AE D)) =
      Formalism.L2.Theta.mt T h⁻¹ * t * Formalism.L2.Theta.mt S g := by
    first
    | rfl
    | (simp only [actO, _root_.inv_inv]; done)
    | simp [actO]
  unfold adjCo
  rw [hact, key, map_mul_conj (rdA φ) BS BT (Formalism.L2.Theta.mt S g⁻¹) (Formalism.L2.Theta.mt T h) _ _ rfl, grpCo_inv,
    grpCo_val, grpCo_val]

end GlobalTheory.PlaceTensor.AdjCoord

namespace GlobalTheory.PlaceTensor

open AdjCoord

theorem adjCo_isCoord : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → ∀ (BS : GL (Fin S.rank) (Fv D.host.F v)) (BT : GL (Fin T.rank) (Fv D.host.F v)), IsCoord (cA D e) (latO S T ΛS ΛT fun _ => True) (adjCo φ S T BS BT) ∧ ∀ (g : GA D S) (h : GA D T) (t : WO S T), adjCo φ S T BS BT (actO S T g⁻¹ h⁻¹ t) = ((grpCo φ S BS g)⁻¹).val * adjCo φ S T BS BT t * (grpCo φ T BT h).val := by
  intro D S T ΛS ΛT hS hT v φ e he BS BT
  refine ⟨?_, fun g h t => adjCo_actO φ S T BS BT g h t⟩
  have hc := (_root_.GlobalTheory.PlaceCoord.isCoord_mapCo D S T ΛS ΛT hS hT v (conjProj φ) (cA D e) (isIdemOf_conjProj he) 1 1).1
  have h1 : ((S.gram⁻¹).map (incA D)).map (rdA φ) * (S.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : ((T.gram⁻¹).map (incA D)).map (rdA φ) * (T.gram.map (incA D)).map (rdA φ) = 1 := by
    rw [← Matrix.map_mul, gram_inv_mul, Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have hA : ((S.gram.map (incA D)).map (rdA φ) * BS.val) * ((BS⁻¹).val * ((S.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BS.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h1
  have hB : ((T.gram.map (incA D)).map (rdA φ) * BT.val) * ((BT⁻¹).val * ((T.gram⁻¹).map (incA D)).map (rdA φ)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc BT.val, Units.mul_inv, Matrix.one_mul]
    exact mul_eq_one_comm.1 h2
  convert isCoord_comp hc _ _ _ _ hA hB using 1
  funext t
  have ht : (((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ).map (rdA φ) =
      ((t : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (rdA (conjProj φ)))ᵀ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.transpose_apply, rdA_conjProj]
  simp only [adjCo, mapCo, Matrix.map_mul, ht, _root_.inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc]

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceLatticeStabilisersFixWeilVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensor

private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := by
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this

private theorem det_int {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) (g : GA D V)
    (h : ∀ y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)),
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E))) :
    finPart D (Formalism.L2.Theta.mt V g).det ∈ intAE D := by
  have hd : finPart D (Formalism.L2.Theta.mt V g).det = (finMat D.sp.cm.sig V.gram g).det :=
    RingHom.map_det (finPart D) (Formalism.L2.Theta.mt V g)
  rw [hd, GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.DetTranslate.det_mem_int D.host.F L _ hL.toIsLattice.fg hL.span_eq_top h

private theorem unram_detAt {D : D7} {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hL : Submodule.IsFullLattice D.host.E L) {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      (finMat D.sp.cm.sig V.gram g).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    {e : AE D} (he : e * e = e) {ε : AF D.host.F} (hs : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {χ : (AE D)ˣ →* Circle} (hχ : GlobalTheory.WeilParts.UnramAt ε χ) : χ (GlobalTheory.VecInv.detAt e he V g) = 1 := by
  refine hχ _ ?_ (GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g fun y hy => (h y).1 hy)) ?_
  · change _ * (e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) - 1
    linear_combination ((Formalism.L2.Theta.mt V g).det - 1) * hs
  · rw [← MonoidHom.map_inv]
    exact GlobalTheory.Mem.DetUnit.part_mem_intAE he (det_int hL g⁻¹ (GlobalTheory.LocalLatStab.inv_keeps V _ g h))


theorem splitVacuumFixed : ∀ D : D7, SplitVacuumFixed D := by
  intro D ψ S T χS χT om ΛS ΛT hW hS hT v hv uS uT f hf hvac k hk k' hk'
  obtain ⟨e, he, hb⟩ := hv
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.SplitIdem.evalV_singleV_same _ _ _, fun _ hw => GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw⟩
  have hb' : e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := hb
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  have s1 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * e = e := by
    rw [← hb']; linear_combination he.1 + he.2.1
  have s2 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) * cA D e = cA D e := by
    rw [← hb']; linear_combination he'.1 + he.2.1
  have sk := suppPl_emb S v k
  have sk' := suppPl_emb T v k'
  have kS := emb_keeps_latHat S hS.1.fg v hk
  have kT := emb_keeps_latHat T hT.1.fg v hk'
  have key := GlobalTheory.VacStabFixed.om_split_halves hW hS hT he (fun i j => by rw [hb']; exact sk i j)
    (fun i j => by rw [hb']; exact sk' i j)
    (fun u hu => ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (kS y).1 hy) (fun y hy => (kT y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (GlobalTheory.LocalLatStab.inv_keeps S _ _ kS)
        (GlobalTheory.LocalLatStab.inv_keeps T _ _ kT) u hu⟩)
    (GlobalTheory.VecInv.isDetAt_detAt e he.1 S _) (GlobalTheory.VecInv.isDetAt_detAt e he.1 T _) hf
    (fun u hu hh => hvac.2 e he u (GlobalTheory.VacStabFixed.half_mem_place hε s1 hu hh) hh)
    (fun u hu hh => hvac.2 _ he' u (GlobalTheory.VacStabFixed.half_mem_place hε s2 hu hh) hh)
  rwa [splitFacO, unram_detAt (selfDual_full S ΛS hS) kS he.1 s1 uT, unram_detAt (selfDual_full T ΛT hT) kT he.1 s1 uS,
    inv_one, mul_one, Circle.coe_one, one_smul] at key

end GlobalTheory.PlaceTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemLatticeCompletionOfSupportedPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_mem_lattice_completion_of_supported_places : ∀ (D : D7) (S : HSp D) (P : GlobalTheory.FinPl.Pl D → Prop) (L L' : GlobalTheory.FinPl.Lat S) (g : GA D S), g ∈ grpAt S P →
  (∀ y : Fin S.rank → AE D, y ∈ latV S L P → (mt S g - 1) *ᵥ y ∈ latV S L' P) →
  ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L, (Lev.finE S g).1 *ᵥ x - x ∈ Formalism.L2.Herm.hatL (F := D.host.F) L' := by
  first | exact @GlobalTheory.LatBridge.sub_mem_hatL | exact GlobalTheory.LatBridge.sub_mem_hatL | (intros; apply GlobalTheory.LatBridge.sub_mem_hatL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionSplitProductDatumIsPureTensor
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.PlaceTensor.SplitProduct.thetaAt_sum_isPure : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (ι : Type) (s : Finset ι) (v : ι → FinPl D) (a : ι → AE D), (∀ i ∈ s, IsSplitIdem D (a i) ∧ a i + cA D (a i) = idem D (.inl (v i))) → Set.InjOn v s → ∀ Φ : ι → WO S T → ℂ, (∀ i ∈ s, IsSBHalf (a i) (latO S T ΛS ΛT fun _ => True) (Φ i)) → ∀ (x : Place D → WO S T → ℂ) (f Ψ : WO S T → ℂ), (∀ i ∈ s, IsThetaAt ψ (symplO S T) (heisO ψ S T) (a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ (Φ i) (x (.inl (v i)))) → (∀ p, (∀ i ∈ s, p ≠ .inl (v i)) → x p = f₀) → (∀ t, IsHalf (∑ i ∈ s, a i) t → Ψ t = ∏ i ∈ s, Φ i (a i • t)) → (∀ t, ¬ IsHalf (∑ i ∈ s, a i) t → Ψ t = 0) → IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ i ∈ s, a i) (latO S T ΛS ΛT fun _ => True) 1 f₀ Ψ f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  exact GlobalTheory.PlaceTensor.SplitProduct.isPure_of_facts D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕
    (_root_.GlobalTheory.LocalPure.isPure_base_and_local D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ)
    (_root_.GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ).1
    (fun a h1 h2 h3 =>
      ⟨fun x y hx hy Tm hTm =>
        ((_root_.GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).1 x y hx hy).2 f₀ Tm hTm,
        (_root_.GlobalTheory.PlaceTensor.halfWaves_span D ψ S T ΛS ΛT (base_std hB) hB.2.2.1 hB.2.2.2.1 a h1 h2 h3).2⟩)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftDiagonalRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.DownApprox

open GlobalTheory.Grid GlobalTheory.ChainFr
open scoped ENNReal

variable {D : D7}

theorem jm_not {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm (fun j => !(ε j)) = -Formalism.REAL.Jm ε := by
  ext a b
  by_cases h : a = b
  · subst h
    cases hε : ε a <;> simp [Formalism.REAL.Jm, hε]
  · simp [Formalism.REAL.Jm, Matrix.diagonal_apply_ne _ h]

theorem gramAt_neg (V : HSp D) (τ : D.what₂.Tau) : gramAt D (neg V) τ = -gramAt D V τ := by
  ext i j
  simp [gramAt, neg_gram]

def negFr (N : Node D) : Fr (neg N.V) where
  ε τ j := !(N.M.ε τ j)
  fr := N.M.fr
  fr_unit := N.M.fr_unit
  fr_gram τ := by
    rw [jm_not, Matrix.mul_neg, Matrix.neg_mul, N.M.fr_gram τ, gramAt_neg]

theorem negFr_cart (N : Node D) : (negFr N).cart = cartS true N := by
  funext τ
  show (N.M.fr τ)⁻¹ * Formalism.REAL.Jm (fun j => !(N.M.ε τ j)) * N.M.fr τ = -((N.M.fr τ)⁻¹ * Formalism.REAL.Jm (N.M.ε τ) * N.M.fr τ)
  rw [jm_not, Matrix.mul_neg, Matrix.neg_mul]

theorem thetaKernel_le_sobolev_mul_height_source {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeil ψ true S T χS χT ω) (μ : Measure (WO (neg S) T))
    (𝓓 : Set (WO (neg S) T)) (hμ : IsCovolOne (ratL T (neg S)) μ 𝓓) (U : AddSubgroup (WO (neg S) T))
    (hU : IsOpen (U : Set (WO (neg S) T))) :
    ∃ (d A : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ (neg S) T U, ∀ (g : GA D S) (h : GA D T),
      ‖thetaKO ω g h f‖ ≤ K * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.quotHeight S g ^ A * GlobalTheory.Grow.height T h ^ A := by
  have hω' : IsWeilDatumO ψ (neg S) T χS χT (ω.toSgn true) := hω
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (neg S).rank T.rank
  obtain ⟨C, hC0, hC⟩ := (H (neg S) T rfl rfl).real ψ hθ hU
  refine ⟨d, A, C * 2 ^ A, by positivity, fun f hf g h => ?_⟩
  have hb := (hC χS χT (ω.toSgn true) hω' μ 𝓓 hμ f hf).2
  have hinv : ∀ γ ∈ GQ S, ∀ g, thetaKO ω (γ * g) h f = thetaKO ω g h f := fun γ hγ g => by
    have e1 : (((ofSgn true S).symm (γ * g), h) : GA D (neg S) × GA D T) =
        ((ofSgn true S).symm γ, 1) * ((ofSgn true S).symm g, h) := by simp
    show (ω.toSgn true) ((ofSgn true S).symm (γ * g), h) f 0 = (ω.toSgn true) ((ofSgn true S).symm g, h) f 0
    rw [e1, map_mul, Module.End.mul_apply]
    exact hω'.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) 1 (one_mem _) _ (hω'.om_pres _ _ hf.1)
  have hs : 0 ≤ (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal := ENNReal.toReal_nonneg
  have hgr : ∀ g, ‖thetaKO ω g h f‖ ≤ (C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * GlobalTheory.Grow.height T h ^ A) *
      GlobalTheory.Grow.height S g ^ A := fun g => by
    have := hb ((ofSgn true S).symm g) h
    refine this.trans_eq ?_
    show C * (GlobalTheory.Size.sobO ψ θ μ 𝓓 d f).toReal * (GlobalTheory.Grow.height S g * GlobalTheory.Grow.height T h) ^ A = _
    ring
  refine (GlobalTheory.Grow.norm_le_quotHeight_pow (f := fun g => thetaKO ω g h f) hinv hgr g).trans_eq ?_
  ring

theorem exists_sum_of_mem_fockSpan {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A : Fr V} {B : Fr W}
    {U : AddSubgroup (WO V W)} {g : WO V W → ℂ} (hg : g ∈ fockSpan ψ θ A B U) :
    ∃ (n : ℕ) (f : Fin n → (WO V W → ℂ)) (p : Fin n → PolF D W.rank V.rank),
      (∀ l, IsVacF ψ θ A B (f l)) ∧ g = ∑ l, ptF ψ θ A B (f l) (p l) := by
  obtain ⟨n, c, u, hu⟩ := Submodule.mem_span_set'.1 hg
  have hm : ∀ l, ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ GlobalTheory.Size.thetaLevel ψ V W U ∧ (u l : WO V W → ℂ) = ptF ψ θ A B f₀ P :=
    fun l => (u l).2
  choose f₀ P hv _ he using hm
  refine ⟨n, f₀, fun l => c l • P l, hv, ?_⟩
  rw [← hu]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [he l]
  exact (map_smul (pureTensorO ψ θ V W A.cart B.cart A.onb B.onb (f₀ l)) (c l) (P l)).symm

theorem isVacF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) :
    IsVacF ψ θ (negFr S) (Fr.ofModel T.M) f ↔ IsFinVec ψ θ true S T f := by
  unfold IsVacF IsFinVec
  rw [negFr_cart]
  rfl

theorem ptF_negFr {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (S T : Node D) (f : WO S.V T.V → ℂ) (P : Pol S T) :
    ptF ψ θ (negFr S) (Fr.ofModel T.M) f P = fock ψ θ true S T f P := by
  unfold ptF fock
  rw [negFr_cart]
  rfl


end GlobalTheory.DownApprox
end
end

