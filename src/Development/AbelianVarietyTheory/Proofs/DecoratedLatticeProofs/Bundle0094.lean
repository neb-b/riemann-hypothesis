module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianLinkMapAdditiveRationalEquivariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.LinkKappa

open GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule (ofAdj)

variable {D : D7}

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem finPart_conj (z : AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem map_ofAdj_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (hφ : ∀ z, φ z = 0 → φ (cA D z) = 0)
    (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z.map φ = 0) : (ofAdj L S z).map φ = 0 := by
  have h1 : (adj z).map φ = 0 := by
    funext i j
    exact hφ (z j i) (congrFun (congrFun hz j) i)
  have h2 := map_mul_eq_zero_right φ (giA S) (map_mul_eq_zero_left φ h1 (gA L))
  funext i j
  have h3 : φ ((giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0 := congrFun (congrFun h2 i) j
  show φ (incA D (-D.host.xi0⁻¹) * (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) i j) = 0
  rw [map_mul, h3, mul_zero]

theorem trace_mul_smul_middle_eq_smul_trace {R : Type} [CommRing R] {m n : ℕ} (c : R) (a : Matrix (Fin m) (Fin m) R)
    (b : Matrix (Fin m) (Fin n) R) (g : Matrix (Fin n) (Fin n) R) (y : Matrix (Fin n) (Fin m) R) :
    (a ⬝ (b ⬝ ((c • g) ⬝ y))).trace = c * (a ⬝ (b ⬝ (g ⬝ y))).trace := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]


set_option maxHeartbeats 1600000 in
theorem hO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (c : D.host.E)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = (c * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    hO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = incA D c * hO S L' y x := by
  have h : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ (rat τ : Mx D L.rank L'.rank)) =
      incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L' := by
    rw [gA, gA, ← rat_conjTranspose, ← rat_mul, ← rat_mul, ← rat_smul]; exact congrArg rat hτ
  have h' : adj (rat τ : Mx D L.rank L'.rank) ⬝ (gA L ⬝ ((rat τ : Mx D L.rank L'.rank) ⬝ y)) =
      (incA D (c * (D.host.xi0 * star D.host.xi0)) • gA L') ⬝ y := by
    rw [← h, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, ofAdj, ofAdj]
  simp only [adj_smul, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel, trace_smul, smul_eq_mul]
  rw [trace_mul_comm (rat τ : Mx D L.rank L'.rank), Matrix.mul_assoc y, trace_mul_comm y]
  simp only [Matrix.mul_assoc]
  rw [h']
  have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h1 : incA D c = incA D (-D.host.xi0⁻¹) *
      (cA D (incA D (-D.host.xi0⁻¹)) * incA D (c * (D.host.xi0 * star D.host.xi0))) := by
    rw [GlobalTheory.DualPairCheck.cA_incA, ← map_mul, ← map_mul]
    congr 1
    rw [star_neg, star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    field_simp
  have h2 := trace_mul_smul_middle_eq_smul_trace (R := AE D) (incA D (c * (D.host.xi0 * star D.host.xi0))) (giA S) (adj x) (gA L') y
  rw [h1, mul_assoc, mul_assoc]
  exact congrArg (fun t => incA D (-D.host.xi0⁻¹) * (cA D (incA D (-D.host.xi0⁻¹)) * t)) h2

theorem ofAdj_add (L S : HSp D) (z z' : Mx D L.rank S.rank) : ofAdj L S (z + z') = ofAdj L S z + ofAdj L S z' := by
  rw [ofAdj, ofAdj, ofAdj, adj_add, Matrix.add_mul, Matrix.mul_add, smul_add]

theorem continuous_ofAdj (L S : HSp D) : Continuous (ofAdj L S) := by
  have h1 : Continuous fun z : Mx D L.rank S.rank => (adj z ⬝ gA L : Mx D S.rank L.rank) :=
    continuous_adj.matrix_mul continuous_const
  have h2 : Continuous fun z : Mx D L.rank S.rank => (giA S ⬝ (adj z ⬝ gA L) : Mx D S.rank L.rank) :=
    continuous_const.matrix_mul h1
  exact h2.const_smul (incA D (-D.host.xi0⁻¹))

theorem ofAdj_mem (L S : HSp D) {z : Mx D L.rank S.rank} (hz : z ∈ ratMx D L.rank S.rank) :
    ofAdj L S z ∈ ratMx D S.rank L.rank :=
  ratMx_smul _ (ratMx_mul (rat_mem S.gram⁻¹) (ratMx_mul (ratMx_adj hz) (rat_mem L.gram)))

theorem mt_inv_ofAdj (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    mt S g⁻¹ ⬝ ofAdj L S z = ofAdj L S (z ⬝ mt S g) := by
  simp only [ofAdj, mt_inv, adj_mul, Matrix.mul_smul, Matrix.mul_assoc, gA_giA_cancel]

theorem ofAdj_mul_mt_inv (L S : HSp D) (g : GA D S) (z : Mx D L.rank S.rank) :
    ofAdj L S (z ⬝ mt S g⁻¹) = mt S g ⬝ ofAdj L S z := by
  rw [← mt_inv_ofAdj, inv_inv]

theorem symplO_ofAdj (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ)
    (hτ : τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram) (x y : WO S L') :
    symplO L S (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ x))
      (ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ y)) = -((ε : AF D.host.F) * symplO S L' x y) := by
  rw [symplO_eq, hO_ofAdj L L' S τ _ hτ, ← mul_neg, ← GlobalTheory.OrientedHeis.symplO_skew, symplO_eq, map_intCast,
    mul_left_comm, ← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]

theorem kappa_props : ∀ (D : D7) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E) (ε : ℤ), τᴴ ⬝ (L.gram ⬝ τ) = ((ε : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ κ : WO S L' → WO L S, (∀ w, κ w = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) → (∀ w w', κ (w + w') = κ w + κ w') ∧ Continuous κ ∧ (∀ w ∈ ratMx D L'.rank S.rank, κ w ∈ ratMx D S.rank L.rank) ∧ (∀ (g : GA D S) (w : WO S L'), κ (w ⬝ mt S g⁻¹) = mt S g ⬝ κ w) ∧ (∀ w w', symplO L S (κ w) (κ w') = -((ε : AF D.host.F) * symplO S L' w w')) ∧ (∀ w, (w.map (infPart D) = 0 → (κ w).map (infPart D) = 0) ∧ (w.map (finPart D) = 0 → (κ w).map (finPart D) = 0)) := by
  intro D L L' S τ ε hτ κ hκ
  refine ⟨fun w w' => ?_, ?_, fun w hw => ?_, fun g w => ?_, fun w w' => ?_, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · rw [hκ, hκ, hκ, ← ofAdj_add]
    exact congrArg (ofAdj L S) (Matrix.mul_add (rat τ : Mx D L.rank L'.rank) w w')
  · have h : Continuous fun w : Mx D L'.rank S.rank => ((rat τ : Mx D L.rank L'.rank) ⬝ w : Mx D L.rank S.rank) :=
      continuous_const.matrix_mul continuous_id
    rw [funext hκ]
    exact (continuous_ofAdj L S).comp h
  · rw [hκ]
    exact ofAdj_mem L S (ratMx_mul (rat_mem τ) hw)
  · rw [hκ, hκ, ← ofAdj_mul_mt_inv]
    exact congrArg (ofAdj L S) (Matrix.mul_assoc (rat τ : Mx D L.rank L'.rank) w (mt S g⁻¹)).symm
  · rw [hκ, hκ]
    exact symplO_ofAdj L L' S τ ε hτ w w'
  · rw [hκ]
    exact map_ofAdj_eq_zero (infPart D) (fun z hz => by rw [infPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (infPart D) _ hw)
  · rw [hκ]
    exact map_ofAdj_eq_zero (finPart D) (fun z hz => by rw [finPart_conj, hz, map_zero]) L S
      (map_mul_eq_zero_right (finPart D) _ hw)

end GlobalTheory.LinkKappa

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionCutIntegralProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl

theorem pairA_zero_mul_pairA_zero (F : Type) [Field F] [NumberField F] (a b : Af F) :
    pairA F 0 a * pairA F 0 b = pairA F 0 (a * b) := by
  show (((0 : Ainf F), a) * ((0 : Ainf F), b) : Ainf F × Af F) = ((0 : Ainf F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem pairA_zero_smul_tmul (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a b : Af F) (e : E) :
    pairA F 0 a • (pairA F 0 b ⊗ₜ[F] e : AF F ⊗[F] E) = pairA F 0 (a * b) ⊗ₜ[F] e := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, pairA_zero_mul_pairA_zero]

theorem infPart_pairA_zero_tmul (D : D7) (b : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0 := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (pairA D.host.F 0 b ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  have : fstA D.host.F (pairA D.host.F 0 b) = 0 := rfl
  rw [this, TensorProduct.zero_tmul]

theorem latO_algebra : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (u : WO S T), u ∈ latO S T LS LT P → (∀ γ ∈ intAf D.host.F, pairA D.host.F 0 γ • u ∈ latO S T LS LT (fun v => P v ∧ evalV D.host.F v γ ≠ 0)) ∧ pairA D.host.F 0 1 • u = u ∧ u.map (infPart D) = 0 ∧ ((∀ v, ¬ P v) → u = 0) := by
  intro D S T LS LT P u hu
  unfold latO at hu
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · refine AddSubgroup.subset_closure ⟨γ * α, fun v => ?_, fun v hv => ?_, a, ha, s, hs, t, ht, ?_⟩
      · rw [map_mul]
        exact mul_mem (hγ v) (hα v)
      · rw [map_mul]
        by_cases h : P v
        · have : evalV D.host.F v γ = 0 := by
            by_contra h'
            exact hv ⟨h, h'⟩
          rw [this, zero_mul]
        · rw [hP v h, mul_zero]
      · ext i j
        exact pairA_zero_smul_tmul _ _ _ _ _
    · ext i j
      have := pairA_zero_smul_tmul D.host.F D.host.E 1 α (a * t i * ∑ k, star (s k) * S.gram k j)
      rw [one_mul] at this
      exact this
    · ext i j
      exact infPart_pairA_zero_tmul D α _
    · have h0 : α = 0 := by
        apply RestrictedProduct.ext
        intro v
        exact hP v (h v)
      subst h0
      ext i j
      have : pairA D.host.F 0 0 = 0 := rfl
      show pairA D.host.F 0 0 ⊗ₜ[D.host.F] _ = (0 : AE D)
      rw [this, TensorProduct.zero_tmul]
  | zero =>
    refine ⟨fun γ _ => ?_, smul_zero _, ?_, fun _ => rfl⟩
    · rw [smul_zero]
      exact zero_mem _
    · ext i j
      exact map_zero (infPart D)
  | add x y _ _ hx hy =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_add]
      exact add_mem (hx.1 γ hγ) (hy.1 γ hγ)
    · rw [smul_add, hx.2.1, hy.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy.2.2.1 i) j
      show infPart D (x i j + y i j) = 0
      rw [map_add (infPart D), h1, h2, add_zero]
    · rw [hx.2.2.2 h, hy.2.2.2 h, add_zero]
  | neg x _ hx =>
    refine ⟨fun γ hγ => ?_, ?_, ?_, fun h => ?_⟩
    · rw [smul_neg]
      exact neg_mem (hx.1 γ hγ)
    · rw [smul_neg, hx.2.1]
    · ext i j
      have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx.2.2.1 i) j
      show infPart D (- x i j) = 0
      rw [map_neg, h1, neg_zero]
    · rw [hx.2.2.2 h, neg_zero]

end GlobalTheory.FinPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.SelfDualAt

variable {D : D7}


open Classical in
def indP (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
theorem evalV_indP (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (indP P) = if P v then 1 else 0 := rfl

def cP (P : Pl D → Prop) : AF D.host.F := pairA D.host.F 0 (indP P)

theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

theorem hO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = hO S T (c • x) y := by
  unfold hO
  simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring

theorem symplO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = symplO S T (c • x) y := by
  unfold symplO
  rw [hO_smul_swap]


set_option maxHeartbeats 800000 in
theorem compFin_repr (w : Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
        (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y) k =
      evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e := rfl
    rw [h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [RingHom.map_add (f := _), LinearEquiv.map_add (e := _), Finsupp.add_apply, hx, hy]
    exact (RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm

theorem eq_zero_of_compFin (y : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y = 0) :
    y = 0 := by
  have hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0 := by
    refine Finsupp.ext fun k => ?_
    have hk : ∀ w : Pl D, evalV D.host.F w
        ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := fun w => by
      rw [← compFin_repr, h w, map_zero]; rfl
    rw [Finsupp.zero_apply]
    refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
    exact hk w
  simpa using hr

set_option maxHeartbeats 800000 in
theorem compFin_alg_cP (P : Pl D → Prop) (w : Pl D) (hw : P w) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) (cP P))) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rfl
  rw [h, evalV_indP, if_pos hw]
  exact Algebra.TensorProduct.one_def.symm


set_option maxHeartbeats 800000 in
theorem algebraMap_placeIdempotent_mul (P : Pl D → Prop) (z : AE D) (hz : z ∈ idAt D P) :
    algebraMap (AF D.host.F) (AE D) (cP P) * z = z := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at hz
  obtain ⟨hinf, hfin⟩ := hz
  rw [RingHom.mem_ker] at hinf
  have h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0 := by
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · rw [RingHom.map_mul, hinf, mul_zero]
    · apply eq_zero_of_compFin
      intro w
      rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hw : P w
      · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]
      · have h1 := hfin ⟨w, hw⟩
        rw [RingHom.mem_ker] at h1
        rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at h0
  exact h0.symm

theorem smul_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (y : WO S T) (hy : y ∈ latO S T LS LT fun _ => True) : cP P • y ∈ latO S T LS LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩
    · intro v
      rw [map_mul]
      refine mul_mem ?_ (hα v)
      rw [evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro v hv
      rw [map_mul, evalV_indP, if_neg hv, zero_mul]
    · ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem latO_ann_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  intro D ψ hψ S T LS LT hS hT P u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hinf : u.map (infPart D) = 0 := by
    ext i j
    have h := (Ideal.mem_inf.1 (hu i j)).1
    rw [RingHom.mem_ker] at h
    simpa using h
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩
  have hfix : cP P • u = u := by
    ext i j
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact algebraMap_placeIdempotent_mul P _ (hu i j)
  constructor
  · intro hm u' hu'
    exact (key u hinf).1 (hle hm) u' (hle hu')
  · intro hann
    have h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1 := by
      intro y hy
      have h := hann _ (smul_mem_latO S T _ _ P y hy)
      rwa [symplO_smul_swap, hfix] at h
    rw [← hfix]
    exact smul_mem_latO S T _ _ P u ((key u hinf).2 h2)

end GlobalTheory.SelfDualAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticePlaceCutSmulMemOpenSubgroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatLevel


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
theorem exists_finset_of_nhds_zero {F : Type} [Field F] [NumberField F] (V : Set (Af F)) (hV : IsOpen V)
    (h0 : (0 : Af F) ∈ V) :
    ∃ s : Finset (HeightOneSpectrum (𝓞 F)), ∀ γ ∈ Formalism.MainNotions.StandardLattice.intAf F, (∀ v ∈ s, evalV F v γ = 0) → γ ∈ V := by
  set f := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite with hf
  have hc : Continuous f := (RestrictedProduct.isOpenEmbedding_structureMap
    (fun v => Valued.isOpen_integer _)).continuous
  have hO : IsOpen (f ⁻¹' V) := hV.preimage hc
  have hz : (0 : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) ∈ f ⁻¹' V := h0
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hO _ hz
  refine ⟨I, fun γ hγ hs => ?_⟩
  let x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨γ v, hγ v⟩
  have hx : x ∈ (I : Set _).pi u := by
    intro v hv
    have h1 : x v = 0 := Subtype.ext (hs v hv)
    rw [h1]
    exact (hu v hv).2
  have := hsub hx
  exact this

end GlobalTheory.LatLevel

namespace GlobalTheory.LatLevel

theorem smul_mem_open_of_vanish : ∀ (D : D7) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (P : Pl D → Prop) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ u ∈ latO S T LS LT P, ∃ s : Finset (Pl D), ∀ γ ∈ intAf D.host.F, (∀ v ∈ s, evalV D.host.F v γ = 0) → pairA D.host.F 0 γ • u ∈ U := by
  intro D S T LS LT P U hU u _hu
  letI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have hg : Continuous fun β : Af D.host.F => (pairA D.host.F 0 β) • u := by
    have h1 : Continuous fun β : Af D.host.F => pairA D.host.F 0 β :=
      continuous_const.prodMk continuous_id
    exact h1.smul continuous_const
  obtain ⟨s, hs⟩ := exists_finset_of_nhds_zero _ (hU.preimage hg)
    (by
      show pairA D.host.F 0 0 • u ∈ (U : Set (WO S T))
      have : pairA D.host.F 0 0 = 0 := rfl
      rw [this, zero_smul]
      exact U.zero_mem)
  exact ⟨s, fun γ hγ hv => hs γ hγ hv⟩

end GlobalTheory.LatLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem resEta_core {D : D7} {χ : (AE D)ˣ →* Circle} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)
    (h : ResEta D χ S.rank) : ResEta D χ S₀.rank :=
  resEta_parity h (by rw [← d.rank_add]; omega)

theorem descent_of_weilDatumExists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D → Descent D := by
  intro D hW ψ S T χS χT om h
  refine ⟨fun S₀ ρ d => ?_, fun T₀ ρ d => ?_⟩
  · exact hW S₀ T ψ χS χT h.std h.hecS h.hecT (resEta_core d h.resS) h.resT
  · exact hW S T₀ ψ χS χT h.std h.hecS h.hecT h.resS (resEta_core d h.resT)

end GlobalTheory.Unf

end
end

