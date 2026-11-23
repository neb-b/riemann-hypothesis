module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0268
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePiPointsAtInfinitePlacesCMTypeImage
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

section Conj

variable {k r : ℕ}

def cjm (M : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => star (M i j)

theorem cjm_cjm (M : Formalism.QuantumDeterminants.Mt k r) : cjm (cjm M) = M := by
  funext i j; simp [cjm]

theorem measurable_cjm : Measurable (cjm : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  unfold cjm; fun_prop

def cjmE : Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun := cjm
  invFun := cjm
  left_inv := cjm_cjm
  right_inv := cjm_cjm
  measurable_toFun := measurable_cjm
  measurable_invFun := measurable_cjm

theorem map_star_eq (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : X.map star = Xᴴᵀ := by
  ext i j; simp

theorem exp_map_star (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (X.map star) = (NormedSpace.exp X).map star := by
  rw [map_star_eq, map_star_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

theorem Hpk_map_star : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem map_star_mem_N {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.Nset k r) : g.map star ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · have h1' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := h1
    show (g.map star)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g.map star = Formalism.QuantumDeterminants.Hpk k r
    have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M.map star = M.map (starRingEnd ℂ) := by
      intro M; rfl
    have hc : (g.map star)ᴴ = gᴴ.map star := by ext i j; simp
    rw [hc, ← Hpk_map_star, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, h1']
  · simp only [Matrix.map_apply, h2 a i hi]; split_ifs <;> simp
  · simp only [Matrix.map_apply, h3 i j a b c]; split_ifs <;> simp

end Conj

section Conj2
variable {k r : ℕ}

def cjR (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := (WithLp.equiv 2 _).symm (realifyFun ((unrealify x).map star))
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify]

theorem unrealify_realify' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  simp [unrealify, realifyFun]

theorem unrealify_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (cjR m x) = (unrealify x).map star := unrealify_realify' _

theorem norm_sq_unrealify' {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

theorem norm_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖cjR m x‖ = ‖x‖ := by
  have : ‖cjR m x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_unrealify', norm_sq_unrealify', unrealify_cjR]
    simp only [Matrix.map_apply, norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

theorem cjR_mem {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) : ∀ x ∈ lieE S, cjR (2 * r + k + 1) x ∈ lieE S := by
  intro x hx
  have : lieE S ≤ (lieE S).comap (cjR (2 * r + k + 1)) := by
    unfold lieE
    rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.subset_span ⟨X.map star, fun t => ?_, ?_⟩
    · have e : ((t : ℂ) • X.map star) = ((t : ℂ) • X).map star := by
        ext i j; simp
      rw [e, exp_map_star]; exact hS _ (hX t)
    · show _ = (WithLp.equiv 2 _).symm (realifyFun ((unrealify _).map star))
      rw [unrealify_realify']
  exact this hx

theorem norm_cjR_restrict {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (x : lieE S) :
    ‖(cjR (2 * r + k + 1)).restrict (cjR_mem hS) x‖ = ‖x‖ := by
  show ‖cjR (2 * r + k + 1) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
    ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖
  exact norm_cjR _

theorem haarLie_map_cjm {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (κ : ENNReal) : (haarLie S κ).map (cjmE (k := k) (r := r)) = haarLie S κ := by
  unfold haarLie
  rw [Measure.map_smul κ (cjmE (k := k) (r := r)).measurable.aemeasurable]
  congr 1
  set E : lieE S → Formalism.QuantumDeterminants.Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE
  by_cases hm : AEMeasurable E volume
  · let Φ₀ : lieE S →ₗᵢ[ℝ] lieE S := ⟨(cjR (2 * r + k + 1)).restrict (cjR_mem hS), norm_cjR_restrict hS⟩
    let Φ : lieE S ≃ₗᵢ[ℝ] lieE S := Φ₀.toLinearIsometryEquiv rfl
    have hΦ := Φ.measurePreserving
    have e : (cjmE (k := k) (r := r)) ∘ E = E ∘ Φ := by
      funext x
      show cjm (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) =
        fun i j => NormedSpace.exp (unrealify (cjR (2 * r + k + 1) x)) i j
      rw [unrealify_cjR, exp_map_star]
      rfl
    rw [AEMeasurable.map_map_of_aemeasurable (cjmE (k := k) (r := r)).measurable.aemeasurable hm, e,
      ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]
  · exfalso
    apply hm
    have hu : Continuous (unrealify : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      have he : (fun x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) => unrealify x i j) =
          fun x => ((x (i, j, false) : ℝ) : ℂ) + ((x (i, j, true) : ℝ) : ℂ) * Complex.I := by
        funext x
        apply Complex.ext <;> simp [unrealify]
      rw [he]
      fun_prop
    have hexp : Continuous (NormedSpace.exp : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
      open scoped Norms.Operator in exact NormedSpace.exp_continuous
    apply Measurable.aemeasurable
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact ((continuous_apply j).comp ((continuous_apply i).comp
      (hexp.comp (hu.comp continuous_subtype_val)))).measurable

end Conj2

section Places

variable (D : D7)

def plE : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective (fun τ => InfinitePlace.mk (embS D τ))
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))

theorem plE_tauOf (w : InfinitePlace D.host.E) : plE D (tauOf D w) = w :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_eq (w : InfinitePlace D.host.E) : tauOf D w = (plE D).symm w := by
  rw [Equiv.eq_symm_apply, plE_tauOf]

def cjwE (w : InfinitePlace D.host.E) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then MeasurableEquiv.refl _ else cjmE

theorem cjwE_apply (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : cjwE D w M = cjw D w M := by
  unfold cjwE cjw
  split_ifs <;> rfl

def GmE : (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) ≃ᵐ (InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)).trans
    (MeasurableEquiv.piCongrRight (fun w => cjwE D w))

theorem coe_GmE : ⇑(GmE D) = Gm D := by
  funext y w
  show cjwE D w ((MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)) y w) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, cjwE_apply, Gm, tauOf_eq, eq_rec_constant]

theorem cjwE_mp (w : InfinitePlace D.host.E) :
    MeasurePreserving (cjwE D w) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  unfold cjwE
  split_ifs
  · exact MeasurePreserving.id _
  · exact ⟨(cjmE).measurable, haarLie_map_cjm (fun g hg => map_star_mem_N hg) 1⟩

theorem GmE_mp : MeasurePreserving (GmE D)
    (Measure.pi fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (Measure.pi fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) :=
    (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1
  have h1 := measurePreserving_piCongrLeft (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (plE D)
  have h2 := measurePreserving_pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (cjwE_mp D)
  exact h2.comp h1

end Places

theorem measure_Gm_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) =
      Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  intro D S
  rw [← coe_GmE, MeasurableEquiv.image_eq_preimage_symm, ← MeasurableEquiv.map_apply, (GmE_mp D).symm.map_eq]

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold

def FlagPairStabilizer {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T') :
    Subgroup (GV D) where
  carrier := H0 F F'
  one_mem' := ⟨Subgroup.one_mem _, fun _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun i => ?_, fun i => ?_⟩
    · show a (b _) = _
      rw [hb1, ha1]
    · show a (b _) = _
      rw [hb2, ha2]
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    refine ⟨Subgroup.inv_mem _ ha, fun i => ?_, fun i => ?_⟩
    · conv_lhs => rw [← ha1 i]
      show a.symm (a _) = _
      simp
    · conv_lhs => rw [← ha2 i]
      show a.symm (a _) = _
      simp

theorem mem_H0sub {D : D7} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F' : LFlag (D.sp.Y 0) D.R.rS T')
    (h : GV D) : h ∈ FlagPairStabilizer F F' ↔ h ∈ H0 F F' := Iff.rfl

end GlobalTheory.Unfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangular
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.LocCong

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : GlobalTheory.HL.Places F E sig) {N r : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (B : Fin (r + 1) → E) (v : Fin (r + 1) → Fin N → E) :
    A.bc p (∑ a, B a • v a) = ∑ a, (A.loc p).ιE (B a) • A.bc p (v a) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [GlobalTheory.HL.Places.bc, Finset.sum_apply, map_sum, smul_eq_mul]

theorem loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMov n m hn hm hgm hterm P hP
  obtain ⟨d, hlat, hloc⟩ := hterm
  obtain ⟨B, B', hB1, hB2, hB1', hB2', hBB⟩ := _root_.GlobalTheory.MovedFrames.moved_frames D X Y u u' F00 F'0 t₀ ρ U U' hMov n m hn hm
  have hc1 := _root_.GlobalTheory.HL.GCoord.c_eq_one_of_gS_mem D X Y F00 F'0 FP G c P hP
  have hSf : ∀ a, (G.S (below D P)).f a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f a) := by
    intro a
    have := G.f_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hSf' : ∀ a, (G.S (below D P)).f' a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f' a) := by
    intro a
    have := G.f'_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hfr : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b = (n⁻¹ * t₀.lin * m) (frame (lf D (X.Fu u')) b) := by
    intro b
    unfold mapLF
    rw [dite_eq_left hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(n⁻¹ * t₀.lin * m)) _ _) b).symm
  have hyin : ∀ a, frame (lf D (X.Fu u)) a ∈ t₀.lam := fun a => _root_.GlobalTheory.RowFrame.frame_mem_rows D X Y u t₀.lam t₀.mem a
  have hxin : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b ∈ t₀.lam := by
    intro b
    rw [hfr b, ← hgm]
    exact Submodule.mem_map_of_mem (_root_.GlobalTheory.RowFrame.frame_mem_rows D X Y u' t₀.lam' t₀.mem' b)
  have hy : ∀ b, c.e ((ρ * n) (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • G.f a := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.mul_apply, (hBB b).1, map_sum]
    simp only [map_smul, c.f_eq]
  have hx : ∀ b, c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • G.f' a := by
    intro b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.mul_apply, (hBB b).2, map_sum]
    simp only [map_smul, c.f'_eq]
  have hmemc : ∀ v ∈ t₀.lam, c.e ((ρ * n) v) ∈ c.lat (ρ * n) t₀.lam := fun v hv =>
    Submodule.mem_map.2 ⟨v, hv, rfl⟩
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  obtain ⟨ξp, hξO, hξ1, hξ2, hξT⟩ := _root_.GlobalTheory.HL.FrameChange.frames_congr _ D.R.rS D.R.k (G.S (below D P)) (d (below D P))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (c.lat (ρ * n) t₀.lam)) (hloc (below D P))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (lf D (X.Fu u)) b))))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))))
    (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B a b)) (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B' a b))
    (fun a b h => by simp [hB1 a b h]) (fun a => by simp [hB2 a])
    (fun a b h => by simp [hB1' a b h]) (fun a => by simp [hB2' a])
    (fun b => by simp only [hy, bc_sum, hSf])
    (fun b => by simp only [hx, bc_sum, hSf'])
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => Submodule.subset_span ⟨_, hmemc _ (hxin b), rfl⟩)
  have hfg : (c.lat (ρ * n) t₀.lam).FG := hlat.fg
  have hpos : 0 < Formalism.MainNotions.S.Lat.gS D := by
    unfold Formalism.MainNotions.S.Lat.gS
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.T.exists_global_unitriangular_of_local_congruence (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ D.R.rS (c.lat (ρ * n) t₀.lam) hfg
    (Formalism.MainNotions.S.Lat.gS D) hpos (below D P)
    (fun b => c.e ((ρ * n) (frame (lf D (X.Fu u)) b)))
    (fun b => c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))) ξp hξO hξ1 hξ2
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => (_root_.GlobalTheory.HL.ThetaG.inTh_lat_iff D X Y F00 F'0 FP G c P hP (c.lat (ρ * n) t₀.lam) _).1 (hξT b))
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  set v := frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b with hv
  have hφ : c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) -
      ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • c.e ((ρ * n) (frame (lf D (X.Fu u)) a)) = c.e ((ρ * n) v) := by
    rw [hv, map_sub, map_sub]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [frameAct, map_sum, map_smul]
  rw [hφ] at h
  have hmap : Ideal.span {((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • c.lat (ρ * n) t₀.lam =
      (Ideal.span {((Formalism.MainNotions.S.Lat.gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam).map
        ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
    unfold GCoord.lat
    rw [Submodule.map_smul'']
  rw [hmap] at h
  obtain ⟨s, hs, hsv⟩ := h
  refine ⟨s, hs, ?_⟩
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hinj : Function.Injective ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) :=
    ((ρ * n).trans c.e).injective
  have : z = s • v := by
    apply hinj
    rw [hzv, LinearMap.map_smul]
    rfl
  rw [← this]
  exact hz

end GlobalTheory.HL.LocCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NsubCocompact
section
noncomputable section

namespace GlobalTheory.UnipFlagCore

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Matrix
open scoped TensorProduct ENNReal

theorem mem_spanR_iff {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] {n r : ℕ}
    (e : Fin r → Fin n → E) (s : Set (Fin r)) (w : Fin n → R ⊗[F] E) :
    w ∈ spanR (F := F) R e s ↔
      ∃ c : Fin r → R ⊗[F] E, (∀ b, b ∉ s → c b = 0) ∧ w = ∑ b, c b • ratTup (F := F) R e b := by
  classical
  constructor
  · intro hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨Pi.single a 1, fun b hb => ?_, ?_⟩
      · exact Pi.single_eq_of_ne (by rintro rfl; exact hb ha) _
      · rw [Finset.sum_eq_single a]
        · simp only [Pi.single_eq_same, one_smul]; rfl
        · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
        · simp
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun b hb => by simp [hc b hb, hd b hb], ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul t x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨t • c, fun b hb => by simp [hc b hb], ?_⟩
      simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : b ∈ s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · rw [hc b hb, zero_smul]; exact Submodule.zero_mem _

theorem hE_swap {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) : hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ.1 j i]; ring

theorem nsub_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r) (T : F),
    P.IsStd σ J T → ∃ K : Set (Nsub (AF F) σ J P), IsCompact K ∧
      ∀ m : Nsub (AF F) σ J P, ∃ γ ∈ ratOf (K := Nsub (AF F) σ J P), ∃ k ∈ K, m = γ * k := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP
  have hσ := conj_invol hCM
  obtain ⟨h0, -, hef, -, -, -, -⟩ := hP
  have he : LinearIndependent E P.e := linearIndependent_of_dual P.e P.f fun a b => by
    rw [hE_swap hσ hJ (P.e b) (P.f a), hef]
    split_ifs with h1 h2 h2
    · simp
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  have hlin : ∀ (g : HA (AF F) σ J) (x : Fin n → AF F ⊗[F] E),
      lin (AF F) σ J g x - x = ((HA.mat _ σ J g).1 - 1) *ᵥ x := fun g x => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; rfl
  obtain ⟨K, hK, hm⟩ := cocompact_of_mem_iff_adelic hσ hJ P.e he h0 (Nsub (AF F) σ J P) fun g => by
    refine and_congr (forall_congr' fun a => ?_) (forall_congr' fun x => imp_congr Iff.rfl ?_)
    · have := mem_spanR_iff (F := F) (AF F) P.e {b | b < a} (lin (AF F) σ J g (ratV (F := F) (AF F) (P.e a)) - ratV (F := F) (AF F) (P.e a))
      rw [this, hlin]
      simp only [Set.mem_setOf_eq, not_lt]
      rfl
    · have := mem_spanR_iff (F := F) (AF F) P.e Set.univ (lin (AF F) σ J g x - x)
      rw [this, hlin]
      simp only [Set.mem_univ, not_true_eq_false, false_imp_iff, implies_true, true_and]
  refine ⟨K, hK, fun m => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hm m
  exact ⟨γ, hγ, k, hk, rfl⟩

end GlobalTheory.UnipFlagCore
end
end

