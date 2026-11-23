module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0281
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineAndJumps
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TateDualCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

section Local

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem fracInv_of_tied (T : LocTied l P AI) (K : FinExt l) : FracInv (P.PD K) := by
  intro x y hx h
  refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem lineUnit_of_tied (T : LocTied l P AI) (K : FinExt l) : LineUnit (P.PD K) := by
  intro b hb h
  refine (_root_.GlobalTheory.MemLoc.tied_regular_and_onto l P AI T).1 K b hb fun g hg => ?_
  obtain ⟨x, hx⟩ := h ⟨g, hg⟩
  exact ⟨x, by rw [← P.PD_actB K ⟨g, hg⟩, hx, Algebra.smul_def]⟩

theorem matRep_apply {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x : Fin k → L) : matRep M g x = (M g).mulVec x := rfl

theorem dot_dual {L Γ : Type} [CommRing L] [Group Γ] {k : ℕ} (M : Γ →* Matrix (Fin k) (Fin k) L)
    (g : Γ) (x y : Fin k → L) : (M g).mulVec x ⬝ᵥ (M g⁻¹).transpose.mulVec y = x ⬝ᵥ y := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]

theorem tateDual (T : LocTied l P AI) (K LL : FinExt l)
    (hs : Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1) {k : ℕ}
    (M M' : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)
    (hM : ∀ g, M' g = ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose)
    (hc : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep M') ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      multV (P.PD K) (matRep M') τ a = multV (P.PD K) (matRep M) τ (-a - 1) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  constructor
  · have h1 : IsCrys (P.PD K) (matRep (dualM M)) := by
      refine subCrys (P.PD K) ↥LL.1 hf _ _ _ _ (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap ?_
        (dotProductEquiv ↥LL.1 (Fin k)).injective (dualCrys (P.PD K) ↥LL.1 hf hu _ _ hc)
      intro g x
      refine LinearMap.ext fun y => ?_
      change (M g⁻¹).transpose.mulVec x ⬝ᵥ y = x ⬝ᵥ (M g⁻¹).mulVec y
      rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
    refine GlobalTheory.TwistCrys.isCrys_twist (P.PD K) (tensorCrys (P.PD K) ↥LL.1 hf hu)
      (quotCrys (P.PD K) ↥LL.1 hf hu) (matRep (dualM M)) (matRep M')
      (WeaklyAdmissibleFiltrations.charRep (cycLL (P.PD K) ↥LL.1 ^ (1 : ℤ))) (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1))
      LinearMap.id 1 rfl (fun g x => ?_) (fun g x => ?_)
      (GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI T K LL 1).1 h1
    · rw [zpow_one]; rfl
    · rw [matRep_apply, hM, Matrix.smul_mulVec]; rfl
  · intro τ a
    have h := (GlobalTheory.DRDual.twisted_dual_deRham l P AI T K LL _ (matRep M) _ (matRep M')
      (dotProductEquiv ↥LL.1 (Fin k)).toLinearMap 1 (dotProductEquiv ↥LL.1 (Fin k)).bijective
      (fun g x y => by
        change (M g).mulVec x ⬝ᵥ (M' g).mulVec y = _ * (x ⬝ᵥ y)
        rw [hM, Matrix.smul_mulVec, dotProduct_smul, dot_dual, zpow_one, smul_eq_mul])
      (GlobalTheory.T.isDeRham_of_isCrystalline_span l P AI T K LL _ _ hc).1).2 τ (-a - 1) hs
    rwa [show -(-a - 1) - 1 = a by ring] at h

def sumRep {L Γ : Type} [CommRing L] [Group Γ] {m k : ℕ} (M : Fin m → (Γ →* Matrix (Fin k) (Fin k) L)) :
    Representation L Γ (Fin m → Fin k → L) where
  toFun g := LinearMap.pi fun a => matRep (M a) g ∘ₗ LinearMap.proj a
  map_one' := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun a => ?_
    simp

theorem isCrys_of_isSubOfSums (T : LocTied l P AI) (K LL : FinExt l) {ι : Type} {k : ℕ}
    (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (hc : ∀ x, IsCrys (P.PD K) (matRep (Ms x)))
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    (h : IsSubOfSums ρ (fun x g => Ms x g)) : IsCrys (P.PD K) ρ := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have hf := fracInv_of_tied T K
  have hu := lineUnit_of_tied T K
  obtain ⟨m, xs, j, hj, he⟩ := h
  refine subCrys (P.PD K) ↥LL.1 hf _ (sumRep fun a => Ms (xs a)) _ ρ j (fun g v => he g v) hj ?_
  rw [isCrys_iff_span (P.PD K) hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  rw [← Finset.univ_sum_single v, TensorProduct.tmul_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  refine tmul_mem_span (P.PD K) (ρ := matRep (Ms (xs a)))
    (f := LinearMap.single ↥LL.1 (fun _ : Fin m => Fin k → ↥LL.1) a) (fun g x => ?_)
    ((isCrys_iff_span (P.PD K) hf hu _).1 (hc _)) b (v a)
  funext a'
  change Pi.single (M := fun _ => Fin k → ↥LL.1) a (matRep (Ms (xs a)) g x) a' =
    matRep (Ms (xs a')) g (Pi.single (M := fun _ => Fin k → ↥LL.1) a x a')
  by_cases ha : a' = a
  · subst ha; simp
  · simp [ha]

end Local

theorem loc_rDuO (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (g : Br.G D.nbr i w hw) :
    mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g =
      ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) •
        (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)) g⁻¹).transpose := by
  have h1 : ((cycLL (Br.PD D.loc D.nbr i w hw) ↥LL'.1 g : (↥LL'.1)ˣ) : ↥LL'.1) =
      IntermediateField.inclusion h
        ((Br.locChi D.nbr i w hw (epsU D.nd i) g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) := by
    rw [GlobalTheory.CycBridge.locChi_epsU]
    exact ((IntermediateField.inclusion h).commutes _).symm
  rw [h1]
  let F : D.nd.O i →+* ↥LL'.1 := (IntermediateField.inclusion h).toRingHom.comp
    ((algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))).comp (D.nbr i w hw).eO.toRingHom)
  let γ : Br.G D.nbr i w hw →* GE D.nd := (decS D.nd w).comp (Br.ι (D.nbr i w hw))
  ext a b
  congr 1
  change F (((chiU D.nd i 1 (γ g) * epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g)⁻¹ b a) =
    F ((epsU D.nd i (γ g) : (D.nd.O i)ˣ) : D.nd.O i) *
      F ((((chiU D.nd i 1 (γ g⁻¹))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * rO D.nd i r x (γ g⁻¹) b a)
  rw [map_inv γ, map_inv (chiU D.nd i 1), inv_inv, ← map_mul, Units.val_mul]
  congr 1
  ring

theorem crystalline_and_jumps : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocTied (D.nd.l i) (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) → ∀ (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x))))) → (∀ (V : Type) [AddCommGroup V] [Module ↥LL'.1 V] [Module ℚ_[D.nd.l i] V] [IsScalarTower ℚ_[D.nd.l i] ↥LL'.1 V] [FiniteDimensional ↥LL'.1 V] (ρ₁ : Representation ↥LL'.1 (Br.G D.nbr i w hw) V), IsSubOfSums ρ₁ (fun x g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rDuO D.nd i r x)) g) → IsCrys (Br.PD D.loc D.nbr i w hw) ρ₁ ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), IsJumpV (Br.PD D.loc D.nbr i w hw) ρ₁ τ' a → ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)) ∧ ∀ π, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e) → (∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' a ≤ 1) → IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) ∧ ∀ (τ' : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) (a : ℤ), ((IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 1) ∧ (¬ (IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ∧ ¬ (0 ≤ -a - 1 ∧ -a - 1 < (D.R.t : ℤ))) → multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)))) τ' a = 0) := by
  intro D i w hw T LL' h r ρ hc
  have hs : Nat.card (↥(D.nbr i w hw).Kw.1 →ₐ[ℚ_[D.nd.l i]] ↥LL'.1) =
      Module.finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 := by
    have := (D.nbr i w hw).Kw.2
    have := LL'.2
    have h1 := (GlobalTheory.splits_of_conjugates_mem _ (D.nbr i w hw).Kw LL' (fun τ x => h
      ((D.nbr i w hw).LL_split τ x)) inferInstance).2
    rw [Nat.card_eq_fintype_card, h1]
  have hd := fun x => tateDual T (D.nbr i w hw).Kw LL' hs _ _ (loc_rDuO D i w hw LL' h r x) (hc x)
  have hj := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero _ _ _ T (D.nbr i w hw).Kw LL'
  refine ⟨fun V _ _ _ _ _ ρ₁ hsub => ⟨isCrys_of_isSubOfSums T (D.nbr i w hw).Kw LL' _
    (fun x => (hd x).1) V ρ₁ hsub, fun τ' a ha => ?_⟩, fun π hπ hle => ?_⟩
  · refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (Br.PD D.loc D.nbr i w hw) ρ₁ _ τ'
      {a | ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r x)))) τ' (-a - 1)} hsub (fun x b hb => ⟨x, ?_⟩) a ha
    refine (hj _ _ τ' _).2.2.2 ?_
    rw [← (hd x).2]
    exact (hj _ _ τ' _).2.2.1 hb
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.crystalline_summand_and_dual_from_inverse_character_twist D i w hw T LL' h r ρ π hπ
    obtain ⟨-, -, h3⟩ := h2 (GlobalTheory.T.isDeRham_of_isCrystalline_span _ _ _ T (D.nbr i w hw).Kw LL' _ _ (hc π)).1
    refine ⟨(h1 (hc π)).2, fun τ' a => ?_⟩
    have e1 := (h3 τ' a).2
    have e2 := (h3 τ' (-a - 1)).1
    have e3 := hle τ' (-a - 1)
    have e4 : 0 ≤ multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
      (Br.loc D.nbr i w hw (WpO D.nd i ρ π)))) τ' (-a - 1) := (hj _ _ τ' _).2.1
    have e5 : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ↔
      multV (Br.PD D.loc D.nbr i w hw) (matRep (mapM (IntermediateField.inclusion h).toRingHom
        (Br.loc D.nbr i w hw (rTwO D.nd i r π)))) τ' (-a - 1) ≠ 0 := (hj _ _ τ' _).2.2
    rw [e5, e1]
    split_ifs at e2 with hh <;> omega

end GlobalTheory.TateDualCrys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeBasisSpanInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrisCoord

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : Type} [CommRing B] [Algebra F B] {d : ℕ}

def crd (bV : Module.Basis (Fin d) F V) (r : Fin d) : V ⊗[F] B →ₗ[F] B :=
  (TensorProduct.lid F B).toLinearMap ∘ₗ TensorProduct.map (bV.coord r) LinearMap.id

theorem crd_tmul (bV : Module.Basis (Fin d) F V) (r : Fin d) (v : V) (x : B) :
    crd bV r (v ⊗ₜ[F] x) = bV.coord r v • x := by
  simp [crd]

theorem crd_mulLeft (bV : Module.Basis (Fin d) F V) (r : Fin d) (β : B) (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map (LinearMap.id : V →ₗ[F] V) (LinearMap.mulLeft F β) z) =
      β * crd bV r z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x => simp [crd_tmul, mul_smul_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, mul_add]

theorem crd_map (bV : Module.Basis (Fin d) F V) (r : Fin d) (f : V →ₗ[F] V) (σ : B →ₗ[F] B)
    (z : V ⊗[F] B) :
    crd bV r (AlgebraTensorModule.map f σ z) =
      ∑ s, LinearMap.toMatrix bV bV f r s • σ (crd bV s z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v x =>
    have h := congrFun (LinearMap.toMatrix_mulVec_repr bV bV f v) r
    simp only [Matrix.mulVec, dotProduct] at h
    simp only [AlgebraTensorModule.map_tmul, crd_tmul, Module.Basis.coord_apply, map_smul, smul_smul]
    rw [← Finset.sum_smul, ← h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add, Finset.sum_add_distrib]

theorem crd_basis (bV : Module.Basis (Fin d) F V) (r j : Fin d) :
    crd bV r ((bV j) ⊗ₜ[F] (1 : B)) = if r = j then 1 else 0 := by
  rw [crd_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
  by_cases h : r = j
  · subst h; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm h), if_neg h, zero_smul]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

variable {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
  [IsScalarTower ℤ_[l] ℚ_[l] V] {d : ℕ}

theorem linIndep_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) :
    LinearIndependent ℚ_[l] (fun i => (b i : V)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]]
  exact b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)

theorem sum_lat (T : Submodule ℤ_[l] V) (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) :
    (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • (b i : V) := by
  have h := congrArg T.subtype (b.sum_repr w)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at h
  simp only [map_smul, Submodule.subtype_apply] at h
  simp only [algebraMap_smul]
  exact h.symm

theorem span_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
  rw [← hT]
  refine Submodule.span_le.mpr fun x hx => ?_
  rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, sum_lat T b]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def bVL (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) : Module.Basis (Fin d) ℚ_[l] V :=
  Module.Basis.mk (linIndep_lat T b) (span_lat T hT b)

theorem bVL_apply (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (i : Fin d) : bVL T hT b i = (b i : V) := by
  simp [bVL]

theorem repr_lat (T : Submodule ℤ_[l] V) (hT : Submodule.span ℚ_[l] (T : Set V) = ⊤)
    (b : Module.Basis (Fin d) ℤ_[l] T) (w : T) (r : Fin d) :
    (bVL T hT b).repr (w : V) r = algebraMap ℤ_[l] ℚ_[l] (b.repr w r) := by
  have h : (w : V) = ∑ i, (algebraMap ℤ_[l] ℚ_[l] (b.repr w i)) • bVL T hT b i := by
    simp only [bVL_apply]; exact sum_lat T b w
  rw [h, Module.Basis.repr_sum_self]

end GlobalTheory.CrisCoord

namespace GlobalTheory.CrisCoord

theorem toMatrix_lat {l : ℕ} [Fact l.Prime] {G : Type} [Group G] {V : Type} [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] G V}
    (L : Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] L.T) (g : G) (r s : Fin d) :
    LinearMap.toMatrix (bVL L.T L.span b) (bVL L.T L.span b) (ρ g) r s =
      algebraMap ℤ_[l] ℚ_[l] (LinearMap.toMatrix b b (actT L g) r s) := by
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, bVL_apply, ← repr_lat L.T L.span b]
  rfl

theorem lattice_basis_span_invariants : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), ∀ j : Fin d, ∃ (m : ℕ) (c : Fin m → Per.Bcris l) (v : Fin m → Fin d → Per.Bcris l), (∀ i (g : ↥(GK K)), ((LinearMap.toMatrix b b (actT L g)).map (Per.zB l)).mulVec (fun r => Per.σB (g : GQ l) (v i r)) = v i) ∧ (Pi.single j 1 : Fin d → Per.Bcris l) = ∑ i, c i • v i := by
  intro l _ K P AI T V _ _ _ _ _ ρ L hC d b j
  obtain ⟨m, β, δ, hδ, hy⟩ :=
    _root_.GlobalTheory.Per.RatSpan.crisSpan_rat l P AI T K V ρ hC ((bVL L.T L.span b j) ⊗ₜ[ℚ_[l]] (1 : P.R.B))
  refine ⟨m, fun i => T.eB (β i), fun i r => T.eB (crd (bVL L.T L.span b) r (δ i)), ?_, ?_⟩
  · intro i g
    have hinv : actVB (P.PD K) ρ g (δ i) = δ i := by
      have h := hδ i
      simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at h
      exact h g
    funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hinv
    beta_reduce
    rw [← key, actVB, crd_map]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [toMatrix_lat, Algebra.smul_def, map_mul, PadicInt.algebraMap_apply, T.zB]
    congr 1
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
      AlgHom.coe_coe]
    rw [← T.actB]
    congr 1
    exact (P.PD_actB K g _).symm
  · funext r
    have key := congrArg (fun z => T.eB (crd (bVL L.T L.span b) r z)) hy
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, crd_mulLeft, crd_basis, map_mul] at key
    beta_reduce
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← key]
    by_cases h : r = j
    · subst h; simp
    · simp [h]

end GlobalTheory.CrisCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBlochKatoCocycleOfCrysDeRhamPair
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundDel

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

lemma actVB_tmul' (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := rfl

lemma actVdR_tmul' (g : G) (v : V) (b : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actdR g b := rfl

lemma φVB_tmul' (v : V) (b : B) :
    φVB PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.φ b := rfl

lemma ιV_tmul' (v : V) (b : B) :
    ιV PD (LL := LL) (V := V) (v ⊗ₜ[Qp] b) = v ⊗ₜ[Qp] PD.ι b := rfl

lemma φVB_actVB' (g : G) (x : V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', φVB_tmul', φVB_tmul', actVB_tmul', PD.φ_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma ιV_actVB' (g : G) (x : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (actVB PD ρ g x) = actVdR PD ρ g (ιV PD (LL := LL) (V := V) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => rw [actVB_tmul', ιV_tmul', ιV_tmul', actVdR_tmul', PD.ι_comm]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b =>
    rw [actVB_tmul', actVB_tmul', actVB_tmul', map_mul, map_mul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma actVdR_mem_FilV' (g : G) (a : ℤ) (y : V ⊗[Qp] BdR)
    (hy : y ∈ FilV PD (LL := LL) (V := V) a) :
    actVdR PD ρ g y ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Submodule.zero_mem]
  | tmul v b =>
    exact ⟨ρ g v ⊗ₜ[Qp] ⟨PD.actdR g b.1, PD.Fil_G g a _ b.2⟩, rfl⟩
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ hx hy

include PD in
lemma nontrivial_B' : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact Submodule.zero_mem _

include PD in
lemma tmul_one_injective' {v w : V} (h : v ⊗ₜ[Qp] (1 : B) = w ⊗ₜ[Qp] (1 : B)) : v = w := by
  haveI := nontrivial_B' PD
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero : (1 : B) ≠ 0)
  have := congrArg (fun z => TensorProduct.rid Qp V (LinearMap.lTensor V f z)) h
  simpa [hf] using this

lemma sub_fixed_mem (d₁ : V ⊗[Qp] B) (h₁ : d₁ ∈ Dcris PD ρ) (d₂ : V ⊗[Qp] BdR) (h₂ : d₂ ∈ DdR PD ρ)
    (x : V ⊗[Qp] B) (y : V ⊗[Qp] BdR) (hy : y ∈ FilV PD (LL := LL) (V := V) 0)
    (hx : x - φVB PD (LL := LL) (V := V) x = d₁) (hxy : ιV PD (LL := LL) (V := V) x - y = d₂)
    (g : G) :
    φVB PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVB PD ρ g x - x ∧
      ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) ∈ FilV PD (LL := LL) (V := V) 0 := by
  have e₁ : actVB PD ρ g d₁ - d₁ = 0 := (Submodule.mem_iInf _).1 h₁ g
  have e₂ : actVdR PD ρ g d₂ - d₂ = 0 := (Submodule.mem_iInf _).1 h₂ g
  rw [← hx, map_sub] at e₁
  rw [← hxy, map_sub] at e₂
  constructor
  · rw [map_sub, φVB_actVB', ← sub_eq_zero, ← neg_eq_zero, ← e₁]
    abel
  · have : ιV PD (LL := LL) (V := V) (actVB PD ρ g x - x) = actVdR PD ρ g y - y := by
      rw [map_sub, ιV_actVB', ← sub_eq_zero, ← e₂]
      abel
    rw [this]
    exact Submodule.sub_mem _ (actVdR_mem_FilV' PD ρ g 0 y hy) hy

lemma cocycle_of_tmul_one (x : V ⊗[Qp] B) (c : G → V)
    (hc : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x) (g h : G) :
    c (g * h) = c g + ρ g (c h) := by
  apply tmul_one_injective' PD
  have e : ρ g (c h) ⊗ₜ[Qp] (1 : B) = actVB PD ρ g (c h ⊗ₜ[Qp] (1 : B)) := by
    rw [actVB_tmul', map_one]
  rw [add_tmul, e, hc, hc, hc, map_sub, actVB_mul']
  abel

end General

theorem connecting_cocycle : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ A : GRep ↥(GK K) ℚ_[l] LL O, ∀ d₁ ∈ Dcris (P.PD K) A.ρ, ∀ d₂ ∈ DdR (P.PD K) A.ρ, ∃ (x : A.V ⊗[ℚ_[l]] P.R.B) (y : A.V ⊗[ℚ_[l]] P.R.BdR) (c : ↥(GK K) → A.V), y ∈ FilV (P.PD K) (LL := LL) (V := A.V) 0 ∧ x - φVB (P.PD K) (LL := LL) (V := A.V) x = d₁ ∧ ιV (P.PD K) (LL := LL) (V := A.V) x - y = d₂ ∧ c ∈ finiteCocycles (P.PD K) A.ρ ∧ ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := by
  intro l _ P AI T K LL _ _ _ O _ _ hO A d₁ h₁ d₂ h₂
  obtain ⟨hsurj, hker⟩ := GlobalTheory.FundSeq.tensor_fundamental_sequence l P AI T K LL A.V
  obtain ⟨x, y, hy, hx, hxy⟩ := hsurj d₁ d₂
  have key : ∀ g, ∃ v : A.V, actVB (P.PD K) A.ρ g x - x = v ⊗ₜ[ℚ_[l]] (1 : P.R.B) := fun g =>
    hker _ (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).1
      (sub_fixed_mem (P.PD K) A.ρ d₁ h₁ d₂ h₂ x y hy hx hxy g).2
  choose c hc using key
  have hc' : ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) A.ρ g x - x := fun g => (hc g).symm
  have hcont : Continuous c :=
    GlobalTheory.FundCont.contCore_tied l P AI T K LL O hO A 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) x c
      (fun g => by rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add]; exact hc' g)
  exact ⟨x, y, c, hy, hx, hxy,
    ⟨⟨hcont, cocycle_of_tmul_one (P.PD K) A.ρ x c hc'⟩, x, hc'⟩, hc'⟩

end GlobalTheory.FundDel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWildStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalObjects_every_family_wild : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r₀ : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ₀ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r₀ → TakenWild N i r₀ ρ₀ → ∀ (r : N.X i → (GE N →* GL (Fin R.nV) (N.O i))) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))), GoodR N i r → ∀ π ∈ N.Z i, (∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := R.t) (r π) (ρ π) (N.chi i) e) → ∃ S : IdempotentChoiceData N i, GoodCongruenceObjects N r ρ π S ∧ IsWildInertiaCyclotomicElement N i S.g0 := by
  first | exact @GlobalTheory.ConsEveryFamilyWild.main | exact GlobalTheory.ConsEveryFamilyWild.main | (intros; apply GlobalTheory.ConsEveryFamilyWild.main <;> assumption)
end

