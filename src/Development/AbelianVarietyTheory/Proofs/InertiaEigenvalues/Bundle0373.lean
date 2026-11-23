module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.FrameEq

theorem map_inj {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (hf : Function.Injective f)
    {M M' : Matrix m n R} (h : M.map f = M'.map f) : M = M' := by
  ext i j
  exact hf (congrFun (congrFun h i) j)

private theorem padicInt_hom_ext_pt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(l : R)}) _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  have hz : z = (PadicInt.appr z n : ℤ_[l]) + c * (l : ℤ_[l]) ^ n := by rw [hc]; ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  rw [hz]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

theorem map_smul_rh {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j
  simp

theorem frobW_galW {l : ℕ} [Fact l.Prime] (g : GQ l) (x : WCb l) :
    frobW l (galW l g x) = galW l g (frobW l x) := by
  ext n
  simp [frobW, galW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def, map_pow]

theorem cocycle_frob {R : Type} [CommRing R] {d N : ℕ} (fr ga : R →+* R) (hc : ∀ x, fr (ga x) = ga (fr x))
    (e : R) (T A ε Z : Matrix (Fin d) (Fin d) R) (hT : IsUnit T) (hφ : e ^ N • T.map fr = T * A)
    (hgal : Z * T.map ga = T * ε) (hZ : Z.map fr = Z) :
    e ^ N • (ε * A.map ga) = ga e ^ N • (A * ε.map fr) := by
  have h1 : ga e ^ N • T.map (fun x => ga (fr x)) = T.map ga * A.map ga := by
    have := congrArg (fun M => M.map ga) hφ
    simp only [map_smul_rh, Matrix.map_mul, Matrix.map_map, map_pow] at this
    exact this
  have h2 : Z * T.map (fun x => ga (fr x)) = T.map fr * ε.map fr := by
    have := congrArg (fun M => M.map fr) hgal
    simp only [Matrix.map_mul, Matrix.map_map, hZ] at this
    have e2 : T.map (fun x => ga (fr x)) = T.map (⇑fr ∘ ⇑ga) := by
      ext i j; simp [hc]
    rw [e2]; exact this
  apply hT.mul_left_cancel
  calc T * (e ^ N • (ε * A.map ga)) = e ^ N • (T * ε * A.map ga) := by
        rw [Matrix.mul_smul, Matrix.mul_assoc]
    _ = e ^ N • (Z * (ga e ^ N • T.map (fun x => ga (fr x)))) := by
        rw [h1, ← hgal, Matrix.mul_assoc]
    _ = ga e ^ N • ((e ^ N • T.map fr) * ε.map fr) := by
        rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, h2, Matrix.smul_mul]
    _ = T * (ga e ^ N • (A * ε.map fr)) := by
        rw [hφ, Matrix.mul_smul, Matrix.mul_assoc]


open GlobalTheory.FrameEq in
theorem frame_Y_eqs : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y Y' : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → Y * Y' = τ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * F.A.map bk.ev ∧ (∀ g : ↥(GK K), τ ^ N • ((ρ g).map (Per.zA l) * Y.map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)) ∧ ∀ g : ↥(GK K), bk.ev bk.E ^ N • (F.ε g * F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))) = Per.σA (g : GQ l) (bk.ev bk.E) ^ N • (F.A.map bk.ev * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y Y' hY _
  have hev : ∀ s, inclW l (bk.ev s) = bk.evW s := fun s => rfl
  have hz : ∀ z : ℤ_[l], inclW l (Per.zA l z) = algebraMap ℤ_[l] (WCb l) z := fun z => by
    rw [← (inclWA l).commutes z, padicInt_hom_ext_pt (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) z]; rfl
  refine ⟨?_, ?_, ?_⟩
  · apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [frobW_inclW]
    rw [e1, Matrix.map_mul, hY]
    have e2 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e2, Matrix.smul_mul, ← F.φ]
    have e3 : ((inclW l τ ^ N) • F.T).map (frobW l) = frobW l (inclW l τ) ^ N • F.T.map (frobW l) := by
      ext i j; simp
    rw [e3, frobW_inclW, hτ.1, map_mul, hev, smul_smul, mul_pow, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have e1 : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      ext i j; simp [galW_inclW]
    have e2 : ((ρ g).map (Per.zA l)).map (inclW l) = zW (ρ g) := by ext i j; simp [hz]
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, e1, e2, hY]
    have e3 : ((inclW l τ ^ N) • F.T).map (galW l (g : GQ l)) =
        galW l (g : GQ l) (inclW l τ) ^ N • F.T.map (galW l (g : GQ l)) := by
      ext i j; simp
    rw [e3, galW_inclW, Matrix.mul_smul, F.gal, map_pow, map_pow, smul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  · intro g
    apply map_inj (inclW l) inclW_injective
    have key := cocycle_frob (frobW l).toRingHom (galW l (g : GQ l)).toRingEquiv.toRingHom
      (fun x => frobW_galW (g : GQ l) x) (bk.evW bk.E) F.T (F.A.map bk.evW) ((F.ε g).map (inclW l)) (zW (ρ g))
      F.unit F.φ (F.gal g) (by ext i j; simp [zW])
    rw [map_smul_rh, map_smul_rh, Matrix.map_mul, Matrix.map_mul, map_pow, map_pow, hev]
    have e1 : (F.A.map (fun s => Per.σA (g : GQ l) (bk.ev s))).map (inclW l) =
        (F.A.map bk.evW).map (galW l (g : GQ l)).toRingEquiv.toRingHom := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply]
      show _ = galW l (g : GQ l) (bk.evW (F.A i j))
      rw [← hev, galW_inclW]
    have e2 : ((F.ε g).map WittVector.frobenius).map (inclW l) = ((F.ε g).map (inclW l)).map (frobW l).toRingHom := by
      ext i j; simp [frobW_inclW]
    have e3 : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by ext i j; simp [hev]
    rw [e1, e2, e3, ← galW_inclW, hev]
    exact key

end GlobalTheory.FrameEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrism
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoordEx

theorem exists_basis {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {d : ℕ}
    (e : Module.Basis (Fin d) A M) : ∃ b : Module.Basis (Fin d) B N, ∀ i, b i = u (e i) := by
  let v : M →ₛₗ[f] (Fin d → B) :=
    { toFun := fun x i => f (e.repr x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (Fin d → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (e i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← e.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hv : ∀ i, S (u (e i)) = Pi.single i 1 := fun i => by
    rw [hS]
    ext j
    change f (e.repr (e i) j) = _
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (e i) := fun i => by
    simp [Q, Fintype.linearCombination_apply_single]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B (Fin d)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, hQ1, hv, LinearMap.id_apply]
  refine ⟨(Pi.basisFun B (Fin d)).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.ofLinear_apply, hQ1]

theorem equivFun_eq {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : ℕ}
    (b : Module.Basis (Fin d) A M) (y : M) (c : Fin d → A) (h : y = ∑ i, c i • b i) : b.equivFun y = c := by
  rw [h, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e →
    ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  intro l _ K bk d S M e hF B
  have hb : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q), ∃ b : Module.Basis (Fin d) Q.A (M.M Q),
      ∀ i, b i = M.tr g (e i) := fun Q g => exists_basis (M.tr_bc g) e
  choose b hb using hb
  have hs : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (y : M.M Q),
      y = ∑ i, (b Q g).equivFun y i • M.tr g (e i) := fun Q g y => by
    conv_lhs => rw [← (b Q g).sum_equivFun y]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]
  refine ⟨{ fin := M.fin B
            proj := M.proj B
            v := fun {Q} a g => (b Q g).equivFun.toLinearMap.comp (M.tr a)
            bc := fun {Q} a g => (M.tr_bc a).comp_equiv _
            v_ε := fun {Q} a g g' x => ?_
            v_nat := fun {Q Q'} c a g x i => ?_ }, fun {Q} a g x => hs Q g _⟩
  · change (b Q g).equivFun (M.tr a x) = (S.ε g g').mulVec ((b Q g').equivFun (M.tr a x))
    refine equivFun_eq _ _ _ ?_
    refine (hs Q g' (M.tr a x)).trans ?_
    generalize (b Q g').equivFun (M.tr a x) = c
    simp only [hF.tr g g', Finset.smul_sum, smul_smul, hb, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (c j)]
  · change (b Q' (c.comp g)).equivFun (M.tr (c.comp a) x) i = c.f ((b Q g).equivFun (M.tr a x) i)
    refine congrFun (equivFun_eq _ _ (fun i => c.f ((b Q g).equivFun (M.tr a x) i)) ?_) i
    refine (M.tr_comp c a x).trans ((congrArg (M.tr c) (hs Q g (M.tr a x))).trans ?_)
    refine (map_sum (M.tr c) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact ((M.tr c).map_smulₛₗ _ _).trans
      (congrArg (c.f _ • ·) ((hb Q' (c.comp g) j).trans (M.tr_comp c g (e j))).symm)

end GlobalTheory.BSP.CoordEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusGaloisRelationFrameAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.GalPhi

variable {l : ℕ} [Fact l.Prime]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  apply inclW_injective
  rw [← frobW_inclW, ← galW_inclW, ← galW_inclW, ← frobW_inclW]
  refine WittVector.ext fun n => ?_
  simp [galW, frobW, mapAlgEquivW, mapEquivW, WittVector.map_coeff, frobenius_def]

theorem frobenius_algebraMap (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  change WittVector.frobenius (zlW l (OCb l) z) = zlW l (OCb l) z
  rw [WittVector.frobenius_eq_map_frobenius]
  simp only [zlW, RingHom.comp_apply]
  refine WittVector.ext fun n => ?_
  simp only [WittVector.map_coeff]
  exact congrArg (fun φ : ZMod l →+* OCb l => φ (((WittVector.equiv l).symm.toRingHom z).coeff n))
    (RingHom.ext_zmod ((frobenius (OCb l) l).comp (ZMod.castHom (dvd_refl l) (OCb l))) (ZMod.castHom (dvd_refl l) (OCb l)))

theorem gal_ainf {K : FinExt l} (bk : BK K) (τ : Ainf l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ N • F.T)
    (g : ↥(GK K)) :
    τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
      Per.σA (g : GQ l) τ ^ N • (Y * F.ε g) := by
  have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
    refine Matrix.ext fun i j => ?_; exact (inclWA l).commutes _
  have hσ : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (galW_inclW _ _).symm
  have hT : (Y.map (inclW l)).map (galW l (g : GQ l)) = inclW l (Per.σA (g : GQ l) τ) ^ N • F.T.map (galW l (g : GQ l)) := by
    rw [hY, ← galW_inclW, ← map_pow]
    refine Matrix.ext fun i j => ?_; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Matrix.ext fun i j => ?_
  apply inclW_injective
  have key : (τ ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map (inclW l) =
      (Per.σA (g : GQ l) τ ^ N • (Y * F.ε g)).map (inclW l) := by
    rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
      hz, hσ, hT, Matrix.mul_smul, F.gal, hY, Matrix.smul_mul, smul_smul, smul_smul, mul_comm]
    simp only [map_pow]
  exact congrFun (congrFun key i) j

end GlobalTheory.GalPhi


open GlobalTheory.GalPhi in
theorem GlobalTheory.GalPhi.galPhi : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ g : ↥(GK K), (bk.ev bk.E * τ) ^ N • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * (Y.map WittVector.frobenius).map (Per.σA (g : GQ l))) = Per.σA (g : GQ l) (bk.ev bk.E * τ) ^ N • (Y.map WittVector.frobenius * (F.ε g).map WittVector.frobenius) := by
  intro l _ K bk τ hτ N d ρ F Y hY g
  have h := congrArg (fun M => M.map (WittVector.frobenius : Ainf l →+* Ainf l)) (gal_ainf bk τ N d ρ F Y hY g)
  rw [Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_mul, Matrix.map_mul,
    map_pow, map_pow, ← σA_frobenius, hτ.1] at h
  have h1 : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
    refine Matrix.ext fun i j => ?_; exact frobenius_algebraMap _
  have h2 : (Y.map (Per.σA (g : GQ l))).map (WittVector.frobenius : Ainf l →+* Ainf l) =
      (Y.map WittVector.frobenius).map (Per.σA (g : GQ l)) := by
    refine Matrix.ext fun i j => ?_; exact (σA_frobenius _ _).symm
  rw [h1, h2] at h
  exact h

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltration
section
noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (_root_.GlobalTheory.ExpImage.epsT_pow_taylor l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [coeff_eq, map_add (f := _), map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add (f := _), e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFactorTiltLogBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.InertiaEigenvalues.TiltGalLog

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem zeta_pow_compat {l : ℕ} [Fact l.Prime] (C : Core l) (c : ℤ_[l]) (m : ℕ) :
    C.ζ m ^ (PadicInt.toZModPow (m + 1) c).val = C.ζ m ^ (PadicInt.toZModPow m c).val := by
  have hz : C.ζ m ^ (l ^ m) = 1 := TAct.zeta_pow C m
  have hred : ∀ a : ℕ, C.ζ m ^ a = C.ζ m ^ (a % l ^ m) := fun a => by
    conv_lhs => rw [← Nat.mod_add_div a (l ^ m), pow_add, pow_mul, hz, one_pow, mul_one]
  have hmod : (PadicInt.toZModPow (m + 1) c).val ≡ (PadicInt.toZModPow m c).val [MOD l ^ m] := by
    rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val, ZMod.natCast_zmod_val]
    have h := congrArg (fun f : ℤ_[l] →+* ZMod (l ^ m) => f c)
      (PadicInt.zmod_cast_comp_toZModPow (p := l) m (m + 1) (Nat.le_succ m))
    simpa using h
  rw [hred, hmod, ← hred]

theorem rootT_mul {l : ℕ} [Fact l.Prime] (a b : Per.Fl l) (m : ℕ) :
    rootT (a * b) m = rootT a m * rootT b m := by
  unfold rootT
  rw [← map_mul]
  congr 1
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply', ih, map_mul]

theorem gal_factor_log : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (x : Per.Fl l) (g : GQ l) (c : ℤ_[l]),
    (∀ m : ℕ, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m c).val * rootT x m) →
    ∃ e : Per.Fl l, Per.σF g x = x * e ∧ e.untilt = 1 ∧
      Per.IsLog l e (aDp l (Per.zA l c) * C.j C.t) := by
  intro l _ C x g c H
  obtain ⟨e, he⟩ := NoLog.exists_tilt (fun m => C.ζ m ^ (PadicInt.toZModPow m c).val)
    (fun m => by
      show (C.ζ (m + 1) ^ (PadicInt.toZModPow (m + 1) c).val) ^ l = C.ζ m ^ (PadicInt.toZModPow m c).val
      rw [← pow_mul, mul_comm, pow_mul, C.ζ_succ, zeta_pow_compat]) 1 (by simp [C.ζ_zero])
  have he1 : e.untilt = 1 := Subtype.ext (by
    have := he 0
    rw [C.ζ_zero, one_pow, map_one] at this
    exact this)
  have hre : ∀ m, rootT e m = rootT C.ε m ^ (PadicInt.toZModPow m c).val := fun m =>
    Subtype.ext (by rw [he m, SubmonoidClass.coe_pow, C.ε_root m, map_pow])
  have hxe : Per.σF g x = x * e := by
    refine Perfection.ext fun n => ?_
    change PreTilt.coeff n (Per.σF g x) = PreTilt.coeff n (x * e)
    rw [coeff_eq_mk_rootT, coeff_eq_mk_rootT, H n, rootT_mul, hre n, mul_comm]
  obtain ⟨y, -, hy, -⟩ := exists_isLogA l e he1
  have hyeq := NoLog.log_eq C e c y he hy
  refine ⟨e, hxe, he1, ?_⟩
  have h := LogFun.isLog_map he1 hy C.j_cris
  have hj : C.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l c)) = aDp l (Per.zA l c) := by
    rw [GlobalTheory.RingIface.tower, C.j_cris.on0, Subalgebra.coe_algebraMap, aDp, RingHom.comp_apply]
  rwa [hyeq, map_mul, hj] at h

end GlobalTheory.InertiaEigenvalues.TiltGalLog
end

