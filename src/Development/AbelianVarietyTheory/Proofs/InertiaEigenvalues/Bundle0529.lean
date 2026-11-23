module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0364
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0523

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairing
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_dualLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ hO hcyc U U' P hP LT

  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hfr
  haveI : Module.Finite O LT.T := Module.Finite.iff_fg.mpr LT.fg
  haveI : Module.Free O LT.T := LT.free
  let b := Module.Free.chooseBasis O LT.T
  let e : Module.Free.ChooseBasisIndex O LT.T → U.V := fun i => (b i : U.V)
  have he_O : LinearIndependent O e := b.linearIndependent.map' LT.T.subtype (Submodule.ker_subtype _)
  have he_L : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).mp he_O
  have hspanO : Submodule.span O (Set.range e) = LT.T := by
    have h1 : Set.range e = LT.T.subtype '' Set.range b := (Set.range_comp _ _)
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanL : Submodule.span LL (Set.range e) = ⊤ := by
    rw [← Submodule.span_span_of_tower O LL (Set.range e), hspanO]; exact LT.span
  let bL := Basis.mk he_L (le_of_eq hspanL.symm)
  have hbL : ∀ i, bL i = e i := fun i => Basis.mk_apply _ _ _
  let φ : U'.V →ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearMap.pi (fun i => P (e i))
  have hφ : ∀ y i, φ y i = P (e i) y := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hP.2.2.1 y
    intro x
    have h1 : P.flip y = 0 := bL.ext (fun i => by
      rw [hbL]; simpa [hφ] using congrFun hy i)
    simpa using LinearMap.congr_fun h1 x
  have hdim : finrank LL U'.V = finrank LL (Module.Free.ChooseBasisIndex O LT.T → LL) := by
    rw [← hP.2.2.2, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis bL]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφinj
  let φe : U'.V ≃ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let bf := (Pi.basisFun LL (Module.Free.ChooseBasisIndex O LT.T)).map φe.symm
  have hφf : ∀ i j, P (e j) (bf i) = (Pi.single i (1 : LL) : Module.Free.ChooseBasisIndex O LT.T → LL) j := fun i j => by
    have : φ (bf i) = Pi.single i 1 := by
      simp only [bf, Basis.map_apply, Pi.basisFun_apply]
      exact φe.apply_symm_apply _
    exact congrFun this j
  let T' : Submodule O U'.V :=
    { carrier := {y | ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a}
      add_mem' := by
        intro y z hy hz x hx
        obtain ⟨a, ha⟩ := hy x hx
        obtain ⟨c, hc⟩ := hz x hx
        exact ⟨a + c, by simp [ha, hc]⟩
      zero_mem' := fun x _ => ⟨0, by simp⟩
      smul_mem' := by
        intro c y hy x hx
        obtain ⟨a, ha⟩ := hy x hx
        refine ⟨c * a, ?_⟩
        show P x (c • y) = _
        rw [← algebraMap_smul LL c y, map_smul, ha, smul_eq_mul, map_mul] }
  have hmem : ∀ y, y ∈ T' ↔ ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a := fun y => Iff.rfl
  have hmem' : ∀ y, y ∈ T' ↔ ∀ i, P (e i) y ∈ Set.range (algebraMap O LL) := by
    intro y; constructor
    · intro hy i; obtain ⟨a, ha⟩ := hy (e i) (b i).2; exact ⟨a, ha.symm⟩
    · intro hy x hx
      choose a ha using hy
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • e i := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h2
        exact h2.symm
      obtain ⟨c, hcx⟩ : ∃ c : Module.Free.ChooseBasisIndex O LT.T → O, x = ∑ i, c i • e i := ⟨_, hx'⟩
      refine ⟨∑ i, c i * a i, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcx, map_sum, LinearMap.sum_apply, map_sum (algebraMap O LL)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← algebraMap_smul LL (c i) (e i), map_smul, LinearMap.smul_apply, ← ha i,
        smul_eq_mul, map_mul]
  have hf_mem : ∀ i, bf i ∈ T' := fun i => (hmem' _).mpr fun j => by
    rw [hφf]
    refine ⟨(Pi.single i (1 : O) : Module.Free.ChooseBasisIndex O LT.T → O) j, ?_⟩
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  have hT'eq : T' = Submodule.span O (Set.range bf) := by
    apply le_antisymm
    · intro y hy
      choose a ha using (hmem' y).mp hy
      have hy' : y = ∑ i, a i • bf i := by
        apply hφinj
        funext j
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hφ, hφ, map_sum, ← ha j]
        simp_rw [← algebraMap_smul LL (a _) (bf _), map_smul, hφf, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        simp
      rw [hy']
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hf_mem i
  have hfO : LinearIndependent O bf := (LinearIndependent.iff_fractionRing O LL).mpr bf.linearIndependent
  have hstab : ∀ g, ∀ y ∈ T', U'.ρ g y ∈ T' := by
    intro g y hy x hx
    obtain ⟨u, hu⟩ := hcyc g
    obtain ⟨a, ha⟩ := hy (U.ρ g⁻¹ x) (LT.stable g⁻¹ x hx)
    refine ⟨u * a, ?_⟩
    have hx' : U.ρ g (U.ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h3 := hP.1 g (U.ρ g⁻¹ x) y
    rw [hx'] at h3
    rw [h3, hu, ha, map_mul]
  have hopenT : IsOpen (T' : Set U'.V) := by
    have h4 : (T' : Set U'.V) = ⋂ i, (fun y => P (e i) y) ⁻¹' Set.range (algebraMap O LL) := by
      ext y; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact hmem' y
    rw [h4]
    exact isOpen_iInter_of_finite
      (fun i => hopen.preimage (IsModuleTopology.continuous_of_linearMap (R := LL) (P (e i))))
  refine ⟨⟨T', hstab, ?_, ?_, ?_⟩, ⟨hP, hmem⟩, hopenT⟩
  · rw [hT'eq]; exact Submodule.fg_span (Set.finite_range _)
  · rw [hT'eq]; exact Module.Free.of_basis (Basis.span hfO)
  · rw [hT'eq, Submodule.span_span_of_tower O LL]; exact bf.span_eq

end GlobalTheory.Pass.LocDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedMatricesOfEtaleRealisation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem repr_map_baseChange {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (s : WCb l →ₗ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T)
    (y : WCb l ⊗[ℤ_[l]] T) (i : Fin d) :
    (b.baseChange (WCb l)).repr (TensorProduct.map s r y) i =
      ∑ n, algebraMap ℤ_[l] (WCb l) (LinearMap.toMatrix b b r i n) * s ((b.baseChange (WCb l)).repr y n) := by
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
      ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  | add y z hy hz =>
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_add (f := _), Finsupp.add_apply, mul_add]

end GlobalTheory.BSP

namespace GlobalTheory.BSP


set_option maxHeartbeats 1600000 in
theorem exists_mReal_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  intro l _ K bk d S M e hF T _ _ ρ j H
  have hfin := H.finite
  have hfree := H.free
  obtain ⟨e', he'⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'
  have hrank : Module.finrank ℤ_[l] T = d := by
    rw [← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  let U : Matrix (Fin d) (Fin d) (WCb l) := (b.baseChange (WCb l)).toMatrix c
  have hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i := fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm
  have hcj : ∀ k, c k = j (M.tr bk.ι (e k)) := fun k => by rw [hc, he']
  refine ⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · letI := (b.baseChange (WCb l)).invertibleToMatrix c
    exact isUnit_of_invertible _
  · have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
    let t : ↥(ainfObj K).I := ⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩
    have hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A)) := hu
    have ht0 : (t : (ainfObj K).A) ≠ 0 := fun h => hu'.ne_zero (by rw [h, map_zero])
    have key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) =
        ∑ i, bk.evW (S.A i k) • c i := by
      intro k
      have hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k) := by
        simp [Pi.single_apply]
      obtain ⟨m, s, hm⟩ := exists_isFrac (t : (ainfObj K).A)
        (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))
      obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm
      replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by
        simpa only [hsum] using hm
      have hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id
          (j (M.tr bk.ι (e k))) = j m := H.j_φ t ht0 _ m s hm
      have hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) =
          (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) :=
        funext fun j' => by
          by_cases h : j' = k
          · subst h; simp
          · simp [Pi.single_apply, h]
      rw [hφ1] at hr
      have hr3 := (j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)
      have hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r)) := by
        rw [map_pow]; exact hu'.pow r
      have hr5 := sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))
      have hr7 := (j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))
      have e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a :=
        map_pow _ _ _
      have e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s :=
        map_pow _ _ _
      have hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) =
          ∑ i, bk.evW (S.A i k) • c i := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]
        rfl
      apply (hu.pow s).smul_left_cancel.1
      calc inclW l (bk.ev bk.E) ^ s • (inclW l (bk.ev bk.E) ^ S.a •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k))
          = inclW l (bk.ev bk.E) ^ S.a • (inclW l (bk.ev bk.E) ^ s •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k)))) := by
            rw [hcj, smul_smul, smul_smul, mul_comm]
        _ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj
        _ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm
        _ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) •
              j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7
        _ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]
    have hev : ∀ x, bk.evW x = inclW l (bk.ev x) := fun _ => rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)),
      map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      AlgHom.toLinearMap_apply] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U,
      Module.Basis.toMatrix_apply]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]
  · intro g
    have keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) =
        ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i := by
      intro k
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, ← hcj]
      rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · rw [← hcj, hck]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedStratifiedCrystalBasis
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frame_coord_cancel {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ}
    (b : Module.Basis (Fin d) B N) {t p q : B} (ht : t ∈ nonZeroDivisors B) {m : N} {k r s : ℕ}
    {v w : Fin d → B} (h1 : t ^ r • (p • m - t ^ k • ∑ i, v i • b i) = 0)
    (h2 : t ^ s • (q • m - t ^ k • ∑ i, w i • b i) = 0) (i : Fin d) : p * w i = q * v i := by
  have e1 := congrArg (fun x => b.equivFun x i) h1
  have e2 := congrArg (fun x => b.equivFun x i) h2
  simp only [← b.equivFun_symm_apply, map_smul, map_sub, LinearEquiv.apply_symm_apply, map_zero,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at e1 e2
  have f1 := (mem_nonZeroDivisors_iff.1 (pow_mem ht r)).1 _ e1
  have f2 := (mem_nonZeroDivisors_iff.1 (pow_mem ht s)).1 _ e2
  rw [← sub_eq_zero]
  apply (mem_nonZeroDivisors_iff.1 (pow_mem ht k)).1
  linear_combination q * f1 - p * f2

theorem frame_sum_single {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (v : Fin d → N)
    (j : Fin d) : ∑ i, (Pi.single j 1 : Fin d → B) i • v i = v j := by
  simp [Pi.single_apply]

theorem frame_sum_mulVec {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] {d : ℕ} (φ : B →+* B)
    (A ε : Matrix (Fin d) (Fin d) B) (v c : Fin d → N) (h : ∀ x, v x = ∑ i, ε i x • c i) (j : Fin d) :
    ∑ i, A.mulVec (fun x => φ ((Pi.single j 1 : Fin d → B) x)) i • v i = ∑ i, (ε * A) i j • c i := by
  have h2 : (fun x => φ ((Pi.single j 1 : Fin d → B) x)) = Pi.single j 1 := by
    ext x
    by_cases hx : x = j <;> simp [hx]
  simp only [h2, Matrix.mulVec_single_one, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul, mul_comm]
  rfl

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem frame_matrix_φ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ)
    (A : Matrix (Fin d) (Fin d) bk.S)
    (hΦ : ∀ j : Fin d, IsFrac (bk.toP bk.E)
      (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a)
    {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (c : Module.Basis (Fin d) B.A (M.M B))
    (hc : ∀ i, c i = M.tr f (e i)) (ε : Matrix (Fin d) (Fin d) B.A)
    (htr : ∀ j, M.tr g (e j) = ∑ i, ε i j • M.tr f (e i)) :
    BK.hf g bk.E ^ a • (A.map (BK.hf f) * ε.map B.D.φ) = BK.hf f bk.E ^ a • (ε * A.map (BK.hf g)) := by
  obtain ⟨hI, ht⟩ := _root_.GlobalTheory.BSP.hf_E_span_and_regular l K bk B f
  let t : ↥B.I := ⟨BK.hf f bk.E, hI.ge (Ideal.mem_span_singleton_self _)⟩
  ext i j
  obtain ⟨m, k, hm⟩ := exists_isFrac (t : B.A) (M.Φ B t (M.tr g (e j)))
  obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B g t (Pi.single j 1) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k)
      (frame_sum_single (fun i => M.tr g (e i)) j).symm hm)
  obtain ⟨s, hs⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e a A hΦ B f t (fun i => ε i j) m k
    (Eq.subst (motive := fun z => IsFrac (t : B.A) (M.Φ B t z) m k) (htr j) hm)
  have h1 := frame_sum_mulVec B.D.φ (A.map (BK.hf g)) ε (fun i => M.tr g (e i)) c
    (fun x => (htr x).trans (Finset.sum_congr rfl fun i _ => congrArg (fun z => ε i x • z) (hc i).symm)) j
  rw [h1] at hr
  simp only [← hc] at hs
  exact frame_coord_cancel c ht hr hs i

theorem exists_frame_matrices (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :
    ∃ ε : ∀ {B : Obj l ↥(OL K)}, Hom bk.prism B → Hom bk.prism B → Matrix (Fin d) (Fin d) B.A,
      (∀ {B} (f g : Hom bk.prism B) (j : Fin d), M.tr g (e j) = ∑ i, ε f g i j • M.tr f (e i)) ∧
      (∀ {B} (f : Hom bk.prism B), ε f f = 1) ∧
      (∀ {B} (f g h : Hom bk.prism B), ε f g * ε g h = ε f h) ∧
      (∀ {B B'} (k : Hom B B') (f g : Hom bk.prism B), (ε f g).map k.f = ε (k.comp f) (k.comp g)) := by
  have hb : ∀ {B : Obj l ↥(OL K)} (f : Hom bk.prism B), ∃ c : Module.Basis (Fin d) B.A (M.M B),
      ∀ i, c i = M.tr f (e i) := fun f => GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  choose c hc using @hb
  have htr : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d),
      M.tr g (e j) = ∑ i, (c f).toMatrix (c g) i j • M.tr f (e i) := fun f g j => by
    rw [← hc, ← (c f).sum_toMatrix_smul_self (c g) j]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  have huniq : ∀ {B : Obj l ↥(OL K)} (f g : Hom bk.prism B) (j : Fin d) (v : Fin d → B.A),
      M.tr g (e j) = ∑ i, v i • M.tr f (e i) → ∀ i, (c f).toMatrix (c g) i j = v i := fun f g j v h i => by
    change (c f).repr (c g j) i = v i
    rw [hc, h]
    simp only [← hc]
    rw [← (c f).equivFun_symm_apply, ← (c f).equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨fun f g => (c f).toMatrix (c g), htr, fun f => (c f).toMatrix_self,
    fun f g h => (c f).toMatrix_mul_toMatrix (c g) (c h), fun k f g => ?_⟩
  ext i j
  refine (huniq (k.comp f) (k.comp g) j (fun i => k.f ((c f).toMatrix (c g) i j)) ?_ i).symm
  refine (M.tr_comp k g (e j)).trans ((congrArg (M.tr k) (htr f g j)).trans ?_)
  refine (map_sum (M.tr k) _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
  exact ((M.tr k).map_smulₛₗ _ _).trans
    (congrArg (fun z => k.f ((c f).toMatrix (c g) i j) • z) (M.tr_comp k f (e i)).symm)

theorem exists_framed (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M : FCrys l ↥(OL K)) :
    ∃ (d : ℕ) (S : Strat bk d) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  have : IsLocalRing bk.prism.A := inferInstanceAs (IsLocalRing (Wq l bk.a)⟦X⟧)
  have := M.fin bk.prism
  have := M.proj bk.prism
  have : Module.Free bk.prism.A (M.M bk.prism) := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, ⟨e⟩⟩ : ∃ d, Nonempty (Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) :=
    ⟨_, ⟨Module.finBasis bk.prism.A (M.M bk.prism)⟩⟩
  obtain ⟨a, b, A, A', hA, hΦ⟩ := _root_.GlobalTheory.BSP.frob_matrix_bk l K bk d M e
  obtain ⟨ε, htr, h1, h2, h3⟩ := exists_frame_matrices M e
  refine ⟨d, ⟨a, b, A, A', hA, ε, h1, h2, h3, fun f g => ?_⟩, e, htr, hΦ⟩
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ _ (M.tr_bc f) _ e
  exact frame_matrix_φ M e a A hΦ f g c hc (ε f g) (htr f g)

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_span_corner_charpoly_separable : ∀ {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ} (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), AbsIrrDistinct (matRep σ) → b * a = 1 → a * b ∈ Submodule.span K (Set.range σ) → ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_mem_span_corner_separable | exact GlobalTheory.SpanRing.exists_mem_span_corner_separable | (intros; apply GlobalTheory.SpanRing.exists_mem_span_corner_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmithFactorizationEtaleOEModPrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.SmithQuot

theorem oe_dvr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := GlobalTheory.OEDvr.perfectRing_Cb
  obtain ⟨hdivl, -, -, hfac, -⟩ := GlobalTheory.OEDvr.main l K bk
  have hlW : Irreducible ((l : ℕ) : WCb l) := WittVector.irreducible l (k := Cb l)
  have hlO : (l : WCb l) ∈ bk.OE := natCast_mem _ l
  set π : ↥bk.OE := ⟨(l : WCb l), hlO⟩
  have hπ : ¬ IsUnit π := fun h => hlW.not_isUnit (h.map bk.OE.subtype)
  have hfac' : ∀ x : ↥bk.OE, x ≠ 0 → ∃ k : ℕ, Associated (π ^ k) x := by
    intro x hx
    obtain ⟨k, v, v', hv, hv', hvv, hx'⟩ := hfac x x.2 (fun h => hx (Subtype.ext h))
    refine ⟨k, ⟨⟨⟨v, hv⟩, ⟨v', hv'⟩, Subtype.ext hvv, Subtype.ext (by rw [mul_comm]; exact hvv)⟩, ?_⟩⟩
    apply Subtype.ext
    simp [π, hx']
  have hunit : ∀ x : ↥bk.OE, IsUnit (x : WCb l) → IsUnit x := by
    intro x hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    obtain ⟨k, hk⟩ := hfac' x hx0
    rcases k with _ | k
    · exact hk.isUnit_iff.mp (by rw [pow_zero]; exact isUnit_one)
    · exfalso
      obtain ⟨u, hu⟩ := hk
      have : (l : WCb l) ∣ (x : WCb l) := by
        rw [← hu]; exact ⟨(l : WCb l) ^ k * (u : ↥bk.OE), by simp [π, pow_succ]; ring⟩
      exact hlW.not_isUnit (isUnit_of_dvd_unit this hx)
  have hirr : Irreducible π := by
    refine ⟨hπ, ?_⟩
    intro a b hab
    have := hlW.isUnit_or_isUnit (show ((l : ℕ) : WCb l) = (a : WCb l) * (b : WCb l) from congrArg Subtype.val hab)
    exact this.imp (hunit a) (hunit b)
  exact IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, fun {x} hx => hfac' x hx⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' n : ℕ) (Q : Matrix (Fin d) (Fin d') (WCb l)) (P : Matrix (Fin d') (Fin d') (WCb l)), 1 ≤ n → (∀ i j, P i j ∈ bk.OE) → (∃ S : Matrix (Fin d') (Fin d) (WCb l), (∀ i j, (l : WCb l) ^ n ∣ (Q * S - (1 : Matrix (Fin d) (Fin d) (WCb l))) i j)) → (∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) ↔ ∃ w, v = P *ᵥ w) → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (Q * R' - Tn) i j) := by
  intro l _ K bk d d' n Q P hn hP hS hker
  obtain ⟨S, hS⟩ := hS
  obtain ⟨U, Uinv, hU, hUi, h1, h2, hdich⟩ := _root_.GlobalTheory.SmithOE.main l K bk (oe_dvr l K bk) d' P hP
  classical
  let J : Finset (Fin d') := Finset.univ.filter (fun j => ¬ ∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w)
  have hi : ∀ j ∉ J, ∀ i, (l : WCb l) ^ n ∣ (Q * U) i j := by
    intro j hj i
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    have := (hker (fun i => U i j)).mpr hj i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hii : ∀ v : Fin d' → WCb l, (∀ i, (l : WCb l) ^ n ∣ (Q *ᵥ v) i) → ∀ j ∈ J, (l : WCb l) ∣ (Uinv *ᵥ v) j := by
    intro v hv j hj
    obtain ⟨w, rfl⟩ := (hker v).mp hv
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hr := (hdich j).resolve_left hj
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum (fun k _ => (hr k).mul_right _)
  obtain ⟨e, hunit, hdiv⟩ := _root_.GlobalTheory.CardJ.exists_cols_of_rightInv_WCb l d d' n Q S U Uinv J hn hS h1 h2 hi hii
  refine ⟨Q * U.submatrix id (fun k => (e k : Fin d')), Uinv.submatrix (fun k => (e k : Fin d')) id,
    U.submatrix id (fun k => (e k : Fin d')), hunit, fun i j => hUi _ _, fun i j => hU _ _, hdiv, ?_⟩
  intro i j
  simp [Matrix.mul_submatrix_one, Matrix.submatrix]

end GlobalTheory.SmithQuot
end

