module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentWachLetterBasisFiltration
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversTameActsRingEndoWittPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverRing

variable {l : ℕ} [hl : Fact l.Prime]

theorem smul_eq_zero_ainf {c : ℤ_[l]} (hc : c ≠ 0) {z : Ainf l} (h : c • z = 0) : z = 0 := by
  have h1 := PadicInt.unitCoeff_spec hc
  rw [h1, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc] at h
  have h2 : (l : Ainf l) ^ c.valuation * z = 0 :=
    ((PadicInt.unitCoeff hc).isUnit.map (algebraMap ℤ_[l] (Ainf l))).mul_right_eq_zero.1 h
  have key : ∀ n : ℕ, ∀ z : Ainf l, (l : Ainf l) ^ n * z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih => intro z h; exact ih z (ainf_torsionFree _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact key _ z h2

theorem one_tmul_inj {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Nontrivial O]
    {x y : Ainf l} (h : (1 : O) ⊗ₜ[ℤ_[l]] x = (1 : O) ⊗ₜ[ℤ_[l]] y) : x = y := by
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_zero (b.repr.injective (by ext i; simp [hc i]))
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] (Ainf l) ((b.coord i).rTensor (Ainf l) w)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (smul_eq_zero_ainf hi h1)

variable {a : ℕ} [NeZero a]

theorem exists_root {e : ℕ} [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]
    (γ : TameGal ↥LL.1 l e a) :
    ∃ c : Wq l a, ∀ τ, algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ c) = γ.root τ := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have he : e = l ^ a - 1 := by
    have := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a); omega
  set w : ↥LL.1 := ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) with hwdef
  have hw : (w : Om l) = ω := by
    refine (algebraMap (Om l) ℂ_[l]).injective ?_
    have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
    simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
    exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)
  have hwp : IsPrimitiveRoot w e := by
    rw [he]
    refine IsPrimitiveRoot.of_map_of_injective (f := (LL.1).val) ?_ Subtype.val_injective
    simpa [hw] using hω
  have hpow : (((γ.left : (↥LL.1)ˣ) : ↥LL.1)) ^ e = 1 := (mem_rootsOfUnity' _ _).1 γ.left.2
  obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one hpow
  refine ⟨WittVector.teichmuller l z ^ k, fun τ => ?_⟩
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z ^ k)) : ↥(OL LL)) : ↥LL.1) = _
  rw [map_pow, sigma_pow_teich, map_pow, map_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hwdef,
    TameGal.root, powL_apply]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hk]
  ring

end GlobalTheory.BKGal.CoverRing


open GlobalTheory.BKGal.CoverRing GlobalTheory.BKGal.CoverBridge in
theorem GlobalTheory.BKGal.covers_ringEndo : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a),
    Covers ↥LL.1 (thetaW a LL) ϖ g γ →
      ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  intro l _ a e _ _ ϖ LL _ _ g γ hcov
  obtain ⟨c, hc⟩ := exists_root LL γ
  refine ⟨(rescale c).comp (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
    Wq l a →+* Wq l a)), fun x => ?_⟩
  have h := hcov (toAc (thetaW a LL) ↥LL.1 x)
    (toAc (thetaW a LL) ↥LL.1 (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x))) (fun τ => toAc_rescale (thetaW a LL) γ c hc x τ)
  rw [PiSys.iTot_toAc, PiSys.iTot_toAc, galOA_tmul] at h
  exact (one_tmul_inj h).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalBasisTransportFreeOverPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysIndep

theorem exists_read {Z O S W R N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing R]
    [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup N]
    (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (g : S →+* R)
    (hg : ∀ z, g (algebraMap Z S z) = algebraMap O R (algebraMap Z O z)) (D : N →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i) :
    ∃ V : N →+ (ι → R), (∀ s x x' i, D x' i = ((1 : O) ⊗ₜ[Z] ρ s) * D x i → V x' i = g s * V x i) ∧
      (∀ (c : O) x i, D x i = algebraMap O _ c → V x i = algebraMap O R c) := by
  letI : Algebra Z R := ((algebraMap O R).comp (algebraMap Z O)).toAlgebra
  haveI : IsScalarTower Z O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : S →ₐ[Z] R := { toRingHom := g, commutes' := hg }
  let Ψ : O ⊗[Z] S →ₐ[O] R :=
    Algebra.TensorProduct.lift (Algebra.ofId O R) g' fun _ _ => Commute.all _ _
  have hi : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) ρ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := O) ρ.toLinearMap hρ
  choose C hC using hD
  refine ⟨AddMonoidHom.mk' (fun x i => Ψ (C x i)) fun x y => funext fun i => ?_, fun s x x' i h => ?_,
    fun c x i h => ?_⟩
  · have : C (x + y) i = C x i + C y i := hi (by rw [map_add (f := _), hC, hC, hC, map_add (f := _), Pi.add_apply])
    change Ψ (C (x + y) i) = Ψ (C x i) + Ψ (C y i)
    rw [this, map_add (f := _)]
  · have : C x' i = ((1 : O) ⊗ₜ[Z] s) * C x i := hi (by
      rw [map_mul, hC, hC, h, Algebra.TensorProduct.map_tmul]; rfl)
    change Ψ (C x' i) = g s * Ψ (C x i)
    rw [this, map_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have : C x i = algebraMap O _ c := hi (by rw [hC, h, AlgHom.commutes])
    change Ψ (C x i) = _
    rw [this, AlgHom.commutes]

theorem indep_of_coord {Z O S W B R M N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing B]
    [CommRing R] [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι] {f : S →+* B} {u : M →ₛₗ[f] N}
    (hu : SemiBC u) (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (ψ : B →+* R)
    (hψ : ∀ z, ψ (f (algebraMap Z S z)) = algebraMap O R (algebraMap Z O z)) (D : M →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i)
    (hs : ∀ (s : S) x, D (s • x) = ((1 : O) ⊗ₜ[Z] ρ s) • D x) (m : O → ι → M)
    (hm : ∀ o j k, D (m o j) k = o • if k = j then 1 else 0) :
    ∃ lam : N →+ (ι → R), ∀ (Q : Type) [Fintype Q] (c : ι → Q → O) (y : ι → Q → B) (i : ι),
      lam (∑ j, ∑ q, y j q • u (m (c j q) j)) i = ∑ q, c i q • ψ (y i q) := by
  obtain ⟨V, hV1, hV2⟩ := exists_read ρ hρ (ψ.comp f) hψ D hD
  have hVb : ∀ (o : O) j k, V (m o j) k = algebraMap O R (if k = j then o else 0) := fun o j k => by
    refine hV2 _ _ _ ?_
    rw [hm]
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one o).symm
    · rw [smul_zero, map_zero]
  let V' : M →+ (Unit → ι → R) := AddMonoidHom.mk' (fun x _ => V x)
    fun x y => funext fun _ => map_add V x y
  obtain ⟨lam, hl1, hl2⟩ := CrysExt.exists_ext hu (fun _ : Unit => ψ) V' fun w x _ k =>
    hV1 w x (w • x) k (by rw [hs]; rfl)
  refine ⟨(Pi.evalAddMonoidHom _ ()).comp lam, fun Q _ c y i => ?_⟩
  have h3 : ∀ j q, lam (y j q • u (m (c j q) j)) () i =
      if i = j then c j q • ψ (y j q) else 0 := fun j q => by
    rw [hl1, hl2]
    change _ * V _ i = _
    rw [hVb]
    split_ifs
    · rw [Algebra.smul_def, mul_comm]
    · rw [map_zero, mul_zero]
  change lam _ () i = _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_apply, h3]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]


variable (a) in
noncomputable def evW (ϖ : PiSys l e) : (Wq l a)⟦X⟧ →ₐ[ℤ_[l]] WCb l where
  toRingHom := (inclW l).comp (ϖ.ev a)
  commutes' z := by
    change inclW l (ϖ.ev a (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = _
    rw [PowerSeries.algebraMap_apply, PiSys.ev_C, AlgHom.commutes]
    exact (inclWA l).commutes z

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}

theorem exists_toW_eq {m : Vec K a ι} (hm : m ∈ P.M) (i : ι) :
    ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i := by
  have h1 : toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i =
      OfCrystal.iR K t ϖ fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩ :=
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  obtain ⟨s, hs⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O)
    (fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩)
  refine ⟨∑ k, Module.Free.chooseBasis ℤ_[l] O k • ((1 : O) ⊗ₜ[ℤ_[l]] s k), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, OfCrystal.iR_toAc]
  rfl

theorem toW_bas (j : ι) (hm : (bas j : Vec K a ι) ∈ P.M) (i : ι) :
    toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ i = if i = j then 1 else 0 := by
  rw [toW_apply]
  split_ifs with h
  · rw [← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))
  · rw [← map_zero (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE b hb
  have h0 : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (BKCoord.ev_injective ϖ)
      (BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hJo : ∀ c x, J ((oE c).u (ϖ.prism a) x) = c • J x := fun c x => by
    have h3 := (congrArg jA ((oE c).u_tr (ϖ.toAinf a) x)).symm.trans (hoE c _)
    have h4 := (congrArg (kappa T) h3).trans (OfCrystal.kappa_mulZ T c _)
    rewrite [hJ, hJ]
    exact h4
  have hJs : ∀ (w : (ϖ.prism a).A) x, J (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • J x :=
    fun w x => by
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (BKCoord.kappa_smul T _ _)
    rewrite [hJ, hJ]
    exact h5
  refine ⟨fun i => hi (by rw [hJo, one_smul]), ?_⟩
  intro P' f Q Q' _ _ c y c' y' heq R _ _ ψ hψ i
  have h1 : ∃ D : E.M (ϖ.prism a) →+ (ι → OW l O), ∀ x, D x = I.j.symm (J x) :=
    ⟨I.j.symm.toLinearMap.toAddMonoidHom.comp J, fun _ => rfl⟩
  obtain ⟨D, hD⟩ := h1
  have h2 : ∀ x k, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = D x k := fun x k => by
    obtain ⟨m, hm, h⟩ := (him (J x)).1 ⟨x, hJ x⟩
    rw [hD, h, LinearEquiv.symm_apply_apply]
    exact exists_toW_eq t ϖ hm k
  have h3 : ∀ (w : (ϖ.prism a).A) x, D (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • D x :=
    fun w x => (hD _).trans ((congrArg I.j.symm (hJs w x)).trans
      ((I.j.symm.map_smul _ _).trans (congrArg _ (hD x).symm)))
  have h4 : ∀ (o : O) j k, D ((oE o).u (ϖ.prism a) (b j)) k = o • if k = j then 1 else 0 := fun o j k => by
    obtain ⟨hm, h⟩ := hb j
    have h5 : I.j.symm (J (b j)) = toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ :=
      I.j.symm_apply_eq.2 ((hJ _).trans h)
    have h6 : I.j.symm (o • J (b j)) = o • I.j.symm (J (b j)) := LinearMapClass.map_smul_of_tower _ _ _
    have h7 := ((hD _).trans (congrArg I.j.symm (hJo o (b j)))).trans (h6.trans (congrArg (o • ·) h5))
    exact (congrFun h7 k).trans (congrArg (o • ·) (toW_bas t ϖ j hm k))
  letI : Algebra ℤ_[l] (ϖ.prism a).A := (inferInstance : Algebra ℤ_[l] (Wq l a)⟦X⟧)
  obtain ⟨lam, hlam⟩ := indep_of_coord (Z := ℤ_[l]) (S := (ϖ.prism a).A) (E.tr_bc f) (evW a ϖ)
    (OfCrystal.ev_injective ϖ t K) ψ hψ D h2 h3 (fun o j => (oE o).u (ϖ.prism a) (b j)) h4
  simp only [FHom.u_tr] at heq
  exact (hlam Q c y i).symm.trans ((congrArg (lam · i) heq).trans (hlam Q' c' y' i))

end GlobalTheory.CrysIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFinite
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.JumpsFinite


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem jumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ →
    (Jumps (PD := (D.loc l).PD K) T).Finite := by
  intro D HW l _ K s LL h T hcrys
  have hP := GlobalTheory.NL.Points.points D HW l K s LL h
  have hfin : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hP.2.2.2.1]
    haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    exact Module.finrank_pos.ne'
  have hsub : Jumps (PD := (D.loc l).PD K) T ⊆
      ⋃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, {a | IsJumpV ((D.loc l).PD K) T.ρ τ a} := by
    rintro a ⟨τ, hτ⟩
    exact Set.mem_iUnion.2 ⟨τ, hτ⟩
  refine (Set.finite_iUnion fun τ => ?_).subset hsub
  obtain ⟨i, ζ, hpt⟩ := hP.2.2.1 τ
  obtain ⟨-, hemb, ι, hcomp⟩ := hP.2.1 i ζ τ hpt
  have hrank := (GlobalTheory.Per.LetterDim.tied_letter_component_finrank l _ _
    (D.locT l) K LL T.V T.ρ).1 hP.2.2.2.2 hcrys (((HW l).W K s LL h).emb i)
  set Dm := Di (HW l) h T i with hDm
  have hDfin : FiniteDimensional ↥LL.1 ↥Dm := by
    rcases Nat.eq_zero_or_pos (Module.finrank ↥LL.1 T.V) with h0 | hpos
    · have hV : Subsingleton T.V := Module.finrank_zero_iff.1 h0
      have hVB : Subsingleton (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := by
        refine ⟨fun x y => ?_⟩
        have hz : ∀ z : T.V ⊗[ℚ_[l]] (D.loc l).R.B, z = 0 := by
          intro z
          induction z using TensorProduct.induction_on with
          | zero => rfl
          | tmul v b => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz x, hz y]
      infer_instance
    · exact Module.finite_of_finrank_pos (hrank ▸ hpos)
  let S : ℤ → Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] (D.loc l).R.B) := fun a =>
    Dm ⊓ (FilAt ((D.loc l).PD K) T τ a).comap (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
  have hSanti : Antitone S := by
    refine antitone_int_of_succ_le fun a => inf_le_inf_left _ (Submodule.comap_mono ?_)
    exact sup_le_sup_right (GlobalTheory.Pst.filDR_succ_le ((D.loc l).PD K) T.ρ τ a) _
  let f : ℤ → ℕ := fun a => Module.finrank ↥LL.1 ↥(S a)
  have hfS : ∀ a, Module.finrank ↥LL.1 ↥(S a) ≤ Module.finrank ↥LL.1 ↥Dm := fun a =>
    Submodule.finrank_mono inf_le_left
  have hlt : ∀ a b, IsJumpV ((D.loc l).PD K) T.ρ τ a → a < b → f b < f a := by
    intro a b ha hab
    obtain ⟨d, hd, h1, h2⟩ := GlobalTheory.T.exists_crystallineLetter_of_hodgeJump D HW l K s LL h T hcrys i ζ τ hpt a ha
    have hle : S b ≤ S (a + 1) := hSanti (by omega)
    have hlt' : S (a + 1) < S a := by
      refine lt_of_le_of_ne (hSanti (by omega)) fun heq => h2 ?_
      have : d ∈ S a := ⟨hd, h1⟩
      rw [← heq] at this
      exact this.2
    haveI : FiniteDimensional ↥LL.1 ↥(S a) :=
      Submodule.finiteDimensional_of_le (inf_le_left : S a ≤ Dm)
    exact lt_of_le_of_lt (Submodule.finrank_mono hle) (Submodule.finrank_lt_finrank_of_lt hlt')
  refine Set.Finite.of_finite_image (f := f) ((Set.finite_Iic (Module.finrank ↥LL.1 ↥Dm)).subset ?_) ?_
  · rintro _ ⟨a, -, rfl⟩
    exact hfS a
  · intro a ha b hb hab
    rcases lt_trichotomy a b with hh | hh | hh
    · exact absurd hab (hlt a b ha hh).ne'
    · exact hh
    · exact absurd hab (hlt b a hb hh).ne

end GlobalTheory.NL.JumpsFinite
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupDivisibleImageCoboundaryIffFiniteLevel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel.NatCup

section Lifts

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I x ∈ L.T :=
  (Submodule.Quotient.mk_surjective I x).choose.2

theorem mk_liftQ_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ L I x, liftQ_mem_lat L I x⟩ : ↥L.T ⧸ I) = x :=
  (Submodule.Quotient.mk_surjective I x).choose_spec

theorem mk_liftD_lat (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    (Submodule.Quotient.mk (liftD L c) : V ⧸ L.T) = c :=
  (Submodule.Quotient.mk_surjective L.T c).choose_spec

theorem mem_span_pow_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by simp [hr]⟩
    · exact ⟨0, by simp [h0, zero_pow hr.ne']⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow, map_one]⟩

theorem pair_shift {V' : Type} [AddCommGroup V'] [Module LL V'] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (f : V' →ₗ[LL] V') (a t â : V) (w y : V') (c π k u v : LL) (hâ : â = a + π • t)
    (hk : c * π = k) (hu : m a (f (w - c • y)) = u) (hv : m t (f y) = v) :
    u - k * v = m a (f w) - c * m â (f y) := by
  subst hâ hk hu hv
  simp only [map_sub, map_add (f := _), map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Lifts

end GlobalTheory.BKFinLevel.NatCup

namespace GlobalTheory.BKFinLevel


open GlobalTheory.BKFinLevel.NatCup in
theorem cobO_cupLD_ioL_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  intro l _ P K LL _ _ _ O _ _ _ L1 hL1 A A' LA LA' m hd ϖ r d c'
  have key : ∀ x, (Submodule.Quotient.mk (cupLD LA' m (d : ↥(GK K) → A.V)
      (fun g => ioL LA' ϖ r (c' g)) x) : LL ⧸ L1.T) =
      Submodule.Quotient.mk (cupQ LA LA' m ϖ r (redT LA _ d) c' x) := by
    rintro ⟨g, h⟩
    rw [Submodule.Quotient.eq, hL1]
    obtain ⟨e, he⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r

    have hyT := liftQ_mem_lat LA' _ (c' h)
    have hw : liftD LA' (ioL LA' ϖ r (c' h)) -
        (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) ∈ LA'.T := by
      have h2 : ioL LA' ϖ r (c' h) = Submodule.Quotient.mk
          ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)) := by
        conv_lhs => rw [← mk_liftQ_lat LA' _ (c' h)]
        rfl
      exact (Submodule.Quotient.eq _).1 ((mk_liftD_lat LA' _).trans h2)

    have haT : (d : ↥(GK K) → A.V) g ∈ LA.T := d.2.2 g (Set.mem_univ g)
    have hred : (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ LA _ (redT LA _ d g),
        liftQ_mem_lat LA _ _⟩ : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
        Submodule.Quotient.mk ⟨(d : ↥(GK K) → A.V) g, haT⟩ := mk_liftQ_lat LA _ _
    obtain ⟨t, ht⟩ := (mem_span_pow_smul_top LA _ _).1 ((Submodule.Quotient.eq _).1 hred)
    have ht' : Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g) =
        (d : ↥(GK K) → A.V) g + (algebraMap O LL ϖ) ^ r • (t : A.V) := by
      have := congrArg (fun z : ↥LA.T => (z : A.V)) ht
      simp only [Submodule.coe_sub, Submodule.coe_smul] at this
      have hs : (algebraMap O LL ϖ) ^ r • (t : A.V) = ϖ ^ r • (t : A.V) := by
        rw [← map_pow, algebraMap_smul]
      rw [hs]
      exact (sub_eq_iff_eq_add').1 this
    have hw2 : A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hw
    have hy2 : A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hyT
    have hb1' : ∃ b : O, m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hw2 _ haT
    have hb2' : ∃ b : O, m (t : A.V) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hy2 _ t.2
    obtain ⟨b1, hb1⟩ := hb1'
    obtain ⟨b2, hb2⟩ := hb2'
    refine ⟨b1 - e * b2, ?_⟩
    show algebraMap O LL (b1 - e * b2) =
      m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)))) -
        (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g))
          (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)))
    have hsplit : algebraMap O LL (b1 - e * b2) =
        algebraMap O LL b1 - algebraMap O LL e * algebraMap O LL b2 := by
      rw [map_sub, map_mul]
    exact hsplit.trans (pair_shift m (A'.ρ g) _ _ _ _ _ _ _ _ _ _ ht' he hb1 hb2)
  unfold CobO
  exact Iff.of_eq (congrArg (fun z => z ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤) (funext key))

end GlobalTheory.BKFinLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); @Module.finrank ↥LL.1 _ _ _ (Submodule.module (DdR (P.PD K) ρ)) = Module.finrank ℚ_[l] ↥K.1 * m → (∀ (σ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), σ x ∈ LL.1) → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.htc_basis) | (exact GlobalTheory.HTBasis.htc_basis) | (intros; apply GlobalTheory.HTBasis.htc_basis  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDvdOfDvdRestrictClosedDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_dvd_of_dvd_restrict_closedDisc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → ∀ y, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ R y → toDisc l (X : bk.S) ρ bk.E ∣ y := by
  first | exact @GlobalTheory.BSP.dvd_of_dvd_restrict_discS | exact GlobalTheory.BSP.dvd_of_dvd_restrict_discS | (intros; apply GlobalTheory.BSP.dvd_of_dvd_restrict_discS <;> assumption)
end

