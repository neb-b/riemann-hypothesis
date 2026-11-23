module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0603
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.SeedExists

theorem exists_seed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ),
    (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T),
    Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  intro l _ K bk τ hτ P AI hstd V _ _ _ _ _ _ _ ρ L _ hcrys d b
  obtain ⟨T⟩ := hstd
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  set ρm : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l] := fun g => LinearMap.toMatrix b b (actT L g) with hρm
  have hv0 := GlobalTheory.T.crystallineLattice_basis_span_invariants l K P AI T V ρ L hcrys d b
  obtain ⟨U, U', hUU', hU⟩ := _root_.GlobalTheory.Per.PerMat.exists_invertible_invariant l K P AI T d ρm hv0
  obtain ⟨hInvB, hInvdR⟩ := _root_.GlobalTheory.MemLoc.fits_inv l P AI T C hC
  obtain ⟨c₁, c₃, F, F', hFF', hF⟩ := _root_.GlobalTheory.SeedF.frob_matrix l K bk C hInvB d ρm U U' hUU' hU
  obtain ⟨N₀, hN₀⟩ := _root_.GlobalTheory.CrisPeriods.periods_over_Acris l K P AI T C hC bk d ρm U U' hUU' hU c₁ F hF
  have hv2 := GlobalTheory.T.crysLattice_basis_mem_sum_deRham_filtration l K P AI T V ρ L hcrys d b
  obtain ⟨N, m, k, c, β, hN, hk, hUN, hUc, hβ, hUcβ⟩ :=
    _root_.GlobalTheory.BdRLatticeGens.exists_lattice_generators l K P AI T C hC hInvdR d ρm U U' hUU' hU hv2 N₀
  have hUU'ι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU', Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨c₂, X, X', hXX', hnp, hX, hX'⟩ :=
    _root_.GlobalTheory.BKModif.exists_modification_of_filtration l K bk C d (U.map C.ι) (U'.map C.ι) hUU'ι N m k c β hk (fun r s => hUN r s) hUc hβ hUcβ
  obtain ⟨Z, Z', hZ⟩ := hN₀ N hN X X' hX hX'
  exact _root_.GlobalTheory.BSP.seed_of_periods l K bk C τ hτ d ρm N c₁ c₂ c₃ F F' X X' hFF' hXX' hnp Z Z' hZ

end GlobalTheory.SeedExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfEquivariantEtaleMapAinf
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem semilinear_square_of_basis {A B N N' Q Q' ι : Type} [CommRing A] [CommRing B] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    {c : A →+* B} (β : Module.Basis ι A N) (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q')
    (G : Q →ₗ[B] Q') (h : ∀ k, j' (w (β k)) = G (j (β k))) (x : N) : j' (w x) = G (j x) :=
  LinearMap.congr_fun (β.ext (f₁ := j'.comp w) (f₂ := G.comp j) h) x

theorem sum_smul_column_eq {R B T T' : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup T]
    [Module R T] [AddCommGroup T'] [Module R T'] {d d' : ℕ} (b : Module.Basis (Fin d) R T)
    (b' : Module.Basis (Fin d') R T') (f : T →ₗ[R] T') (U : Matrix (Fin d) (Fin d) B)
    (U' : Matrix (Fin d') (Fin d') B) (Y : Matrix (Fin d') (Fin d) B)
    (h : U' * Y = (LinearMap.toMatrix b b' f).map (algebraMap R B) * U) (k : Fin d) :
    ∑ i, Y i k • ∑ m, U' m i ⊗ₜ[R] b' m = f.baseChange B (∑ i, U i k ⊗ₜ[R] b i) := by
  have h1 : ∀ i, f (b i) = ∑ m, LinearMap.toMatrix b b' f m i • b' m := fun i => by
    conv_lhs => rw [← b'.sum_repr (f (b i))]
    simp only [LinearMap.toMatrix_apply]
  have h2 : ∀ m, ∑ i, Y i k * U' m i = ∑ i, LinearMap.toMatrix b b' f m i • U i k := fun m => by
    have := congrFun (congrFun h m) k
    simp only [Matrix.mul_apply, Matrix.map_apply] at this
    simp only [Algebra.smul_def, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.baseChange_tmul, h1, TensorProduct.tmul_sum, Finset.smul_sum,
    TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.tmul_smul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul, h2]

theorem square_column {S A B P P' N N' Q Q' κ : Type} [CommRing S] [CommRing A] [CommRing B] [AddCommGroup P]
    [Module S P] [AddCommGroup P'] [Module S P'] [AddCommGroup N]
    [Module A N] [AddCommGroup N'] [Module A N'] [AddCommGroup Q] [Module B Q] [AddCommGroup Q'] [Module B Q']
    [Fintype κ] {a : S →+* A} {c : A →+* B} (t : P →ₛₗ[a] N) (t' : P' →ₛₗ[a] N') (v : P →ₗ[S] P')
    (w : N →ₗ[A] N') (j : N →ₛₗ[c] Q) (j' : N' →ₛₗ[c] Q') (G : Q →ₗ[B] Q') (hw : ∀ x, w (t x) = t' (v x))
    {n : N} {p : P} {y : κ → S} {e : κ → P'} {q : Q} {q' : κ → Q'} (hn : n = t p) (hp : v p = ∑ i, y i • e i)
    (hq : j (t p) = q) (hq' : ∀ i, j' (t' (e i)) = q' i) (h : ∑ i, c (a (y i)) • q' i = G q) :
    j' (w n) = G (j n) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hn, hw, hp, hq, ← h, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [t'.map_smulₛₗ, j'.map_smulₛₗ, hq']

theorem exists_fHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (T' : Type) [AddCommGroup T'] [Module ℤ_[l] T'] (ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')) (M M' : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)) (j' : M'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')), Realises K M (ainfObj K) (ainfId K) T ρ j → Realises K M' (ainfObj K) (ainfId K) T' ρ' j' → ∀ f : T →ₗ[ℤ_[l]] T', (∀ g x, f (ρ g x) = ρ' g (f x)) → ∃ u : FHom M M', ∀ x, j' (u.u (ainfObj K) x) = f.lTensor (WCb l) (j x) := by
  intro l _ K T _ _ ρ T' _ _ ρ' M M' j j' H H' f hf
  obtain ⟨bk⟩ := _root_.GlobalTheory.BSP.nonempty_bk_of_finExt l K
  obtain ⟨d, S, e, hS⟩ := _root_.GlobalTheory.BSP.exists_framed l K bk M
  obtain ⟨d', S', e', hS'⟩ := _root_.GlobalTheory.BSP.exists_framed l K bk M'
  obtain ⟨b, U, hU, hj⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d S M e hS T ρ j H
  obtain ⟨b', U', hU', hj'⟩ := GlobalTheory.T.exists_framedMatrices_of_etaleRealisation l K bk d' S' M' e' hS' T' ρ' j' H'
  have hF : ∀ g, LinearMap.toMatrix b b' f * LinearMap.toMatrix b b (ρ g) =
      LinearMap.toMatrix b' b' (ρ' g) * LinearMap.toMatrix b b' f := fun g => by
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    exact LinearMap.ext (hf g)
  obtain ⟨Y, hY⟩ := _root_.GlobalTheory.BSP.equivariant_matrix_over_bk l K bk d d' S S' _ _ U U' hU hU' _ hF
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.BSP.exists_fHom_of_isStratHom l K bk d d' S S' M M' e e' hS hS' Y
    (_root_.GlobalTheory.isStratHom_of_equivariant l K bk d d' S S' _ _ U U' hU hU' _ hF Y hY)
  obtain ⟨β, hβ⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  refine ⟨u, fun x => ?_⟩
  refine semilinear_square_of_basis β (u.u (ainfObj K)) j j' (f.baseChange (WCb l)) (fun k => ?_) x
  refine square_column (M.tr bk.ι) (M'.tr bk.ι) (u.u bk.prism) (u.u (ainfObj K)) j j' (f.baseChange (WCb l))
    (u.u_tr bk.ι) (hβ k) (hu k) (hj k) hj' ?_
  exact sum_smul_column_eq b b' f U U' _ hY k

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedFCrystalOfStratifiedPhiModuleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framed_fCrystal_of_stratifiedPhiModule : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d), ∃ (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e := by
  first | exact @GlobalTheory.BSP.StratCrys.exists_framed | exact GlobalTheory.BSP.StratCrys.exists_framed | (intros; apply GlobalTheory.BSP.StratCrys.exists_framed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCrystalStratificationMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysStrat

theorem single_mem_M {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (σ : ZMod a) (j : ι) :
    (Pi.single σ (Pi.single j (1 : K⟦X⟧)) : Vec K a ι) ∈ P.M := by
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  by_cases h : τ = σ
  · subst h; rw [Pi.single_eq_same]
    by_cases h' : i = j
    · subst h'; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne h']; exact zero_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem mulVec_single_one' {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M : Matrix ι ι R) (j i : ι) :
    (M *ᵥ Pi.single j 1) i = M i j := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_stratification : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (sh : (↥LL.1)⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧) (φ₂ : (↥LL.1)⟦X⟧⟦X⟧ →+* (↥LL.1)⟦X⟧⟦X⟧), (∀ (f : (↥LL.1)⟦X⟧) (i : ℕ), (i.factorial : (↥LL.1)⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := ↥LL.1))^[i] f) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob (↥LL.1) l f)) → (∀ f : (↥LL.1)⟦X⟧, φ₂ (sh f) = sh (frob (↥LL.1) l f)) → ∃ ε : ZMod a → Matrix ι ι (↥LL.1)⟦X⟧⟦X⟧, (∀ τ, (ε τ).map PowerSeries.constantCoeff = 1) ∧ (∀ τ, ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh = ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) ∧ ∀ (τ : ZMod a) (i j : ι) (k : ℕ), (k.factorial : (↥LL.1)⟦X⟧) * coeff k (ε τ i j) ∈ S (↥(OL LL)) (↥LL.1) e := by
  intro hBS l _ a e _ _ ϖ LL _ _ hl ι _ _ P T I hBK sh φ₂ hsh hφC hφsh
  obtain ⟨EE, c, hinj, hcM, hsurj, hsemi, hO, hfr⟩ := GlobalTheory.T.breuilKisinPrism_crystal_coordinates l a e _ _ (thetaW a LL) ϖ ι P _ _ hBS hBK
  obtain ⟨PP, S₀, p₀, p₁, δ, j, j₀, hI, hδ, hj₀, hjp, hjφ, hS, hS', -⟩ :=
    GlobalTheory.T.exists_crystalline_prisms l a e (↥(OL LL)) (↥LL.1) (thetaW a LL) ϖ hl sh φ₂ hsh hφC hφsh
  obtain ⟨lam₀, hl₀, hv₀⟩ := _root_.GlobalTheory.CrysExt.exists_coord l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₀ j PowerSeries.C
    (fun τ w => (hjp τ w).1)
  obtain ⟨lam₁, hl₁, hv₁⟩ := _root_.GlobalTheory.CrysExt.exists_coord l a e _ _ (thetaW a LL) ϖ ι EE c hsemi PP p₁ j sh
    (fun τ w => (hjp τ w).2)
  obtain ⟨ε, hε⟩ := GlobalTheory.T.crystalline_phi_module_map_exists l a e _ _ (thetaW a LL) ϖ ι P EE c hinj hcM hsurj hsemi hO sh hsh PP p₀ p₁ j hjp
    lam₀ lam₁ hl₀ hl₁ hv₀ hv₁
  have hsh0 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by
    simpa using hsh f 0

  have hcol : ∀ (τ : ZMod a) (jj : ι), ∃ x, c x = Pi.single (τ - 1) (Pi.single jj 1) :=
    fun τ jj => hsurj _ (single_mem_M P _ jj)
  have hv1 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      lam₁ (EE.tr p₁ x) τ = Pi.single jj 1 := fun τ jj x hx => funext fun i => by
    rw [hv₁, hx, Pi.single_eq_same]
    by_cases h : i = jj
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hv0 : ∀ (τ : ZMod a) (jj : ι) (x : EE.M (ϖ.prism a)), c x = Pi.single (τ - 1) (Pi.single jj 1) →
      ∀ i, lam₀ (EE.tr p₁ x) τ i = ε τ i jj := fun τ jj x hx i => by
    rw [hε, hv1 τ jj x hx, mulVec_single_one']
  have hlK : (l : ↥LL.1) ≠ 0 := by
    have h := (map_ne_zero (algebraMap ℚ_[l] ↥LL.1)).2
      (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0)
    rwa [map_natCast] at h
  have hl0 : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ≠ 0 := fun h => hlK (by
    have := congrArg (fun f => PowerSeries.constantCoeff (PowerSeries.constantCoeff f)) h
    simpa using this)
  refine ⟨ε, fun τ => ?_, fun τ => ?_, fun τ i jj k => ?_⟩
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol τ jj
    rw [Matrix.map_apply, ← hv0 τ jj x hx i,
      GlobalTheory.T.crystal_coordinates_constantCoeff_eq l a e _ _ (thetaW a LL) ϖ ι EE c hsemi sh hsh PP S₀ p₀ p₁ δ j j₀ hδ hj₀ hjp lam₀ lam₁ hl₀ hl₁ hv₀ hv₁,
      hv1 τ jj x hx, Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  · refine Matrix.ext fun i jj => ?_
    obtain ⟨x, hx⟩ := hcol (τ - 1) jj
    have hlI : ((l : ℕ) : PP.A) ∈ PP.I := by rw [hI]; exact Ideal.mem_span_singleton_self _
    obtain ⟨n, k, hn⟩ := exists_isFrac ((l : ℕ) : PP.A) (EE.Φ PP ⟨_, hlI⟩ (EE.tr p₁ x))
    have G₀ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₀ j PowerSeries.C φ₂
      (fun τ w => (hjp τ w).1) hjφ hφC (PowerSeries.C_injective) lam₀ hl₀ hv₀ _ n k hn τ i
    have G₁ := GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates l a e _ _ (thetaW a LL) ϖ ι P EE c hsemi hfr PP hlI p₁ j sh φ₂
      (fun τ w => (hjp τ w).2) hjφ hφsh (fun f g h => by rw [← hsh0 f, ← hsh0 g, h]) lam₁ hl₁ hv₁ _ n k hn
    have hy1 := hv1 (τ - 1) jj x hx
    have hy0 : ∀ m, lam₀ (EE.tr p₁ x) (τ - 1) m = ε (τ - 1) m jj := hv0 (τ - 1) jj x hx
    have hE := congrFun (hε n τ) i
    rw [G₀] at hE
    simp only [Matrix.mulVec, dotProduct, G₁, hy1, hy0] at hE
    have key : ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k *
        (((P.mx (τ - 1)).map (frob (↥LL.1) l)).map PowerSeries.C * (ε (τ - 1)).map φ₂) i jj =
        ((l : ℕ) : (↥LL.1)⟦X⟧⟦X⟧) ^ k * (ε τ * ((P.mx (τ - 1)).map (frob (↥LL.1) l)).map sh) i jj := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have h1 : ∀ q, φ₂ ((Pi.single jj (1 : (↥LL.1)⟦X⟧⟦X⟧) : ι → (↥LL.1)⟦X⟧⟦X⟧) q) =
          (Pi.single jj 1 : ι → (↥LL.1)⟦X⟧⟦X⟧) q := fun q => by
        by_cases h : q = jj
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      simp only [h1] at hE
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
        Finset.mem_univ, if_true] at hE
      simp only [Matrix.map_apply] at hE ⊢
      rw [hE, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    exact (mul_left_cancel₀ (pow_ne_zero k hl0) key).symm
  · obtain ⟨x, hx⟩ := hcol τ jj
    rw [← hv0 τ jj x hx i]
    exact _root_.GlobalTheory.BKGal.CrysInteg.factorial_mul_coeff_mem l a e _ _ (thetaW a LL) ϖ ι P EE c hcM PP p₀ j hS' lam₀ hl₀ hv₀ _ τ i k

end GlobalTheory.CrysStrat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLogUniformizerTiltBdRPlusCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem eD_smul_tB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l} (hF : Fits T C)
    (z : ℤ_[l]) :
    T.eD (P.ιB ((z : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l z) * C.j C.t) := by
  rw [map_smul, Algebra.smul_def, map_mul, T.zD, hF.ι, hF.t, Core.tB, C.ι_j, map_mul, GlobalTheory.RingIface.zD_eq_alg]
  simp only [aDp, RingHom.comp_apply]

theorem exists_mem_FilD_neg (C : Core l) (x : Per.BdR l) : ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ)) := by
  have he := _root_.GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨n, y, hy⟩ := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.2 C.ε he x
  refine ⟨n, (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε he _ x).2 ⟨y, ?_⟩⟩
  simpa using hy

theorem const_eq_zero_of_mem_Fil_one {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (K : FinExt l) (c : ↥K.1) (hc : algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil 1) : c = 0 := by
  have h1 := (T.fil K 1 _).1 hc
  have e : algebraMap ↥K.1 P.R.BdR c = algebraMap (Om l) P.R.BdR (c : Om l) := rfl
  rw [e, hF.o] at h1
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast h1)
  have hz' : z = C.o (c : Om l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 hze
  have h0 : Per.θD l z = 0 := by
    have := (GlobalTheory.MemLoc.thetaD_onto_ker l).2
    rw [← this] at hz
    exact hz
  rw [hz', C.o_sec.th] at h0
  have : (c : Om l) = 0 := (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
  exact Subtype.ext this

end GlobalTheory.LogFlatLam

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem σD_alg (g : GQ l) (x : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g x) :=
  GlobalTheory.RingIface.sigD_alg l g x

theorem σDp_alg (g : GQ l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : GQ l) (a : Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

end GlobalTheory.LogFlatLam


open GlobalTheory.LogFlatLam in
theorem GlobalTheory.LogFlatLam.exists_lam : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  rintro l _ K bk P AI T C hF b c ⟨hact, -⟩ - happrox
  obtain ⟨ι, hιC, hιg⟩ := GlobalTheory.BstLog.iota_exists l P AI T
  have hinj := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  set yA := ι (Polynomial.X + Polynomial.C b) with hyA
  have hy : ∀ g : ↥(GK K), P.actQdR (g : GQ l) yA = yA + P.ιB ((c g : ℚ_[l]) • P.tB) := by
    intro g
    rw [hyA, ← hιg, hact g, map_add (f := _), hιC]
  have hKc : ∀ (g : ↥(GK K)) (d : ↥K.1), P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR d) =
      algebraMap ↥K.1 P.R.BdR d := by
    intro g d
    rw [← P.PD_actdR K g, AlgEquiv.commutes]
  obtain ⟨n, hn⟩ := exists_mem_FilD_neg C (T.eD yA)
  have hn' : yA ∈ (P.PD K).Fil (-(n : ℤ)) := (T.fil K _ _).2 hn
  have hg1 : ∀ g : ↥(GK K), (P.PD K).actdR g yA - yA ∈ (P.PD K).Fil 1 := by
    intro g
    rw [P.PD_actdR, hy, add_sub_cancel_left]
    refine (T.fil K 1 _).2 ?_
    rw [eD_smul_tB hF]
    exact_mod_cast (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2
      ⟨_, Ideal.mul_mem_left _ _ (GlobalTheory.MemLoc.core_t_unit_fil l C).2.1, rfl⟩
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K (-(n : ℤ)) 1 yA hn' hg1
  set lamA := yA - algebraMap ↥K.1 P.R.BdR c0 with hlamA
  obtain ⟨lam, hlam1, hlamE⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast (T.fil K 1 lamA).1 hc0)
  have hequiv : ∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t := by
    intro g
    apply hinj
    rw [map_add (f := _), ← σD_alg, hlamE, ← T.actD, hlamA, map_sub, hKc, hy]
    simp only [map_sub, map_add (f := _), eD_smul_tB hF]
    ring
  refine ⟨lam, hequiv, fun m => ?_⟩
  obtain ⟨k, s, hEs, hs⟩ := happrox m
  refine ⟨k, s, hEs, ?_⟩
  set x := aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam with hx
  set xA := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) x) with hxA
  have hxA' : T.eD xA = algebraMap (Per.BdRp l) (Per.BdR l) x := by rw [hxA, RingEquiv.apply_symm_apply]
  have hx1 : xA ∈ (P.PD K).Fil 1 := by
    refine (T.fil K 1 _).2 ?_
    rw [hxA']
    refine (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2 ⟨x, ?_, rfl⟩
    refine Ideal.sub_mem _ (((GlobalTheory.AinfEPow.ePow_facts l K bk 1).2.2.1 _).2 ?_) (Ideal.mul_mem_left _ _ hlam1)
    rw [pow_one]
    exact map_dvd _ hEs
  have hxg : ∀ g : ↥(GK K), (P.PD K).actdR g xA - xA ∈ (P.PD K).Fil (m : ℤ) := by
    intro g
    refine (T.fil K _ _).2 ?_
    rw [map_sub, P.PD_actdR, T.actD, hxA', σD_alg, ← map_sub]
    refine (GlobalTheory.BdRQuot.mem_FilD_nat m _).2 ⟨_, ?_, rfl⟩
    have e : Per.σDp (g : GQ l) x - x = aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) := by
      rw [hx, map_sub, map_mul, map_pow, map_natCast, σDp_aDp, hequiv, map_sub]
      ring
    rw [e]
    exact hs g
  obtain ⟨c', hc'1, hc'm⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K 1 (m : ℤ) xA hx1 hxg
  have hc'0 : c' = 0 := const_eq_zero_of_mem_Fil_one hF K c' hc'1
  rw [hc'0, map_zero, sub_zero] at hc'm
  have h := (T.fil K _ _).1 hc'm
  rw [hxA'] at h
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat m _).1 h
  rw [← hinj hze]
  exact hz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonodromyFrobeniusSolutionFilStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monodromy_frobenius_solution_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (ι : Bst P →ₐ[ℚ_[l]] P.R.BdR), (∀ b, ι (Polynomial.C b) = P.ιB b) → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (x y : V ⊗[ℚ_[l]] Bst P), (l : ℚ_[l]) • phiV P ℚ_[l] V x - x = monV P ℚ_[l] V y → ∃ z : V ⊗[ℚ_[l]] Bst P, monV P ℚ_[l] V z = x ∧ phiV P ℚ_[l] V z - z = y ∧ LinearMap.lTensor V ι.toLinearMap z ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0 := by
  first | exact @GlobalTheory.PMon.solve_mon_phi_fil | exact GlobalTheory.PMon.solve_mon_phi_fil | (intros; apply GlobalTheory.PMon.solve_mon_phi_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistablePeriodMatrixOfIsSemistable
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_periodMatrix_of_isSst : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P ρ → ∃ Q : GL n (Bst P), ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] (Bst P)) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ h
  obtain ⟨hdom, hreg, hu⟩ := stRegular l P AI ⟨T⟩
  obtain ⟨e, -, -, he⟩ := _root_.GlobalTheory.tensorBasisCoords ℚ_[l] (Bst P) V n b
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hK0 : ∀ c : ↥(K0 K), algebraMap ↥(K0 K) (Bst P) c = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) ⟨c, c.2.2⟩ :=
    fun c => rfl
  have hst : ∀ (g : ↥(GK K)) (y : V ⊗[ℚ_[l]] Bst P),
      stRep P ρ g y = TensorProduct.map (ρ g) (actSt P (g : GQ l)).toLinearMap y := fun g y => rfl
  refine GlobalTheory.T.exists_periodMatrix_of_finrank_alt ℚ_[l] ↥(K0 K) (Bst P) ↥(GK K)
    (fun g => (actSt P (g : GQ l) : Bst P →+* Bst P)) n (fun g => LinearMap.toMatrix b b (ρ g))
    (fun g => ?_) (fun g c => ?_) (fun x x' hx hh => ?_) (fun x hx hh => hu K x hx hh)
    ((Dst P ρ).map e.toLinearMap) (fun x => ?_) ?_
  · have h1 : LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g⁻¹) = 1 := by
      rw [← LinearMap.toMatrix_mul, ← map_mul, mul_inv_cancel, map_one, LinearMap.toMatrix_one]
    exact (Matrix.isUnit_det_of_right_inverse h1).ne_zero
  · rw [hK0]
    exact actSt_algebraMap P g _ _ (mem_GK.mp g.2 _ c.2.1)
  · obtain ⟨c, hc, hc'⟩ := hreg K x x' hx hh
    exact ⟨⟨c, hc, c.2⟩, by rw [hK0]; exact hc'⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    have h1 : e y ∈ (Dst P ρ).map e.toLinearMap ↔ y ∈ Dst P ρ := by
      rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]
    rw [h1, mem_Dst]
    refine forall_congr' fun g => ?_
    rw [hst, ← e.injective.eq_iff, he]
    rfl
  · rw [LinearEquiv.finrank_map_eq, h, finrank_eq_card_basis b]

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionsLowAndPullbackRecord
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.LowLevel


set_option maxHeartbeats 1000000 in
theorem expansions_low_and_pullback_record : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ (i : Let K) (ζ : ↥LL.1), (∃ m : ℕ, ζ ^ (((D.loc l).PD K).p ^ m) = 1) → PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 → (∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : AA K LL) • x) k ∈ ιDi W T i ∧ (k < 0 → W.levN T i ζ x k = 0)) ∧ Submodule.span ↥LL.1 (Set.range fun x : ↥(W.N T) => W.levN T i ζ ((letE i : AA K LL) • x) 0) = ιDi W T i) ∧ ∀ (i : Let K) (ζ : ↥LL.1) τ, ptK D.loc HW h i ζ τ → (∀ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T) (j : ℤ), W.levN T i ζ ⟨_, hk⟩ j ∈ ιDi W T i ∧ (j < k → W.levN T i ζ ⟨_, hk⟩ j = 0)) ∧ Submodule.span ↥LL.1 {w | ∃ (x : ↥(W.N T)) (k : ℕ) (hk : W.Q ^ k • W.φD T x ∈ W.N T), w = W.levN T i ζ ⟨_, hk⟩ k} = ιDi W T i :=
  expansions_low_and_pullback

end GlobalTheory.NL.LowLevel
end

