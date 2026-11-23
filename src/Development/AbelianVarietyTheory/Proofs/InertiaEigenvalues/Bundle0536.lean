module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DeRhamIdent

section Generic

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
  [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem TWincl_inj {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G ℚ_[l] K O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem fix_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) (r : R)
    (hr : IsUnit r) (m : M) (h : f (r • m) = r • m) : f m = m := by
  obtain ⟨u, rfl⟩ := hr
  have h2 := congrArg (fun y => ((u⁻¹ : Rˣ) : R) • y) h
  simp only [← map_smul, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

end Generic

section Incl

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ι : Type)

theorem inclV_apply (c : ι → OA l O) (i : ι) : inclV l O ι c i = inclO l O (c i) := rfl

theorem inclV_smul (r : OA l O) (c : ι → OA l O) : inclV l O ι (r • c) = inclO l O r • inclV l O ι c := by
  funext i
  simp only [inclV_apply, Pi.smul_apply, smul_eq_mul, map_mul]

theorem inclV_inj [Module.Free ℤ_[l] O] : Function.Injective (inclV l O ι) := fun c d h =>
  funext fun i => inclO_injective (congrFun h i)

end Incl

end GlobalTheory.DeRhamIdent

namespace GlobalTheory.DeRhamIdent

open GlobalTheory.DeRhamIdent


set_option maxHeartbeats 2000000 in
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨⟨ε, hε⟩, hεall⟩ := _root_.GlobalTheory.MuOfEps.main l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2

  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  set u : (OD l O)ˣ := hu.unit with hudef
  have hu' : (u : OD l O) = toOD l O ν := hu.unit_spec
  have hV := inclV_inj l O ι

  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  have hsum : ∀ c : ι → OA l O,
      inclV l O ι c = ∑ i, inclO l O (c i) • inclV l O ι (Pi.single i 1) := by
    intro c
    funext j
    simp [inclV_apply, Finset.sum_apply, Pi.single_apply]
  have hJ0 : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ν ^ α • z' = ∑ i, c i • z i := by
    intro c z' h
    apply TWincl_inj (inclO l O) inclO_injective T
    calc TWincl (inclO l O) T (ν ^ α • z') = inclO l O (ν ^ α) • I.j (inclV l O ι c) := by
          rw [TWincl_smul, h]
      _ = ∑ i, inclO l O (c i) • I.j (inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [← I.j.map_smul, hsum c, Finset.smul_sum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, I.j.map_smul]
      _ = TWincl (inclO l O) T (∑ i, c i • z i) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hz i, TWincl_smul]
  let w : ι → TW (OD l O) T := fun i => ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • TWincl (toOD l O) T (z i)
  let jD : (ι → OD l O) →ₗ[OD l O] TW (OD l O) T := ∑ i, (LinearMap.proj i).smulRight (w i)
  have hjD : ∀ d, jD d = ∑ i, d i • w i := fun d => by
    simp [jD, LinearMap.sum_apply]
  have hJ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z' := by
    intro c z' h
    have h2 : toOD l O (ν ^ α) • TWincl (toOD l O) T z' =
        ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← TWincl_smul, hJ0 c z' h, map_sum]
      simp only [TWincl_smul]
    rw [hjD]
    calc ∑ i, toOD l O (c i) • w i
        = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • (toOD l O (ν ^ α) • TWincl (toOD l O) T z') := by rw [h2]
      _ = TWincl (toOD l O) T z' := by
          rw [smul_smul, map_pow, ← hu', ← mul_pow, Units.inv_mul, one_pow, one_smul]

  have hK1' : ∀ x, ∃ y, inclV l O ι y = inclO l O (ν ^ β) • I.ofT x := fun x => LinearMap.mem_range.1 (hK1 x)
  choose Cx hC using hK1'
  let C : ↥T.L.T →ₗ[O] (ι → OA l O) :=
    { toFun := Cx
      map_add' := fun x y => hV (by rw [map_add (f := _), hC, hC, hC, map_add (f := _), smul_add])
      map_smul' := fun o x => hV (by rw [map_smul, hC, hC, map_smul, RingHom.id_apply, smul_comm]) }
  let CA : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) := LinearMap.liftBaseChange (OA l O) C
  have hP1 : ∀ z' : TW (OA l O) T,
      inclV l O ι (CA z') = inclO l O (ν ^ β) • I.j.symm (TWincl (inclO l O) T z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _), smul_add]
    | tmul b x =>
      have e1 : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
        simp [TWincl, TensorProduct.smul_tmul']
      have e2 : I.j.symm ((1 : OW l O) ⊗ₜ[O] x) = I.ofT x := rfl
      rw [e1, I.j.symm.map_smul, e2, LinearMap.liftBaseChange_tmul, inclV_smul]
      change inclO l O b • inclV l O ι (Cx x) = _
      rw [hC, smul_comm]
  let ψ : TW (OD l O) T →ₗ[OD l O] (ι → OD l O) := ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β •
    LinearMap.liftBaseChange (OD l O) (((toOD l O).toLinearMap.compLeft ι) ∘ₗ C)
  have hP2 : ∀ z' : TW (OA l O) T,
      ψ (TWincl (toOD l O) T z') = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β • fun i => toOD l O (CA z' i) := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      funext i
      simp
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), hx, hy, ← smul_add]
      congr 1
      funext i
      simp
    | tmul b x =>
      simp only [ψ, CA, TWincl, LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, LinearMap.liftBaseChange_tmul]
      congr 1
      funext i
      simp [C, LinearMap.compLeft, map_mul]
  have hΨ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ψ (TWincl (toOD l O) T z') = fun i => toOD l O (c i) := by
    intro c z' h
    have h1 : CA z' = ν ^ β • c := hV (by rw [hP1, ← h, I.j.symm_apply_apply, inclV_smul])
    rw [hP2, h1]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu', ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have h1 : jD ∘ₗ ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d x
    have e0 : d ⊗ₜ[O] x = d • ((1 : OD l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e0, map_smul, map_smul]
    congr 1
    have hx : I.j (inclV l O ι (Cx x)) = TWincl (inclO l O) T ((ν ^ β) ⊗ₜ[O] x) := by
      rw [hC, I.j.map_smul, I.j_ofT]
      simp [TWincl, TensorProduct.smul_tmul']
    have e3 : TWincl (toOD l O) T ((ν ^ β) ⊗ₜ[O] x) = ((u : OD l O) ^ β) • ((1 : OD l O) ⊗ₜ[O] x) := by
      simp [TWincl, TensorProduct.smul_tmul', hu']
    refine fix_of_unit (jD ∘ₗ ψ) ((u : OD l O) ^ β) ((Units.isUnit u).pow β) _ ?_
    rw [← e3, LinearMap.comp_apply, hΨ _ _ hx, hJ _ _ hx]
  have h2 : ψ ∘ₗ jD = LinearMap.id := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    have hzi : I.j (inclV l O ι (Pi.single i (ν ^ α))) = TWincl (inclO l O) T (z i) := by rw [hc, hz i]
    have e4 : (fun j => toOD l O ((Pi.single i (ν ^ α) : ι → OA l O) j)) =
        ((u : OD l O) ^ α) • (LinearMap.single (OD l O) (fun _ => OD l O) i 1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hu', map_pow]
      · simp [Pi.single_apply, hj]
    refine fix_of_unit (ψ ∘ₗ jD) ((u : OD l O) ^ α) ((Units.isUnit u).pow α) _ ?_
    rw [← e4, LinearMap.comp_apply, hJ _ _ hzi, hΨ _ _ hzi]
  exact ⟨LinearEquiv.ofLinear jD ψ h1 h2, fun c z' h => hJ c z' h⟩

end GlobalTheory.DeRhamIdent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinset
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

namespace GlobalTheory.Pass.LocDual

theorem lenMod_eq_height_map {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S H : Submodule O M) : BlochKatoDuality.lenMod S H = Order.height (S.map H.mkQ) := by
  show Module.length O (↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype) = _
  have hker : LinearMap.ker (H.mkQ ∘ₗ (S ⊔ H).subtype) = H.comap (S ⊔ H).subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range (H.mkQ ∘ₗ (S ⊔ H).subtype) = S.map H.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_sup, Submodule.mkQ_map_self,
      sup_bot_eq]
  rw [← Module.length_submodule]
  exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((H.mkQ ∘ₗ (S ⊔ H).subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))).length_eq

theorem height_map_span_le_of_finset {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (f : M →ₗ[O] N) (S : Set M) (b : ℕ∞)
    (h : ∀ F : Finset M, (↑F : Set M) ⊆ S →
      Order.height ((Submodule.span O (↑F : Set M)).map f) ≤ b) :
    Order.height ((Submodule.span O S).map f) ≤ b := by
  classical
  rw [Order.height_le_iff]
  intro p hp

  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hxin hxout using hx

  have hfin : ∀ i : Fin p.length, ∃ F : Finset M, (↑F : Set M) ⊆ S ∧
      x i ∈ (Submodule.span O (↑F : Set M)).map f := by
    intro i
    have hxi : x i ∈ (Submodule.span O S).map f := hp (p.monotone (Fin.le_last i.succ) (hxin i))
    obtain ⟨y, hyS, hyx⟩ := Submodule.mem_map.mp hxi
    obtain ⟨T, hTS, hyT⟩ := Submodule.mem_span_finite_of_mem_span hyS
    exact ⟨T, hTS, Submodule.mem_map.mpr ⟨y, hyT, hyx⟩⟩
  choose F hFS hxF using hfin
  let G : Finset M := Finset.univ.biUnion F
  have hGS : (↑G : Set M) ⊆ S := by
    intro z hz
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
    exact hFS i hi
  have hFG : ∀ i, Submodule.span O (↑(F i) : Set M) ≤ Submodule.span O (↑G : Set M) := fun i =>
    Submodule.span_mono (fun z hz => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

  let Q := (Submodule.span O (↑G : Set M)).map f
  let q : LTSeries (Submodule O N) := LTSeries.mk p.length (fun j => p j ⊓ Q) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    dsimp only
    refine lt_of_le_of_ne (inf_le_inf_right _ (p.monotone (Fin.castSucc_le_succ i))) ?_
    intro heq
    have h1 : x i ∈ p i.succ ⊓ Q :=
      Submodule.mem_inf.mpr ⟨hxin i, Submodule.map_mono (hFG i) (hxF i)⟩
    rw [← heq] at h1
    exact hxout i (Submodule.mem_inf.mp h1).1)
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height Q := Order.length_le_height inf_le_right
    _ ≤ b := h G hGS

theorem lenMod_span_le_of_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  intro O M _ _ _ S H b h
  rw [lenMod_eq_height_map]
  apply height_map_span_le_of_finset H.mkQ S b
  intro F hF
  rw [← lenMod_eq_height_map]
  exact h F hF

end GlobalTheory.Pass.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfBlochKatoLiftingFamilyAtPlace
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Pass.LocDirect

theorem isSubFam_of_fintype {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (W : GRep G Qp LL O)
    {κ : Type} [Fintype κ] (x : κ → ι) (p : κ → W.V →ₗ[LL] (Fin k → LL))
    (h1 : ∀ j g v, p j (W.ρ g v) = (Ms (x j) g).mulVec (p j v)) (h2 : ∀ v, (∀ j, p j v = 0) → v = 0) :
    IsSubFam Ms W := by
  classical
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun m => x (e.symm m), fun m => p (e.symm m), fun m g v => h1 _ g v,
    fun v hv => h2 v fun j => ?_⟩
  simpa using hv (e j)

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    Br.loc D.nbr i w hw M g =
      (mapM (toK D.nd i) M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd)).map (Br.toLLK (D.nbr i w hw)) := by
  ext a b
  simp only [Br.loc, Br.locM, Br.locO, mapM, MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, RingHom.mapMatrix_apply, Matrix.map_apply, toK]
  exact congrArg Subtype.val (Br.toLLK_alg (D.nbr i w hw) _).symm

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem exists_locEmb (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (x₀ : D.nd.X i)
    (j : (Fin k → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i)) (hj : Function.Injective j)
    (hjM : ∀ g v, j ((mapM (toK D.nd i) M g).mulVec v) = (mapM (toK D.nd i) (rTwO D.nd i r x₀) g).mulVec (j v)) :
    ∃ J : Matrix (Fin D.R.nV) (Fin k) (Br.LL D.nbr i w hw),
      (∀ v, J.mulVec v = 0 → v = 0) ∧
      ∀ g, J * Br.loc D.nbr i w hw M g = Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g * J := by
  classical
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  have hLJ : LinearMap.toMatrix' l * LinearMap.toMatrix' j = 1 := by
    rw [← LinearMap.toMatrix'_comp, hl, LinearMap.toMatrix'_id]
  have hJM : ∀ γ, LinearMap.toMatrix' j * mapM (toK D.nd i) M γ =
      mapM (toK D.nd i) (rTwO D.nd i r x₀) γ * LinearMap.toMatrix' j := by
    intro γ
    have e : j ∘ₗ Matrix.toLin' (mapM (toK D.nd i) M γ) =
        Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r x₀) γ) ∘ₗ j := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, hjM]
    have := congrArg LinearMap.toMatrix' e
    simpa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] using this
  set f := Br.toLLK (D.nbr i w hw)
  refine ⟨(LinearMap.toMatrix' j).map f, fun v hv => ?_, fun g => ?_⟩
  · have h1 : ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f) = 1 := by
      rw [← Matrix.map_mul, hLJ, Matrix.map_one _ (map_zero f) (map_one f)]
    calc v = ((LinearMap.toMatrix' l).map f * (LinearMap.toMatrix' j).map f).mulVec v := by
          rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [loc_eq_map, loc_eq_map, ← Matrix.map_mul, ← Matrix.map_mul, hJM]

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isSubFam_of_isSubSumOf (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))
    {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
    (hM : Continuous fun g => M g) {a : ℕ} (x : Fin a → D.nd.X i) (hx : ∀ j, x j ∈ Xs)
    (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y,
      (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)
    (Wr : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
    (h : BlochKatoDuality.IsSubSumOf Wr.ρ (Xgrep i w hw r x hc Y hst).ρ (ModuleGaloisRepresentation i w hw M hM).ρ) :
    IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rTwO D.nd i r x)) Wr := by
  classical
  obtain ⟨-, x₀, hx₀, j, hj, hjM⟩ := hSub
  obtain ⟨J, hJi, hJ⟩ := exists_locEmb i w hw r M x₀ j hj hjM
  obtain ⟨a', b', p, q, hp, hq, hinj⟩ := h
  let cX : Fin a → (↥(XV i w hw Y) →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw)) :=
    fun m => LinearMap.proj m ∘ₗ (XV i w hw Y).subtype
  let P : (Fin a' × Fin a) ⊕ Fin b' → Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw) :=
    Sum.elim (fun ij => cX ij.2 ∘ₗ (p ij.1 : Wr.V →ₗ[Br.LL D.nbr i w hw] ↥(XV i w hw Y)))
      (fun m => Matrix.mulVecLin J ∘ₗ (q m : Wr.V →ₗ[Br.LL D.nbr i w hw] (Fin k → Br.LL D.nbr i w hw)))
  let xf : (Fin a' × Fin a) ⊕ Fin b' → ↥Xs := Sum.elim (fun ij => ⟨x ij.2, hx ij.2⟩) (fun _ => ⟨x₀, hx₀⟩)
  refine isSubFam_of_fintype _ Wr xf P ?_ ?_
  · rintro (⟨m, n⟩ | m) g v
    · have e1 := hp m g v
      change cX n (p m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r (x n)) g).mulVec (cX n (p m v))
      rw [e1]
      rfl
    · have e1 := hq m g v
      change J.mulVec (q m (Wr.ρ g v)) = (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec (q m v))
      rw [e1]
      have key : ∀ u : Fin k → Br.LL D.nbr i w hw, J.mulVec ((Br.loc D.nbr i w hw M g).mulVec u) =
          (Br.loc D.nbr i w hw (rTwO D.nd i r x₀) g).mulVec (J.mulVec u) := fun u => by
        rw [Matrix.mulVec_mulVec, hJ, ← Matrix.mulVec_mulVec]
      exact key (q m v)
  · intro v hv
    refine hinj v (fun m => ?_) (fun m => hJi _ (hv (Sum.inr m)))
    apply Subtype.ext
    funext n
    exact hv (Sum.inl (m, n))

end GlobalTheory.Pass.LocDirect

namespace GlobalTheory.Pass.LocDirect

theorem liftAll_of_liftFamW : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (e : ℕ), LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e →
    ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M →
    ∀ (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) →
    ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g)
      (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
      (hst : (∀ γ : GE D.nd, ∀ y ∈ Y,
        (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)),
    BlochKatoDuality.LiftAll (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst)
      (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) e := by
  intro D i w hw r _ Xs e hL k M hSub hM a x hx hc Y hst W₁ W₂ h₁ h₂ L₁ L₂ F hF
  exact hL W₁ W₂ (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₁ h₁)
    (isSubFam_of_isSubSumOf i w hw r Xs M hSub hM x hx hc Y hst W₂ h₂) L₁ L₂ F hF

end GlobalTheory.Pass.LocDirect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleDescentFiniteLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedPhiModule_descent_finite_level : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C D : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C) (p q : Hom C D), Cover h → IsPO h h p q → ∀ m : ℕ, letI := (qmap h m).toAlgebra; ∃ N : Submodule (B.A ⧸ adI B ^ m) (Fin d → C.A ⧸ adI C ^ m), (∀ z, z ∈ N ↔ (fun i => qmap p m (z i)) = ((S.ε (p.comp f) (q.comp f)).map (Ideal.Quotient.mk (adI D ^ m))).mulVec fun i => qmap q m (z i)) ∧ Module.Finite (B.A ⧸ adI B ^ m) ↥N ∧ Module.Projective (B.A ⧸ adI B ^ m) ↥N ∧ IsBaseChange (C.A ⧸ adI C ^ m) N.subtype := by
  first | exact @GlobalTheory.BSP.LevH.descent_at_level | exact GlobalTheory.BSP.LevH.descent_at_level | (intros; apply GlobalTheory.BSP.LevH.descent_at_level <;> assumption)
end

