module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BrEqv
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BranchingMultiplicityOneUnitaryFamilies
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0300
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.KJAvg

open GlobalTheory.BranchFormula

def blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 1)

theorem blk_castSucc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    blk A a.castSucc b.castSucc = A a b := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_castSucc_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) :
    blk A a.castSucc (Fin.last n) = 0 ∧ blk A (Fin.last n) a.castSucc = 0 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : blk A (Fin.last n) (Fin.last n) = 1 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem blk_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : blk (A * B) = blk A * blk B := by
  simp [blk, Matrix.fromBlocks_multiply]

theorem blk_cont {n : ℕ} : Continuous (blk (n := n)) := by
  unfold blk
  fun_prop

theorem blk_mul_cont {X : Type} [TopologicalSpace X] {n : ℕ} (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Continuous fun x => blk (f x) * B :=
  (blk_cont.comp hf).matrix_mul continuous_const

theorem isBlock_blk {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : IsBlock (rfl : n + 1 = n + 1) (blk A) A 1 := by
  refine ⟨fun a b => ?_, fun a => ?_, ?_⟩
  · exact blk_castSucc A a b
  · exact blk_castSucc_last A a
  · exact blk_last A

theorem eq_blk {n : ℕ} {A' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {A : Matrix (Fin n) (Fin n) ℂ}
    (h : IsBlock (rfl : n + 1 = n + 1) A' A 1) : A' = blk A := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rw [blk_last]; exact h.2.2
    | cast b => rw [(blk_castSucc_last A b).2]; exact (h.2.1 b).2
  | cast a =>
    induction j using Fin.lastCases with
    | last => rw [(blk_castSucc_last A a).1]; exact (h.2.1 a).1
    | cast b => rw [blk_castSucc]; exact h.1 a b

theorem cptU (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin m => Set.pi Set.univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

theorem cont_val {ι : Type} [Fintype ι] {X : Type} [TopologicalSpace X] {a : ℕ} {G : ι → Matrix (Fin a) (Fin a) ℂ}
    {lam : ι → DomWeight a} {Φ : Frames G → ℂ} (hΦ : Φ ∈ ValC G lam) (M : X → ι → Matrix (Fin a) (Fin a) ℂ)
    (hM : Continuous M) (hinv : ∀ x τ, IsUnit (M x τ).det) : Continuous fun x => Φ ⟨M x, hinv x⟩ := by
  obtain ⟨P, -, rfl⟩ := hΦ
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, one_mul]
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun τ _ => ?_
    exact Continuous.zpow₀ ((continuous_apply τ).comp hM).matrix_det _ fun x => Or.inl (hinv x τ).ne_zero
  · exact (MvPolynomial.continuous_eval P).comp
      (continuous_pi fun x => ((continuous_apply x.1).comp hM).matrix_elem x.2.1 x.2.2)

theorem cont_blkfam {ι : Type} [Fintype ι] {n : ℕ} (y : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Continuous fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y τ :=
  continuous_pi fun τ => blk_mul_cont (fun u : ι → Matrix.unitaryGroup (Fin n) ℂ => (u τ).1)
    (continuous_subtype_val.comp (continuous_apply τ)) (y τ)

theorem uniH {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    u * uᴴ = 1 ∧ uᴴ * u = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact ⟨Matrix.mem_unitaryGroup_iff.1 hu, Matrix.mem_unitaryGroup_iff'.1 hu⟩

theorem r_one {ι : Type} [Fintype ι] {m : ℕ} {K : Type} [Group K] [TopologicalSpace K]
    {r : K → ι → Matrix (Fin m) (Fin m) ℂ} (hr : OntoUni r) (τ : ι) : r 1 τ = 1 := by
  have h := hr.mul 1 1 τ
  rw [mul_one] at h
  have hu := (uniH (hr.uni 1 τ)).2
  calc r 1 τ = (r 1 τ)ᴴ * r 1 τ * r 1 τ := by rw [hu, one_mul]
    _ = (r 1 τ)ᴴ * r 1 τ := by rw [mul_assoc, ← h]
    _ = 1 := hu

theorem r_inv_H {ι : Type} [Fintype ι] {m : ℕ} {K : Type} [Group K] [TopologicalSpace K]
    {r : K → ι → Matrix (Fin m) (Fin m) ℂ} (hr : OntoUni r) (k : K) (τ : ι) : (r k⁻¹ τ)ᴴ = r k τ := by
  have h := hr.mul k⁻¹ k τ
  rw [inv_mul_cancel, r_one hr] at h
  calc (r k⁻¹ τ)ᴴ = (r k⁻¹ τ)ᴴ * (r k⁻¹ τ * r k τ) := by rw [← h, mul_one]
    _ = r k τ := by rw [← mul_assoc, (uniH (hr.uni k⁻¹ τ)).2, one_mul]

theorem avg_eq_mul_branch : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ → (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin n) (Fin n) ℂ), OntoUni r → ∀ (y : Frames G) (yk : K → Frames G), (∀ k, ∃ kt, (∀ τ, GlobalTheory.BranchFormula.IsBlock hN (kt τ) (r k τ) 1) ∧ IsTr kt y (yk k)) → ∀ J ∈ ValC G' sg, ∀ Jk : K → Frames G' → ℂ, (∀ k z z', IsTr (r k) z z' → Jk k z' = J z) → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ∫ k, ℓ (Jk k) * Φ (yk k) ∂ν = c * ℓ (T₀ Φ) := by
  intro ι _ N n hN G G' lam sg hI T₀ hT₀ hne K _ _ _ _ _ ν _ _ r hr y yk hyk J hJ Jk hJk
  subst hN
  have hfd' : FiniteDimensional ℂ (ValC G' sg) := (_root_.GlobalTheory.KJInf.valC_poly ι n G' sg).2.1
  have stab' := (_root_.GlobalTheory.KJInf.valC_poly ι n G' sg).2.2.1
  have stab := (_root_.GlobalTheory.KJInf.valC_poly ι (n + 1) G lam).2.2.1
  haveI := cptU n
  have invH : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (z : Frames G') τ, IsUnit (((u τ).1)ᴴ * z.1 τ).det := by
    intro u z τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).1).mul (z.2 τ)
  let zU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → Frames G' → Frames G' := fun u z => ⟨fun τ => ((u τ).1)ᴴ * z.1 τ, invH u z⟩
  have memJ : ∀ u, (fun z => J (zU u z)) ∈ ValC G' sg := by
    intro u
    refine stab' J hJ (fun τ => ((u τ).1)ᴴ) _ (fun z z' h => congrArg J (Subtype.ext (funext fun τ => (h τ).symm))) ?_
    intro τ
    exact Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).1
  let jU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → ValC G' sg := fun u => ⟨_, memJ u⟩
  obtain ⟨e⟩ : Nonempty (ValC G' sg ≃ₗ[ℂ] (Fin (Module.finrank ℂ (ValC G' sg)) → ℂ)) :=
    ⟨(Module.finBasis ℂ (ValC G' sg)).equivFun⟩
  have invB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) τ, IsUnit (blk (u τ).1 * y.1 τ).det := by
    intro u τ
    rw [Matrix.det_mul, (isBlock_blk (u τ).1).det, mul_one]
    exact (Matrix.isUnit_det_of_left_inverse (uniH (u τ).2).2).mul (y.2 τ)
  let yU : (ι → Matrix.unitaryGroup (Fin n) ℂ) → Frames G := fun u => ⟨fun τ => blk (u τ).1 * y.1 τ, invB u⟩
  let r' : K → ι → Matrix.unitaryGroup (Fin n) ℂ := fun k τ => ⟨r k τ, hr.uni k τ⟩
  have hr' : Continuous r' :=
    continuous_pi fun τ => Continuous.subtype_mk ((continuous_apply τ).comp hr.cont) _
  have hyk' : ∀ k, yk k = yU (r' k) := by
    intro k
    obtain ⟨kt, hb, ht⟩ := hyk k
    exact Subtype.ext (funext fun τ => by rw [ht τ, eq_blk (hb τ)])
  have hJk' : ∀ k, Jk k = (jU (r' k)).1 := by
    intro k
    funext z'
    refine hJk k (zU (r' k) z') z' fun τ => ?_
    show z'.1 τ = r k τ * ((r k τ)ᴴ * z'.1 τ)
    rw [← mul_assoc, (uniH (hr.uni k τ)).1, one_mul]
  have hjU : Continuous jU := by
    refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
    exact cont_val hJ (fun u τ => ((u τ).1)ᴴ * z.1 τ)
      (continuous_pi fun τ => ((continuous_apply τ).subtype_val.matrix_conjTranspose).matrix_mul
        continuous_const) (fun u τ => invH u z τ)
  have he : Continuous e := LinearMap.continuous_of_finiteDimensional e.toLinearMap
  have hint : ∀ Ψ ∈ ValC G lam, MeasureTheory.Integrable (fun k => Ψ (yk k) • e (jU (r' k))) ν := by
    intro Ψ hΨ
    have hH : Continuous fun u => Ψ (yU u) • e (jU u) := by
      refine Continuous.smul (f := fun u => Ψ (yU u)) (g := fun u => e (jU u)) ?_ (he.comp hjU)
      show Continuous fun u => Ψ ⟨fun τ => blk (u τ).1 * y.1 τ, invB u⟩
      have hc1 : Continuous fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y.1 τ := cont_blkfam y.1
      exact cont_val (X := ι → Matrix.unitaryGroup (Fin n) ℂ) (M := fun (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (τ : ι) => blk (u τ).1 * y.1 τ) hΨ hc1 invB
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hH.continuousOn
    have hf : (fun k => Ψ (yk k) • e (jU (r' k))) = (fun u => Ψ (yU u) • e (jU u)) ∘ r' := by
      funext k; simp only [Function.comp_apply, hyk']
    rw [hf]
    exact MeasureTheory.Integrable.of_bound (hH.comp hr').aestronglyMeasurable C
      (MeasureTheory.ae_of_all _ fun k => hC _ (Set.mem_univ _))
  let A : ValC G lam →ₗ[ℂ] (Fin (Module.finrank ℂ (ValC G' sg)) → ℂ) :=
    { toFun := fun Ψ => ∫ k, Ψ.1 (yk k) • e (jU (r' k)) ∂ν
      map_add' := fun Ψ Ψ' => by
        simp only [Submodule.coe_add, Pi.add_apply, add_smul]
        exact MeasureTheory.integral_add (hint Ψ.1 Ψ.2) (hint Ψ'.1 Ψ'.2)
      map_smul' := fun c Ψ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact MeasureTheory.integral_smul c _ }
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (ValC G lam).subtype (Submodule.ker_subtype _)
  have hpΨ : ∀ Ψ (h : Ψ ∈ ValC G lam), p Ψ = ⟨Ψ, h⟩ := fun Ψ h => LinearMap.congr_fun hp ⟨Ψ, h⟩
  let T : (Frames G → ℂ) →ₗ[ℂ] (Frames G' → ℂ) := (ValC G' sg).subtype ∘ₗ e.symm.toLinearMap ∘ₗ A ∘ₗ p
  have key : ∀ Ψ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ℓ (T Ψ) = ∫ k, Ψ (yk k) * ℓ (Jk k) ∂ν := by
    intro Ψ hΨ ℓ
    let L := (ℓ ∘ₗ (ValC G' sg).subtype ∘ₗ e.symm.toLinearMap).toContinuousLinearMap
    have h1 : ℓ (T Ψ) = L (A ⟨Ψ, hΨ⟩) := by
      simp only [T, L, LinearMap.coe_comp, Function.comp_apply, hpΨ Ψ hΨ, LinearMap.coe_toContinuousLinearMap']
    rw [h1]
    show L (∫ k, Ψ (yk k) • e (jU (r' k)) ∂ν) = _
    rw [← L.integral_comp_comm (hint Ψ hΨ)]
    congr 1
    funext k
    simp only [L, map_smul, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.subtype_apply, smul_eq_mul, hJk']
  have hT : BrEqv rfl G G' lam sg T := by
    refine ⟨fun Ψ _ => Submodule.coe_mem _, ?_⟩
    intro k0 kt0 hk0 hkt0 Ψ hΨ Ψ' hΨ' z z' hzz'
    have hΨ'm : Ψ' ∈ ValC G lam := by
      refine stab Ψ hΨ kt0 Ψ' hΨ' fun τ => ?_
      rw [(hkt0 τ).det, mul_one]
      exact Matrix.isUnit_det_of_left_inverse (uniH (hk0 τ)).2
    obtain ⟨k1, hk1⟩ := hr.onto k0 hk0
    have e1 : T Ψ' z = ∫ k, Ψ' (yk k) * Jk k z ∂ν := by
      have := key Ψ' hΨ'm (LinearMap.proj z); simpa using this
    have e2 : T Ψ z' = ∫ k, Ψ (yk k) * Jk k z' ∂ν := by
      have := key Ψ hΨ (LinearMap.proj z'); simpa using this
    rw [e1, e2]
    have p1 : ∀ k, Ψ' (yk k) * Jk k z = Ψ (yk (k1 * k)) * Jk (k1⁻¹ * (k1 * k)) z := by
      intro k
      rw [inv_mul_cancel_left]
      congr 1
      refine hΨ' _ _ fun τ => ?_
      rw [hyk', hyk']
      show blk (r (k1 * k) τ) * y.1 τ = kt0 τ * (blk (r k τ) * y.1 τ)
      rw [hr.mul, blk_mul, hk1, eq_blk (hkt0 τ), mul_assoc]
    have p2 : ∀ k, Jk (k1⁻¹ * k) z = Jk k z' := by
      intro k
      rw [hJk', hJk']
      show J (zU (r' (k1⁻¹ * k)) z) = J (zU (r' k) z')
      congr 1
      refine Subtype.ext (funext fun τ => ?_)
      show (r (k1⁻¹ * k) τ)ᴴ * z.1 τ = (r k τ)ᴴ * z'.1 τ
      rw [hr.mul, Matrix.conjTranspose_mul, r_inv_H hr, hzz' τ, ← hk1, mul_assoc]
    simp_rw [p1]
    rw [MeasureTheory.integral_mul_left_eq_self (fun k => Ψ (yk k) * Jk (k1⁻¹ * k) z) k1]
    simp_rw [p2]
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.BranchFamily.mult_one_families ι (n + 1) n rfl G G' lam sg hI T₀ hT₀ hne T hT
  refine ⟨c, fun Ψ hΨ ℓ => ?_⟩
  have := key Ψ hΨ ℓ
  rw [hc Ψ hΨ, map_smul, smul_eq_mul] at this
  refine Eq.trans ?_ this.symm
  congr 1
  funext k
  ring

end GlobalTheory.KJAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem smul_mem_latMul (S : HSp D) (𝔞 : Set D.host.E) (L : Lat S) (P : Pl D → Prop) (w : AE D)
    (hw : finPart D w ∈ intAE D) : ∀ y ∈ latMul S 𝔞 L P, w • y ∈ latMul S 𝔞 L P := by
  let Ψ : (Fin S.rank → AE D) →+ (Fin S.rank → AE D) := AddMonoidHom.mk' (fun u => w • u) fun x y => smul_add w x y
  have main : latMul S 𝔞 L P ≤ (latMul S 𝔞 L P).comap Ψ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, x, hx, rfl⟩
    let Φ : Af D.host.F ⊗[D.host.F] D.host.E →+ (Fin S.rank → AE D) := AddMonoidHom.mk'
      (fun y => fun i => GlobalTheory.LatticeStable.liftMul D (α ⊗ₜ[D.host.F] (a * x i)) y)
      fun y y' => funext fun i => (GlobalTheory.LatticeStable.liftMul D _).map_add y y'
    have hle : intAE D ≤ (latMul S 𝔞 L P).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨β, hβ, o, rfl⟩
      refine AddSubgroup.subset_closure ⟨β * α, fun v => ?_, fun v hv => ?_, a, ha, o • x, L.smul_mem o hx, ?_⟩
      · rw [map_mul]; exact mul_mem (hβ v) (hα v)
      · rw [map_mul, hP v hv, mul_zero]
      · funext i
        change GlobalTheory.LatticeStable.liftFin D ((β ⊗ₜ[D.host.F] (o : D.host.E)) * (α ⊗ₜ[D.host.F] _)) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.LatticeStable.liftFin_tmul, Pi.smul_apply, Algebra.smul_def,
          show algebraMap _ _ o = (o : D.host.E) from rfl]
        congr 1
        ring
    have e : Ψ (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) = Φ (finPart D w) :=
      funext fun i => GlobalTheory.LatticeStable.mul_pair_tmul D w α _
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, e]
    exact hle hw
  exact fun u hu => main hu

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finPart_e_int (q : SplitPt D k) : finPart D q.e ∈ intAE D := by
  have h := (q.int_iff 1).1 (one_mem _)
  have h1 : q.sec 1 = q.e := by
    have := q.sec_pr 1
    rwa [map_one, mul_one] at this
  rwa [h1] at h

theorem e_mul_mem_latV (q : SplitPt D k) (S : HSp D) (L : Lat S) {s : Fin S.rank → D.host.E} (hs : s ∈ L) :
    (fun j => q.e * incA D (s j)) ∈ latV S L (· = q.v) := by
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hg : (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    AddSubgroup.subset_closure ⟨α, hα, fun u hu => h0 u hu, 1, rfl, s, hs, rfl⟩
  have he : q.e • (fun j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * s j)) ∈ latV S L (· = q.v) :=
    smul_mem_latMul S {1} L (· = q.v) q.e (finPart_e_int q) _ hg
  convert he using 1
  funext j
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]
  rw [Pi.smul_apply, smul_eq_mul, one_mul]
  have : pairA D.host.F 0 α ⊗ₜ[D.host.F] s j = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D (s j) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] s j)
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [this, ← mul_assoc, hee]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
variable {D : D7}
open GlobalTheory.FinPl

theorem rankOne_mem_latO (S T : HSp D) (LS : Lat S) (LT : Lat T) (P : Pl D → Prop) {s : Fin S.rank → D.host.E}
    (hs : s ∈ LS) {y : Fin T.rank → AE D} (hy : y ∈ latA T LT P) :
    (Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P := by
  let Φ : (Fin T.rank → AE D) →+ WO S T := AddMonoidHom.mk'
    (fun y => Matrix.of fun i j => y i * incA D (∑ l, star (s l) * S.gram l j))
    fun y y' => Matrix.ext fun i j => add_mul (y i) (y' i) _
  have main : latA T LT P ≤ (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) P).comap Φ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, hP, a, ha, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩
    ext i j
    change (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rfl
  exact main hy

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul (q : SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

end GlobalTheory.UpMem

namespace GlobalTheory.UpMem
open GlobalTheory.FinPl

theorem up_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT x hx
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S LS hS
  set u := (ofSplit q).up FS FT x with hu_def
  let z : Fin n → Y' → k := fun c => FS.γ *ᵥ (fun m => q.pr (incA D (s c m)))
  let y : Fin n → Fin T.rank → AE D := fun c i => ∑ m, u i m * incA D (s c m)
  have hz : ∀ c r, z c r ∈ 𝒪[k] := by
    intro c
    refine (hFS (z c)).2 ?_
    have : (fun i => q.sec ((FS.β *ᵥ z c) i)) = fun j => q.e * incA D (s c j) := by
      funext j
      simp only [z, Matrix.mulVec_mulVec, FS.βγ, Matrix.one_mulVec]
      exact q.sec_pr _
    rw [this]
    exact e_mul_mem_latV q S LS (hs c).1
  have hy : ∀ c, y c ∈ latA T LT (· = q.v) := by
    intro c
    rw [hU.2 T LT]
    have hint : ∀ r, (x *ᵥ z c) r ∈ 𝒪[k] := fun r =>
      Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hx r m) (hz c m)
    convert (hFT (x *ᵥ z c)).1 hint using 1
    funext i
    change ∑ m, q.sec ((FT.β * x * FS.γ) i m) * incA D (s c m) = _
    simp_rw [sec_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    simp only [z, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc]
    rfl
  have hdec : u = ∑ c, (Matrix.of fun i j => y c i * incA D (∑ l, star (s' c l) * S.gram l j) : WO S T) := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, y, Finset.sum_mul]
    rw [Finset.sum_comm]
    have key : ∀ m, ∑ c, u i m * incA D (s c m) * incA D (∑ l, star (s' c l) * S.gram l j) =
        u i m * incA D (if m = j then 1 else 0) := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hss m j, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_mul, mul_assoc]
    rw [Finset.sum_congr rfl fun m _ => key m]
    simp [apply_ite]
  rw [hdec]
  exact sum_mem fun c _ => rankOne_mem_latO S T LS LT _ (hs c).2 (hy c)

end GlobalTheory.UpMem
end
end

