module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedLatticeSubspace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1364
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tate_free_of_card :
    ∀ (p : ℕ) [Fact p.Prime] (M : Type) [CommGroup M] (r : ℕ), (∀ n : ℕ, Nat.card {x : M // x ^ p ^ n = 1} = p ^ (r * n)) → Nonempty (Tate p M ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) ∧ (∀ (n : ℕ) (x : M), x ^ p ^ n = 1 → ∃ t : Tate p M, t.lev n = x) ∧ ∀ (n : ℕ) (t : Tate p M), t.lev n = 1 ↔ ∃ s : Tate p M, t = (p : ℤ_[p]) ^ n • s := by
  intro p _ M _ r h
  obtain ⟨T, _, _, π, hfree, hfin, hrk, hs, h0, hsm, hon, hker, huniq⟩ :=
    GlobalTheory.exists_tateModule_of_card (Additive M) p r (fun n => by
      rw [← h n]
      exact Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun x => Iff.rfl))
  have hkill : ∀ n x, p ^ n • π n x = 0 := fun n x => by
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [pow_succ, mul_smul, hs, ih]
  let f : T →ₗ[ℤ_[p]] Tate p M :=
    { toFun := fun x => Tate.mk (fun n => Additive.toMul (π n x)) fun n =>
        ⟨congrArg Additive.toMul (hkill n x), congrArg Additive.toMul (hs n x)⟩
      map_add' := fun x y => Tate.ext fun n => congrArg Additive.toMul (map_add (π n) x y)
      map_smul' := fun a x => Tate.ext fun n => congrArg Additive.toMul (hsm n a x) }
  have hf : ∀ x n, (f x).lev n = Additive.toMul (π n x) := fun _ _ => rfl
  have hu : ∀ t : Tate p M, ∃! x, ∀ n, π n x = Additive.ofMul (t.lev n) := fun t =>
    huniq (fun n => Additive.ofMul (t.lev n))
      (by have := t.lev_pow 0
          rw [pow_zero, pow_one] at this
          rw [this]; rfl)
      (fun n => congrArg Additive.ofMul (t.lev_succ n))
  have hsurj : Function.Surjective f := fun t => by
    obtain ⟨x, hx, -⟩ := hu t
    exact ⟨x, Tate.ext fun n => by rw [hf, hx]; rfl⟩
  have hinj : Function.Injective f := fun x y hxy =>
    (hu (f y)).unique (fun n => by rw [← hxy]; rfl) (fun n => rfl)
  refine ⟨⟨(LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans
    (LinearEquiv.ofFinrankEq _ _ (by simpa using hrk))⟩, fun n x hx => ?_, fun n t => ?_⟩
  · obtain ⟨y, hy⟩ := hon n (Additive.ofMul x) (congrArg Additive.ofMul hx)
    exact ⟨f y, by rw [hf, hy]; rfl⟩
  · obtain ⟨x, rfl⟩ := hsurj t
    have key : ∀ y : T, f (p ^ n • y) = (p : ℤ_[p]) ^ n • f y := fun y => by
      rw [map_nsmul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    refine Iff.trans (hker n x) ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨f y, key y⟩
    · rintro ⟨s, hs'⟩
      obtain ⟨y, rfl⟩ := hsurj s
      exact ⟨y, hinj (hs'.trans (key y).symm)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagSiegel

open MeasureTheory Formalism.IndefR.Datum

def diagInt {F : Type} [Field F] [NumberField F] {κ : Type} (μ : @Measure (κ → AF F) (borel _))
    (Φ : (κ ⊕ κ → AF F) → ℂ) : ℂ :=
  @integral (κ → AF F) ℂ _ _ (borel _) μ (fun u => Φ (Sum.elim u u))

def diagMat {m n : ℕ} {X : Type} (w : Matrix (Fin m) (Fin n) X) : Matrix (Fin m) (Fin (n + n)) X :=
  (Matrix.fromCols w w).submatrix id finSumFinEquiv.symm

def thetaDiagInt {D : D7} {m n : ℕ} (ν : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)) (f : Mx D m (n + n) → ℂ) : ℂ :=
  ∫ w in 𝓕, f (diagMat w) ∂ν

def ruleFac {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (_c : E →ₐ[R] E) (C : GlobalTheory.WeilM.TestClass R)
    (χ : Eˣ →* Circle) (a : ℕ) {ν : Type} [Fintype ν] [DecidableEq ν] (t : GL ν E) : ℂ :=
  (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    (((C.modu (Units.map (Algebra.norm R : E →* R) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((a : ℝ) / 2) : ℝ) : ℂ)

end GlobalTheory.DiagSiegel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaQuasiRat

theorem schr_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (GlobalTheory.WeilM.schr ψ w' φ) =
      ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • GlobalTheory.WeilM.schr ψ (w + w') φ := by
  funext x
  simp only [GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add, add_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add]
  congr 2
  have h : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * h

theorem thetaSum_smul' (F : Type) [Field F] [NumberField F] {κ : Type} (c : ℂ) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (c • φ) = c * GlobalTheory.WeilM.thetaSum F φ := by
  simp only [GlobalTheory.WeilM.thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem thetaSum_schr_rat (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1)
    {κ : Type} [Fintype κ] (y z : κ → F) (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i), fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) φ) =
      GlobalTheory.WeilM.thetaSum F φ := by
  have h2 : ⅟(2 : AdeleRing (𝓞 F) F) = algebraMap F (AdeleRing (𝓞 F) F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AdeleRing (𝓞 F) F)) 2, ← map_mul]
    norm_num
  have key : ∀ ξ : κ → F, ψ ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ
      (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) + ⅟(2 : AdeleRing (𝓞 F) F) *
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)))) = 1 := by
    intro ξ
    have e : (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) ⬝ᵥ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i)) +
        ⅟(2 : AdeleRing (𝓞 F) F) * ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (y i)) ⬝ᵥ
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (z i))) =
        algebraMap F (AdeleRing (𝓞 F) F) (ξ ⬝ᵥ z + 1 / 2 * (y ⬝ᵥ z)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, map_add (f := _), map_mul, map_sum, h2]
    rw [e]
    exact hψ _
  unfold GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
  simp only [key, one_mul]
  rw [← (Equiv.addRight y).tsum_eq (fun ξ : κ → F => φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))]
  congr 1
  funext ξ
  congr 1
  funext i
  exact (map_add (algebraMap F (AdeleRing (𝓞 F) F)) (ξ i) (y i)).symm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem cA_apply (D : D7) (a : AF D.host.F ⊗[D.host.F] D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig a = cA D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem symp_eq_symplO (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (hA : JA = T.gramᵀ)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (x y : Formalism.IndefR.Datum.WO S T) :
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB) x y =
      Formalism.IndefR.Datum.symplO S T x y := by
  unfold GlobalTheory.WeilM.symp Formalism.IndefR.Datum.symplO
  congr 1
  have hb : ∀ j l, ξ * incM D.host.F JB j l = incA D D.host.xi0 * incA D (S.gram⁻¹ j l) := fun j l => by
    have := congrFun (congrFun hB j) l
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [this]
    simp [incM, Matrix.map_apply, Matrix.smul_apply, map_mul]
  have e : ∀ i j k l, ξ * (x i j * incM D.host.F JA i k * incM D.host.F JB j l * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (y k l)) =
      incA D D.host.xi0 * (incA D (S.gram⁻¹ j l) * cA D (y k l) * incA D (T.gram k i) * x i j) := fun i j k l => by
    have h1 : incM D.host.F JA i k = incA D (T.gram k i) := by
      subst hA; rfl
    rw [cA_apply, h1]
    linear_combination (x i j * incA D (T.gram k i) * cA D (y k l)) * hb j l
  unfold GlobalTheory.WeilM.hTens Formalism.IndefR.Datum.hO
  simp only [Finset.mul_sum, e]
  symm
  calc _ = ∑ a, ∑ b, ∑ d, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, incA D D.host.xi0 *
        (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm

end GlobalTheory.ThetaQuasiRat

namespace GlobalTheory.ThetaQuasiRat

theorem thetaTr_ratW_add : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : Formalism.IndefR.Datum.WO S T),
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ (ratW T S γ + w) = ψ (-(Formalism.IndefR.Datum.symplOH S T (ratW T S γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ w := by
  intro D ψ hψ S T JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratW T S γ = incM D.host.F γ := rfl
  have hform := co.form (incM D.host.F γ) w
  rw [symp_eq_symplO D S T JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF D.host.F) × (κ → AF D.host.F) :=
    (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i)) with hu
  set v := co.e w
  have law := schr_schr ψ u v Φ
  have hinv : ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      ψ (⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr ψ (u + v) Φ =
      ψ (-(⅟(2 : AF D.host.F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr ψ u (GlobalTheory.WeilM.schr ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF D.host.F) = algebraMap D.host.F (AF D.host.F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [hsum, thetaSum_smul', hu, thetaSum_schr_rat D.host.F ψ hψ.1.2.2.1 y z, ← hu,
    Formalism.IndefR.Datum.symplOH, hform, h2]

end GlobalTheory.ThetaQuasiRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDegreeDensityPullbackEqNormSqDetMul
section
set_option autoImplicit false

noncomputable section

open Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

open Module

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

theorem exterior_repr_univ_of_mem {N k : ℕ} (b : Basis (Fin N) K M) (hk : k ≠ N) {x : ExteriorAlgebra K M}
    (hx : x ∈ ⋀[K]^k M) : b.ExteriorAlgebra.repr x Finset.univ = 0 := by
  rw [Basis.ExteriorAlgebra, Basis.repr_reindex_apply]
  have h1 : (Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N))).1 = N := by
    simp [Set.powersetCard.prodEquiv]
  rcases e : Set.powersetCard.prodEquiv.symm (Finset.univ : Finset (Fin N)) with ⟨j, a⟩
  rw [e] at h1
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ (fun h => hk (h.trans h1)) hx

theorem exterior_repr_univ_map {N : ℕ} (b : Basis (Fin N) K M) (f : M →ₗ[K] M) (x : ExteriorAlgebra K M) :
    b.ExteriorAlgebra.repr (ExteriorAlgebra.map f x) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr x Finset.univ := by
  have key : ∀ s, b.ExteriorAlgebra.repr (ExteriorAlgebra.map f (b.ExteriorAlgebra s)) Finset.univ =
      LinearMap.det f * b.ExteriorAlgebra.repr (b.ExteriorAlgebra s) Finset.univ := by
    intro s
    by_cases hs : s = Finset.univ
    · subst hs
      set g : M [⋀^Fin N]→ₗ[K] K :=
        (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap).compAlternatingMap
          (ExteriorAlgebra.ιMulti K N) with hg
      have hb : ∀ w : Fin N → M, g w = b.ExteriorAlgebra.repr (ExteriorAlgebra.ιMulti K N w) Finset.univ := fun _ => rfl
      have he := AlternatingMap.eq_smul_basis_det b g
      rw [ExteriorAlgebra.basis_apply_ofCard _ (by simp : (Finset.univ : Finset (Fin N)).card = N)]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti, ← hb, ← hb, he,
        AlternatingMap.smul_apply, AlternatingMap.smul_apply, Basis.det_comp, smul_eq_mul, smul_eq_mul]
      ring
    · have hc : s.card ≠ N := fun h => hs (Finset.eq_univ_of_card s (by simpa using h))
      rw [Basis.repr_self, Finsupp.single_apply, if_neg hs, mul_zero,
        ExteriorAlgebra.basis_apply]
      dsimp only [ExteriorAlgebra.ιMulti_family]
      rw [ExteriorAlgebra.map_apply_ιMulti]
      exact exterior_repr_univ_of_mem b hc (ExteriorAlgebra.ιMulti_range K _ ⟨_, rfl⟩)
  have := b.ExteriorAlgebra.ext
    (f₁ := Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap ∘ₗ (ExteriorAlgebra.map f).toLinearMap)
    (f₂ := LinearMap.det f • (Finsupp.lapply Finset.univ ∘ₗ b.ExteriorAlgebra.repr.toLinearMap))
    (fun s => by simpa using key s)
  simpa using LinearMap.congr_fun this x

theorem det_pull_gen {n : ℕ} (L : V n →L[ℂ] V n) :
    LinearMap.det (Matrix.toLin' (fromBlocks (of fun b a => L (coordVec b) a) 0 0
      (of fun b a => conj (L (coordVec b) a)))) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) := by
  rw [LinearMap.det_toLin', det_fromBlocks_zero₂₁]
  have hP : (of fun b a => L (coordVec b) a).det = L.det := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis,
      ← det_transpose]
    congr 1
  have hQ : (of fun b a => conj (L (coordVec b) a)) = (starRingEnd ℂ).mapMatrix (of fun b a => L (coordVec b) a) := by
    ext i j; simp
  rw [hQ, ← RingHom.map_det, hP, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dens_pull {n : ℕ} (L : V n →L[ℂ] V n) (ω : Alt n) :
    dens (pull L ω) = ((‖L.det‖ ^ 2 : ℝ) : ℂ) * dens ω := by
  simp only [dens, pull, bas]
  rw [exterior_repr_univ_map, det_pull_gen, mul_div_assoc]

end GlobalTheory.CxForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
section
open GlobalTheory.CxForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DensPow

variable {n : ℕ}

theorem ι_mul_ι_mul_ι_mul_ι_left (u w w' : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w') = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u)
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u) * ExteriorAlgebra.ι ℂ w' := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w') := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

theorem ι_mul_ι_mul_ι_mul_ι_right (u u' w : Fin n ⊕ Fin n → ℂ) :
    ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ w * (ExteriorAlgebra.ι ℂ u' * ExteriorAlgebra.ι ℂ w) = (0 : Alt n) := by
  have h := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) w u')
  calc _ = ExteriorAlgebra.ι ℂ u * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ u') * ExteriorAlgebra.ι ℂ w := by
          simp only [mul_assoc]
    _ = -(ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ u' * (ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ι ℂ w)) := by
          rw [h]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = 0 := by rw [ExteriorAlgebra.ι_sq_zero]; simp

def row (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n where
  toFun w := ∑ b, w b • sym (a, b)
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c w := by simp [Finset.smul_sum, smul_smul]

theorem coe_row (a : Fin n) (w : Fin n → ℂ) :
    (row a w : Alt n) = dz a * ExteriorAlgebra.ι ℂ (∑ b, w b • Pi.single (Sum.inr b) (1 : ℂ)) := by
  simp [row, sym, dzb, Finset.mul_sum, mul_smul_comm]

theorem row_mul_row (a : Fin n) (w : Fin n → ℂ) : row a w * row a w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, dz]
  exact ι_mul_ι_mul_ι_mul_ι_left _ _ _

theorem row_mul_row_of_ne {a a' : Fin n} (w : Fin n → ℂ) : row a w * row a' w = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_row, coe_row, dz, dz]
  exact ι_mul_ι_mul_ι_mul_ι_right _ _ _

def altRows (n : ℕ) : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] Ev n where
  toMultilinearMap := (MultilinearMap.mkPiAlgebra ℂ (Fin n) (Ev n)).compLinearMap row
  map_eq_zero_of_eq' v i j hij hne := by
    change ∏ a, row a (v a) = 0
    rw [← Finset.mul_prod_erase Finset.univ (fun a => row a (v a)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => row a (v a))
        (Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ j⟩), ← mul_assoc, hij, row_mul_row_of_ne, zero_mul]

theorem altRows_apply (v : Fin n → Fin n → ℂ) : altRows n v = ∏ a, row a (v a) := by
  first
  | rfl
  | simp only [altRows, AlternatingMap.coe_mk, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

theorem alt_eq_det_smul {K M N : Type} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {m : ℕ} (e : Module.Basis (Fin m) K M)
    (f : M [⋀^Fin m]→ₗ[K] N) (h : Fin m → M) : f h = e.det h • f e := by
  have key : f = (LinearMap.toSpanSingleton K N (f e)).compAlternatingMap e.det := by
    refine e.ext_alternating (fun v hv => ?_)
    have hb : Function.Bijective v := Finite.injective_iff_bijective.1 hv
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective v hb
    have hσ : (fun i => e (v i)) = (⇑e) ∘ ⇑σ := rfl
    rw [hσ, LinearMap.compAlternatingMap_apply, LinearMap.toSpanSingleton_apply,
      AlternatingMap.map_perm, AlternatingMap.map_perm, e.det_self, Units.smul_def,
      Units.smul_def, smul_one_smul]
  rw [DFunLike.congr_fun key h]
  rfl

theorem prod_row (H : Matrix (Fin n) (Fin n) ℂ) : ∏ a, row a (H a) = H.det • ∏ a, sym (a, a) := by
  have h1 : ∏ a, row a (H a) = altRows n (fun a b => H a b) := (altRows_apply _).symm
  rw [h1, alt_eq_det_smul (Pi.basisFun ℂ (Fin n)), Pi.basisFun_det, altRows_apply]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  simp [row, Pi.single_apply]

theorem add_pow_of_mul_self {R : Type*} [CommRing R] {x : R} (hx : x * x = 0) (y : R) (m : ℕ) :
    (x + y) ^ (m + 1) = y ^ (m + 1) + ((m : R) + 1) * x * y ^ m := by
  induction m with
  | zero => simp [add_comm]
  | succ m ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((m : R) + 1) * y ^ m * hx

theorem sum_pow_card {R ι : Type*} [CommRing R] [DecidableEq ι] (f : ι → R) (hf : ∀ a, f a * f a = 0) (s : Finset ι) :
    (∀ m, (∑ a ∈ s, f a) ^ (s.card + 1 + m) = 0) ∧ (∑ a ∈ s, f a) ^ s.card = (s.card.factorial : R) * ∏ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun m => by simp, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨fun m => ?_, ?_⟩
    · rw [show s.card + 1 + 1 + m = (s.card + 1 + m) + 1 by omega, add_pow_of_mul_self (hf a),
        show s.card + 1 + m + 1 = s.card + 1 + (m + 1) by omega, ih.1, ih.1]
      simp
    · rw [add_pow_of_mul_self (hf a), show s.card + 1 = s.card + 1 + 0 by rfl, ih.1, ih.2, Nat.factorial_succ]
      push_cast
      ring

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem vol_eq_smul_prod (n : ℕ) : vol n = (Complex.I / 2) ^ n • ∏ a, sym (a, a) := by
  simp only [vol, Algebra.smul_def, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow]

theorem dens_pow (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CxForm.dens (((∑ a, ∑ b, H a b • GlobalTheory.CxForm.sym (a, b) : GlobalTheory.CxForm.Ev n) ^ n : GlobalTheory.CxForm.Ev n) :
      GlobalTheory.CxForm.Alt n) = (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := by
  have hω : (∑ a, ∑ b, H a b • sym (a, b) : Ev n) = ∑ a, row a (H a) := by simp [row]
  have hp : (∑ a, row a (H a)) ^ n = (n.factorial : Ev n) * ∏ a, row a (H a) := by
    simpa using (sum_pow_card (fun a => row a (H a)) (fun a => row_mul_row a _) Finset.univ).2
  have hP : (n.factorial : Ev n) * ∏ a, row a (H a) = ((n.factorial : ℂ) * H.det) • ∏ a, sym (a, a) := by
    rw [prod_row, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  rw [hω, hp, hP, Subalgebra.coe_smul, dens_smul, div_eq_mul_inv, eq_inv_of_mul_eq_one_right h1]

end GlobalTheory.CxForm.DensPow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFrameAbelianPartTorsionFrameStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_frame_abelian_part_torsion_frame : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U.toUnifPre) (ρ : LB.Gen (A.L.pull (eSec A.A))), NormW U.toUnifPre w₀ ρ → ∀ N : ℕ, 1 ≤ N → ∀ (g o : GtPtF D.toPre F), GtPtF.IsNsmul N g o → o.IsZero → ∀ (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x), w.IsGen → LiesOver U.toUnifPre w₀ g w x fr → IsTorsFrame A ρ N x fr → ∀ κ : LB.Gen (kapLB D.toPre (𝟙 D.toPre.P.A ^ N) (N ^ 2) 1), Normd κ → ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J ^ (N ^ 2) * val κ g.b.left z J = 1 := by
  first | exact @GlobalTheory.Poinc.Tors.FrameTors.frame_tors | exact GlobalTheory.Poinc.Tors.FrameTors.frame_tors | (intros; apply GlobalTheory.Poinc.Tors.FrameTors.frame_tors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralLeviConstantTermStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_integral_levi_constant_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E) (f : GLw n w → ℂ), IsHecke (GlobalTheory.LFun.KGL w (n := n)) f ∨ (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw (n - a) w, (m.1.val.charpoly * m.2.val.charpoly).Separable → twOrb (MonoidHom.id _) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := (n - a)))) m (ct (Nat.add_sub_cancel' ha) w f) = absHalf w (resultant m.1.val.charpoly m.2.val.charpoly ^ 2 / (m.1.val.det ^ (n - a) * m.2.val.det ^ a)) * twOrb (MonoidHom.id _) (GlobalTheory.LFun.KGL w (n := n)) (blk (Nat.add_sub_cancel' ha) w m 0) f := by
  first | exact @GlobalTheory.LeviDesc.orbInt_descent | exact GlobalTheory.LeviDesc.orbInt_descent | (intros; apply GlobalTheory.LeviDesc.orbInt_descent <;> assumption)
end

