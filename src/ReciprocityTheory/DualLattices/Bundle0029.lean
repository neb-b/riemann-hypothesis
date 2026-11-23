module

public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0027
public import ReciprocityTheory.DualLattices.Bundle0021
public import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct
public import ReciprocityTheory.DualLattices.IsPairingValueAddRight
public import ReciprocityTheory.DualLattices.HeightFunctionalStatementOfPairingProperties
public import ReciprocityTheory.DualLattices.Bundle0022
public import ReciprocityTheory.DualLattices.Bundle0024
public import ReciprocityTheory.DualLattices.Bundle0026

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.EvActStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvActStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ a : Oe, ∀ f ∈ D.evImg C, ∃ f' ∈ D.evImg C,
    ∀ t : TT p g, f' (red p g t) = f (red p g (D.H.ρ a *ᵥ t))

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvBtStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvBtStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ k : Fin g, ∃ f ∈ D.evImg C, ∀ t : TT p g,
    ∃ r : (Tw.O : Type), algebraMap (Tw.O : Type) C
      ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) - f (red p g t) =
        algebraMap (Tw.O : Type) C (p * r)

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvCotStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvCotStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    ∃ φ : augIdeal (D.evImg C) →ₗ[(Tw.O : Type)] LieDualModP p (Tw.O : Type) g,
      Function.Surjective φ ∧
      LinearMap.ker φ = (sqIdeal (augIdeal (D.evImg C))).comap (augIdeal (D.evImg C)).subtype ∧
      ∀ (a : Oe) (f f' : augIdeal (D.evImg C)) (l : Fin g → (Tw.O : Type)),
        (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (D.H.ρ a *ᵥ t))) →
        φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvHopfStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvHopfStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    (∀ f ∈ D.evImg C, addPull (Tw.O : Type) (Nb p g) f ∈ tensorSpan (Tw.O : Type) (D.evImg C)) ∧
      ∀ f ∈ D.evImg C, (fun x => f (-x)) ∈ D.evImg C

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvHtStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvHtStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ k : Fin g, ∃ f ∈ D.evImg C, ∀ t : TT p g,
    ∃ r : (Tw.O : Type), algebraMap (Tw.O : Type) C
      ((D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) - f (red p g t) =
        algebraMap (Tw.O : Type) C (p * r)

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvLatStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvLatStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) →
    IsLat (Tw.O : Type) (D.evImg C) ∧ D.evImg C ≤ intFun (Tw.O : Type) (Nb p g) ∧
      (1 : Nb p g → C) ∈ D.evImg C ∧ ∀ f f', f ∈ D.evImg C → f' ∈ D.evImg C → f * f' ∈ D.evImg C

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.EvenTwoEvaluationSign
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvenTwoEvaluationSign (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) → p = 2 → ∀ s : TT p g, ∃ f ∈ D.evImg C,
    ∀ t : TT p g, f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g D.H.E s t)).val

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsLimTensor
section
noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀) {p : ℕ}

lemma tw_πr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.π n).comp (Tw.r' n) = (Tw.r n).comp (Tw.π (n + 1)) := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact (Tw.r_π n x).symm

lemma tw_qr (Tw : ATowerL R₀ p) (n : ℕ) : (Tw.r n).comp (Tw.q (n + 1)) = Tw.q n := by
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  exact Tw.r_q n x

lemma lift_down (Tw : ATowerL R₀ p) (n : ℕ) (τ1 : B.G Tw.O) (th1 : B.G (Tw.R' (n + 1)))
    (w1 : B.gg ⊗[R₀] (Tw.R' (n + 1) : Type u)) (h1 : B.map (Tw.π (n + 1)) th1 = B.map (Tw.q (n + 1)) τ1)
    (h2 : (p ^ (n + 1 + 1)) • th1 = B.tg (Tw.π (n + 1)) (Tw.sqZero (n + 1))
      (TensorProduct.map LinearMap.id (ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1))) w1)) :
    B.map (Tw.π n) (p • B.map (Tw.r' n) th1) = B.map (Tw.q n) (p • τ1) ∧
    (p ^ (n + 1)) • (p • B.map (Tw.r' n) th1) = B.tg (Tw.π n) (Tw.sqZero n)
      (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n))
        (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1)) ∧
    LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap (LinearMap.lTensor B.gg (Tw.r' n).1.toLinearMap w1) =
      LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap
        (LinearMap.lTensor B.gg (Tw.π (n + 1)).1.toLinearMap w1) := by
  have e1 : B.map (Tw.π n) (B.map (Tw.r' n) th1) = B.map (Tw.q n) τ1 := by
    rw [← B.map_comp, tw_πr Tw n, B.map_comp, h1, ← B.map_comp, tw_qr Tw n]
  have hf : ∀ a ∈ (Tw.π (n + 1)).ker, (Tw.r' n).1.toLinearMap a ∈ (Tw.π n).ker := by
    intro a ha
    simp only [Submodule.restrictScalars_mem, RingHom.mem_ker] at ha ⊢
    rw [AlgHom.toLinearMap_apply, ← Tw.r_π n a, ha, map_zero]
  have hcomm : ((Tw.r' n).1.toLinearMap.restrict hf) ∘ₗ
      ξmul (Tw.π (n + 1)) (Tw.ξ (n + 1)) (Tw.ξ_mem (n + 1)) =
      ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n) ∘ₗ (Tw.r' n).1.toLinearMap := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    show (Tw.r' n).1 (Tw.ξ (n + 1) * a) = Tw.ξ n * (Tw.r' n).1 a
    rw [map_mul, Tw.r'_ξ n]
  have h3 : (Tw.π n).1.toLinearMap ∘ₗ (Tw.r' n).1.toLinearMap =
      (Tw.r n).1.toLinearMap ∘ₗ (Tw.π (n + 1)).1.toLinearMap :=
    LinearMap.ext fun a => (Tw.r_π n a).symm
  refine ⟨by rw [map_nsmul, map_nsmul, e1], ?_, ?_⟩
  · rw [smul_smul, ← pow_succ, ← map_nsmul, h2,
      ← B.tg_nat (Tw.π (n + 1)) (Tw.π n) (Tw.sqZero (n + 1)) (Tw.sqZero n) (Tw.r' n) hf]
    have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) hcomm
    simp only [LinearMap.lTensor_comp, LinearMap.comp_apply] at h
    exact congrArg (B.tg (Tw.π n) (Tw.sqZero n)) h
  · have h := congrArg (fun f => LinearMap.lTensor B.gg f w1) h3
    simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply] using h

def coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (k : Module.Free.ChooseBasisIndex R₀ B.gg) :
    B.gg ⊗[R₀] M →ₗ[R₀] M :=
  (TensorProduct.lid R₀ M).toLinearMap ∘ₗ LinearMap.rTensor M ((Module.Free.chooseBasis R₀ B.gg).coord k)

lemma coordK_lTensor {M M' : Type u} [AddCommGroup M] [Module R₀ M] [AddCommGroup M'] [Module R₀ M']
    (f : M →ₗ[R₀] M') (k : Module.Free.ChooseBasisIndex R₀ B.gg) (x : B.gg ⊗[R₀] M) :
    B.coordK M' k (LinearMap.lTensor B.gg f x) = f (B.coordK M k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m => simp [coordK]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

lemma sum_coordK (M : Type u) [AddCommGroup M] [Module R₀ M] (x : B.gg ⊗[R₀] M) :
    ∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] B.coordK M k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul g m =>
    simp only [coordK, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, Module.Basis.coord_apply]
    simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add x y hx hy =>
    simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

lemma exists_lim_tensor (Tw : ATowerL R₀ p) (wb : ∀ n, B.gg ⊗[R₀] (Tw.R n : Type u))
    (hwb : ∀ n, LinearMap.lTensor B.gg (Tw.r n).1.toLinearMap (wb (n + 1)) = wb n) :
    ∃ bt : B.gg ⊗[R₀] (Tw.O : Type u), ∀ n, LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap bt = wb n := by
  choose a ha using fun k => Tw.complete (fun n => B.coordK (Tw.R n) k (wb n)) (fun n => by
    rw [← hwb n, B.coordK_lTensor]
    rfl)
  refine ⟨∑ k, (Module.Free.chooseBasis R₀ B.gg k) ⊗ₜ[R₀] a k, fun n => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [LinearMap.lTensor_tmul]
  conv_rhs => rw [← B.sum_coordK _ (wb n)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← ha k n]
  rfl

end BX

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.ExistsReductionOfCoordinateCombination
section
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Lift

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y

lemma red_mulVec (H : HodgeTateDatum p g v R O σ cp) (a : O) (t : TT p g) :
    red p g (H.ρ a *ᵥ t) = nbAct H a (red p g t) := by
  funext i
  exact RingHom.map_mulVec PadicInt.toZMod (H.ρ a) t i

lemma red_surj (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma comp_mem (H : HodgeTateDatum p g v R O σ cp) (a : O) {f : Nb p g → C} (hf : f ∈ H.AA.carrier) :
    (fun y => f (nbAct H a y)) ∈ H.AA.carrier := by
  obtain ⟨f', hf', hf'e⟩ := H.h3 a f hf
  have hfun : (fun y => f (nbAct H a y)) = f' := by
    funext y
    obtain ⟨t, rfl⟩ := red_surj y
    rw [hf'e, red_mulVec]
  rw [hfun]
  exact hf'

variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)

private lemma smul_cancel_lemma {S K : Type*} [CommRing S] [Field K] [Algebra S K]
    (hinj : Function.Injective (algebraMap S K)) {ι κ : Type*} {M : Matrix ι κ S} (hM : M ≠ 0)
    {a b : S} (h : a • M = b • M) : a = b := by
  obtain ⟨x, y, hxy⟩ : ∃ x y, M x y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hM (Matrix.ext fun x y => by simpa using hc x y)
  have h2 : a * M x y = b * M x y := by
    have := congrFun (congrFun h x) y
    simpa only [Matrix.smul_apply, smul_eq_mul] using this
  have h3 : algebraMap S K (a - b) * algebraMap S K (M x y) = 0 := by
    rw [← map_mul, sub_mul, h2, sub_self, map_zero]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp (hinj (by rw [h4, map_zero]))
  · exact absurd (hinj (by rw [h4, map_zero])) hxy

end Lift

end ReciprocityTheory.PGsh.Up
end
end

-- bundled from ReciprocityTheory.DualLattices.PSerFrobStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def nsmulF {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a : Fin g → S) : ℕ → Fin g → S
  | 0 => 0
  | n + 1 => fAdd F (nsmulF F a n) a

def PSerFrobStatement (p : ℕ) [Fact p.Prime] (K : LAlg R₀) (ch : FormalChartAtZero B K g) : Prop :=
  ∀ N : ℕ, ∃ G : Fin g → MvPolynomial (Fin g) R₀,
    (∀ k m, (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff (G k) m = p * r) ∧
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
      nsmulF ch.F a p = fun k => MvPolynomial.aeval a (G k)

end ReciprocityTheory.PGsh.Be2
end
end

-- bundled from ReciprocityTheory.DualLattices.ThmAAll
section
namespace ReciprocityTheory.PGsh

theorem bx_heightFunctional {R₀ : Type*} [CommRing R₀] (B : BX R₀) : HighestWeightVectorUniformBounds B := heightFunctionalStatement_of_pairingProperties B (pairingProperties B)

theorem bx_tangentPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) : TangentPairingStatement B := B.tangentPairingStatement_of_heightFunctional (bx_heightFunctional B)

theorem bx_towerPairing {R₀ : Type*} [CommRing R₀] (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : NsetExpInjectiveSurjective B Tw :=
  b4 B (pairingProperties B) (bx_tangentPairing B) Tw

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.WFrobStatement
section
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def WFrobStatement {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : Prop :=
  ∀ G : MvPolynomial (Fin g) (wd.W : Type),
    (∀ m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff G m ∈ Ideal.span {(p : (wd.W : Type))}) →
    ∃ Q : MvPolynomial (Fin g) (Tw.R 0 : Type), ∀ y : Fin g → (wd.W : Type),
      MvPolynomial.eval y G ∈ Ideal.span {(p : (wd.W : Type))} →
      ∀ a : (wd.W : Type), wd.πW.1 a = MvPolynomial.eval (fun i => wd.πW.1 (y i)) Q →
        MvPolynomial.eval y G = p * a

end ReciprocityTheory.PGsh.Be2
end
end

