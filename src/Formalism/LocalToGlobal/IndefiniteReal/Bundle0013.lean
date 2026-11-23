module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.CxCutEP
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.TransferStatement
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicFormsHyp
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Filter Topology
  IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.AutomorphicFormsHyp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section General

variable {N : ℕ}

def hK (K : Matrix (Fin N) (Fin N) D.host.E) (x y : Mx D N 1) : AE D :=
  ∑ a, ∑ b, cA D (y a 0) * incA D (K a b) * x b 0

end General

def WeilExistsO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilDatumO ψ S T χS χT om

end Formalism.IndefR.AutomorphicFormsHyp

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxCutPO
section
open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.DIV.CyclotomicLifting Formalism.IndefR.Cx.EigenprojectionMatrices

namespace OrthogonalPartDecomposition

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
  {B : BlockDat K G Pl0} {ℓ : Lvl K G} {v0 : InfinitePlace K} {s : ℕ} {Z : Submodule K B.S.Forms}

theorem map_conjTranspose_of_mem_cmMax {n d : ℕ} (σ : K →+* ℂ) (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, E i a ∈ cmMax K) :
    (Eᴴ).map σ = (E.map σ)ᴴ :=
  map_conjTranspose' σ E fun i a => ConjugateWeightGram.isCMSub_cmMax σ _ (hE i a)

theorem HV_map (h : BlockHyp B ℓ v0 s) (σ : K →+* ℂ) :
    (B.HV ℓ).map σ = σ (Nat.card ℓ.P : K)⁻¹ • (((B.vE ℓ).map σ)ᴴ * B.S.H.map σ * (B.vE ℓ).map σ) := by
  have e : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [e, ← map_conjTranspose_of_mem_cmMax σ _ (hv_spec h).1, ← Matrix.map_mul, ← Matrix.map_mul]
  ext a b
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem adjC (h : BlockHyp B ℓ v0 s) (hH : B.OkH) (σ : K →+* ℂ) (i : B.Pl × ℕ) :
    ∃ i', (B.HV ℓ).map σ * (tV B ℓ i).map σ = ((tV B ℓ i').map σ)ᴴ * (B.HV ℓ).map σ := by
  obtain ⟨i', hi'⟩ := opMat_adj hH i
  have hHh : B.S.Hᴴ = B.S.H := FinitelyNonzeroLinear.herm_of_pos h.conj (h.ok.hpos v0)
  have h2 : B.S.H * B.opMat i = (B.opMat i')ᴴ * B.S.H := by
    have := congrArg Matrix.conjTranspose hi'
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hHh] at this
    exact this
  have h2' : B.S.H.map σ * (B.opMat i).map σ = ((B.opMat i').map σ)ᴴ * B.S.H.map σ := by
    rw [← Matrix.map_mul, h2, Matrix.map_mul, map_conjTranspose_of_mem_cmMax σ _ (hH.rat i')]
  have hT : ∀ k, (B.vE ℓ).map σ * (tV B ℓ k).map σ = (B.opMat k).map σ * (B.vE ℓ).map σ := by
    intro k
    rw [← Matrix.map_mul, ← Matrix.map_mul, vE_tV h]
  refine ⟨i', ?_⟩
  rw [HV_map h σ]
  exact adj_transfer _ _ _ _ _ _ _ (hT i) (hT i') h2'

end OrthogonalPartDecomposition

section Main

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)
variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Main

end Formalism.IndefR.Cx
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CxPass
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def prin {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) : CxData A := { X with nP := fun _ => 1 }

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

section Prims

variable (A : FamIn K G Pl0 T m) (X : CxData A.fam.amb)

def GUnit (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def GEquiv (gE : Representation ℂ G X.EE) : Prop :=
  ∀ t (g : G) (x : A.fam.amb.FR t), X.Θ t (X.jR t (A.fam.amb.opR t (Sum.inr g) x)) = gE g (X.Θ t (X.jR t x))

variable {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
    {Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs)}
    {Zsc : DefSub A.fam.amb → IndefScale A.fam.base}

def PrincipalInjectiveCommonRange : Prop :=
  Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0) ∧
    ∀ t, Function.Injective (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) ∧
      LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) =
        LinearMap.range (X.iC (crdOf A ⊥ 1 P1 ψ1 Dc Sp Zsc) false A.fam.base.μ0)

end Prims

section Group

variable {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]

def CharsX (τ : ∀ s, Representation K G (Ws s)) (Xc : Finset (G → K)) : Prop :=
  ∀ χ : G → K, χ ∈ Xc ↔ ∃ s, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = χ

def NearConstantMultiplicities (τ : ∀ s, Representation K G (Ws s)) (P1 : Formalism.IndefR.IndefiniteEpsilonOperator.Pair G K) (nbar de : ℝ) : Prop :=
  ∀ s, (1 - de) * nbar ≤ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ∧ (Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) P1 : ℝ) ≤ (1 + de) * nbar

end Group

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DatumFock
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {m n : ℕ}

section Subst

def dExp (m : ℕ) (p : D.what₂.Tau → ℕ) (e : D.what₂.Tau → ℤ) (τ : D.what₂.Tau) : ℤ := (p τ : ℤ) - ((m + 1) / 2 : ℕ) - e τ

end Subst

section Equiv

end Equiv

end Formalism.IndefR.Datum

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.DatumLemmas
section
noncomputable section

open Matrix

namespace Formalism.IndefR.Datum

end Formalism.IndefR.Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Datum.Brg

section Gen
variable {R : Type*} [CommRing R] (c : R →+* R) {n m : ℕ}

theorem hO_tr (I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a = (I * (y.map c)ᵀ * K * x).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a
      = ∑ b, ∑ d, ∑ c', I a b * c (y c' b) * K c' d * x d a :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c', I a b * c (y c' b) * K c' d * x d a := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem small_gen (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R) (hIG : I * G = 1)
    (hI : (I.map c)ᵀ = I) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((y * I)ᵀ i j) * G k i * K j l * (x * I)ᵀ k l =
      ∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a := by
  rw [sum_eq_trace, hO_tr, ← Matrix.trace_transpose]
  have e : ((y * I)ᵀ).map c = I * (y.map c)ᵀ := by
    rw [Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hI]
  rw [e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = (K * (x * ((I * G) * I * (y.map c)ᵀ))).trace := by simp only [Matrix.mul_assoc]
    _ = ((K * x) * (I * (y.map c)ᵀ)).trace := by rw [hIG, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]

theorem inv_gen (G I g g' : Matrix (Fin n) (Fin n) R) (hIG : I * G = 1) (hGI : G * I = 1) (hg : g * g' = 1)
    (h : (g.map c)ᵀ * G * g = G) : g' * I = I * (g.map c)ᵀ := by
  calc g' * I = (I * G) * g' * I := by rw [hIG, Matrix.one_mul]
    _ = I * ((g.map c)ᵀ * G * g) * g' * I := by rw [h]
    _ = I * (g.map c)ᵀ * (G * (g * g') * I) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, Matrix.mul_one, hGI, Matrix.mul_one]

theorem small_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g' * I = I * (g.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) : (k * x * g' * I)ᵀ = g.map c * (x * I)ᵀ * kᵀ := by
  rw [Matrix.mul_assoc (k * x), h]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem large_gen (hc : ∀ a, c (c a) = a) (G I : Matrix (Fin n) (Fin n) R) (K : Matrix (Fin m) (Fin m) R)
    (hGI : G * I = 1) (hI : (I.map c)ᵀ = I) (hK : (K.map c)ᵀ = K) (x y : Matrix (Fin m) (Fin n) R) :
    ∑ i, ∑ j, ∑ k, ∑ l, c ((I * (y.map c)ᵀ)ᵀ i j) * K k i * G j l * (I * (x.map c)ᵀ)ᵀ k l =
      c (∑ a, ∑ b, ∑ c', ∑ d, I a b * c (y c' b) * K c' d * x d a) := by
  have e0 : (y.map c).map c = y := by ext i j; simp [hc]
  have t : ∀ M : Matrix (Fin n) (Fin n) R, c M.trace = ((M.map c)ᵀ).trace := by
    intro M; simp [Matrix.trace, map_sum]
  have e : ((I * (y.map c)ᵀ)ᵀ).map c = y * I := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, e0, Matrix.transpose_map, hI]
  have e2 : ((I * (y.map c)ᵀ * K * x).map c)ᵀ = (x.map c)ᵀ * K * y * I := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, hI, hK, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [sum_eq_trace, hO_tr, t, e2, ← Matrix.trace_transpose, e]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = ((G * I) * ((x.map c)ᵀ * K * y * I)).trace := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hGI, Matrix.one_mul]

theorem large_act (I g g' : Matrix (Fin n) (Fin n) R) (k : Matrix (Fin m) (Fin m) R) (h : g * I = I * (g'.map c)ᵀ)
    (x : Matrix (Fin m) (Fin n) R) :
    (I * ((k * x * g').map c)ᵀ)ᵀ = k.map c * (I * (x.map c)ᵀ)ᵀ * gᵀ := by
  have k' : g'.map c * Iᵀ = Iᵀ * gᵀ := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this.symm
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.mul_assoc]
  rw [k']

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev GG (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := S.gram.map (incA D)
abbrev GI (S : HSp D) : Matrix (Fin S.rank) (Fin S.rank) (AE D) := (S.gram⁻¹).map (incA D)

theorem cA_inc (a : D.host.E) : cA D (incA D a) = incA D (star a) := by
  simp [cA, sigR, CMData.sig, inclR]; rfl

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => S.herm.eq _ _

theorem GG_GI (S : HSp D) : GG S * GI S = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_GG (S : HSp D) : GI S * GG S = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S))]
  simp

theorem GI_herm (S : HSp D) : ((GI S).map (cA D))ᵀ = GI S := by
  have h : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun h i) j))

theorem GG_herm (S : HSp D) : ((GG S).map (cA D))ᵀ = GG S := by
  refine Matrix.ext fun i j => ?_
  exact (cA_inc _).trans (congrArg (incA D) (congrFun (congrFun (gram_herm S) i) j))

theorem mt_mul_inv (S : HSp D) (g : GA D S) : Formalism.L2.Theta.mt S g * Formalism.L2.Theta.mt S g⁻¹ = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem inv_GI (S : HSp D) (g : GA D S) :
    Formalism.L2.Theta.mt S g⁻¹ * GI S = GI S * ((Formalism.L2.Theta.mt S g).map (cA D))ᵀ :=
  inv_gen (cA D) (GG S) (GI S) _ _ (GI_GG S) (GG_GI S) (mt_mul_inv S g) (mt_rel S g)

theorem bridgeSmall : BridgeSmall D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom S T (toTWsmall S T y) (toTWsmall S T x) = hO S T x y := by
      unfold hHom; rw [if_pos hr]
      exact small_gen (cA D) (GG S) (GI S) (GG T) (GI_GG S) (GI_herm S) x y
    unfold symplO sympl; rw [this]
  · unfold actHom; rw [if_pos hr]
    exact small_act (cA D) (GI S) _ _ _ (inv_GI S g) x

theorem trace_cA (a : AE D) :
    Algebra.trace (AF D.host.F) (AE D) (cA D a) = Algebra.trace (AF D.host.F) (AE D) a := by
  let f : AE D →ₐ[AF D.host.F] AE D := Algebra.TensorProduct.map (AlgHom.id _ _) D.sp.cm.sig
  have hf : ∀ a, f a = cA D a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [f, cA, sigR]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hff : f.comp f = AlgHom.id _ _ := AlgHom.ext fun a => by
    rw [AlgHom.comp_apply, hf, hf, cA_cA]; rfl
  let g : AE D ≃ₐ[AF D.host.F] AE D := AlgEquiv.ofAlgHom f f hff hff
  rw [← hf]
  exact Algebra.trace_eq_of_algEquiv g a

theorem bridgeLarge (hxi : star D.host.xi0 = -D.host.xi0) : BridgeLarge D := by
  intro S T hr
  refine ⟨fun x y => ?_, fun g h x => ?_⟩
  · have : hHom T S (toTWlarge S T y) (toTWlarge S T x) = cA D (hO S T x y) := by
      unfold hHom; rw [if_pos hr.le]
      exact large_gen (cA D) cA_cA (GG S) (GI S) (GG T) (GG_GI S) (GI_herm S) (GG_herm T) x y
    unfold symplO sympl
    rw [this, ← trace_cA (incA D D.host.xi0 * hO S T x y), map_mul, cA_inc, hxi, map_neg, neg_mul, map_neg]
  · unfold actHom; rw [if_pos hr.le]
    have k := inv_GI S g⁻¹
    rw [inv_inv] at k
    exact large_act (cA D) (GI S) _ _ _ k x

theorem star_purely_imaginary_eq_neg : star D.host.xi0 = -D.host.xi0 := by
  have hs : ∀ x : D.host.E, D.host.φ₀ (star x) = starRingEnd ℂ (D.host.φ₀ x) := fun x => by
    haveI := D.host.isCMField_hostE
    exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x
  have hd : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  apply D.host.φ₀.injective
  rw [hs, map_neg]
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, hd]
  simp [div_neg]

theorem bridgeLarge' : BridgeLarge D := bridgeLarge star_purely_imaginary_eq_neg

end Formalism.IndefR.Datum.Brg

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.WeilDatumUniqueOfDeterminants
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis Formalism.IndefR.InjectiveDecompositionAction
  IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.flipTwoThree

def DeterminantInUnitaryOne : Prop :=
  ∀ (D : D7) (V : HSp D) (g : GA D V), (mt V g).det * cA D (mt V g).det = 1

def SplitDetP : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ e, IsSplitIdem D e → ∀ x : (AE D)ˣ, (x : AE D) * cA D (x : AE D) = 1 →
    SuppAtU D e x → ∃ g : GA D V, SuppAt e V g ∧ (∃ x', IsDetAt e V g x') ∧ (mt V g).det = x

variable {D : D7}

theorem mt_one' (V : HSp D) : L2.Theta.mt V 1 = 1 := by
  simp [L2.Theta.mt, map_one]

section Scalar

variable (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χ χ' : (AE D)ˣ →* Circle)
    (ω ω' : GA D V × GA D W →* Module.End ℂ (Hth ψ V W))

end Scalar

section Side

end Side

end Formalism.IndefR.flipTwoThree

end
end

