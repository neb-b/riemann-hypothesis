module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeCoeffTensorAinfOfFrobeniusEqMatrixMul
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal Matrix

namespace GlobalTheory.FrobIntTensor

section Coord

variable {R O S T : Type} [CommRing R] [CommRing O] [Algebra R O] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] {d : Type} (b : Module.Basis d R O)

def coordT (k : d) : O ⊗[R] S →ₗ[R] S :=
  (TensorProduct.lid R S).toLinearMap ∘ₗ TensorProduct.map (b.coord k) LinearMap.id

theorem coordT_tmul (k : d) (o : O) (s : S) : coordT b k (o ⊗ₜ[R] s) = b.repr o k • s := by
  simp [coordT]

theorem coordT_map (f : S →ₐ[R] T) (k : d) (x : O ⊗[R] S) :
    coordT b k (Algebra.TensorProduct.map (AlgHom.id O O) f x) = f (coordT b k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s => rw [Algebra.TensorProduct.map_tmul, coordT_tmul, coordT_tmul, AlgHom.id_apply, map_smul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem coordT_mul_tmul (k : d) (z : O ⊗[R] S) (s : S) :
    coordT b k (z * ((1 : O) ⊗ₜ[R] s)) = coordT b k z * s := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o s' => rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, coordT_tmul, coordT_tmul, smul_mul_assoc]
  | add x y hx hy => simp only [add_mul, map_add (f := _), hx, hy]

theorem sum_coordT [Fintype d] (x : O ⊗[R] S) : ∑ k, b k ⊗ₜ[R] coordT b k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul o s =>
    conv_rhs => rw [← b.sum_repr o]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coordT_tmul, TensorProduct.smul_tmul]
  | add x y hx hy => simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

end Coord

section Witt

variable (l : ℕ) [Fact l.Prime]

def valSub : ValuationSubring (Cb l) where
  toSubring := (algebraMap (OCb l) (Cb l)).range
  mem_or_inv_mem' x := by
    rcases (ValuationRing.iff_isInteger_or_isInteger (OCb l) (Cb l)).mp inferInstance x with h | h
    · obtain ⟨y, hy⟩ := h
      exact Or.inl ⟨y, hy⟩
    · obtain ⟨y, hy⟩ := h
      exact Or.inr ⟨y, hy⟩


set_option synthInstance.maxHeartbeats 400000 in
def toValSub : OCb l →+* valSub l :=
  (algebraMap (OCb l) (Cb l)).codRestrict (valSub l) fun x => ⟨x, rfl⟩

theorem map_toValSub (x : Ainf l) :
    WittVector.map (valSub l).subtype (WittVector.map (toValSub l) x) = inclW l x := by
  ext m
  simp only [WittVector.map_coeff, inclW]
  rfl

theorem mem_range_inclW {n : Type} [Fintype n] (v : n → WCb l) (Y : Matrix n n (Ainf l))
    (h : ∀ i, frobW l (v i) = ∑ j, inclW l (Y i j) * v j) (i : n) : v i ∈ (inclW l).range := by
  have key := GlobalTheory.witt_matrix_coeff_mem_of_frobenius l (valSub l) (Matrix.of fun i (_ : n) => v i)
    (Y.map (WittVector.map (toValSub l))) (Or.inl (by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.of_apply, map_toValSub]
      rw [WittVector.frobenius_eq_map_frobenius]
      exact h i))
  have hc : ∀ m, ∃ y : OCb l, algebraMap (OCb l) (Cb l) y = (v i).coeff m := fun m => key i i m
  refine ⟨WittVector.mk l fun m => Classical.choose (hc m), ?_⟩
  ext m
  rw [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  exact Classical.choose_spec (hc m)

end Witt

section Main

theorem coordT_inclO {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] {d : Type}
    (b : Module.Basis d ℤ_[l] O) (k : d) (y : OA l O) :
    coordT b k (inclO l O y) = inclW l (coordT b k y) :=
  coordT_map b (inclWA l) k y

theorem mem_range_inclO : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {n : Type} [Fintype n] (v : n → OW l O)
    (Y : Matrix n n (OA l O)), (∀ i, frobOW l O (v i) = (Y.map (inclO l O) *ᵥ v) i) →
    ∀ i, v i ∈ (inclO l O).range := by
  intro l _ O _ _ _ _ n _ v Y h i
  classical
  let b := Module.Free.chooseBasis ℤ_[l] O
  let v' : n × Module.Free.ChooseBasisIndex ℤ_[l] O → WCb l := fun p => coordT b p.2 (v p.1)
  let Yt : Matrix (n × Module.Free.ChooseBasisIndex ℤ_[l] O) (n × Module.Free.ChooseBasisIndex ℤ_[l] O)
      (Ainf l) := fun p q => coordT b p.2 (Y p.1 q.1 * (b q.2 ⊗ₜ[ℤ_[l]] (1 : Ainf l)))
  have hv : ∀ j, v j = ∑ m, (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) * ((1 : O) ⊗ₜ[ℤ_[l]] v' (j, m)) := by
    intro j
    conv_lhs => rw [← sum_coordT b (v j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hY : ∀ p, frobW l (v' p) = ∑ q, inclW l (Yt p q) * v' q := by
    rintro ⟨i', k⟩
    have e1 : frobW l (v' (i', k)) = coordT b k (frobOW l O (v i')) := (coordT_map b (frobW l) k (v i')).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, h i', Matrix.mulVec, dotProduct, map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.map_apply]
    conv_lhs => rw [hv j]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have e2 : inclO l O (Y i' j) * (b m ⊗ₜ[ℤ_[l]] (1 : WCb l)) =
        inclO l O (Y i' j * (b m ⊗ₜ[ℤ_[l]] (1 : Ainf l))) := by
      rw [map_mul, inclO_tmul, map_one]
    rw [← mul_assoc, e2, coordT_mul_tmul, coordT_inclO]
  have hr : ∀ p, v' p ∈ (inclW l).range := mem_range_inclW l v' Yt hY
  refine ⟨∑ k, b k ⊗ₜ[ℤ_[l]] Classical.choose (hr (i, k)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  conv_rhs => rw [← sum_coordT b (v i)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (inclO_tmul _ _).trans (congrArg (fun w => b k ⊗ₜ[ℤ_[l]] w) (Classical.choose_spec (hr (i, k))))

end Main

end GlobalTheory.FrobIntTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
section
set_option synthInstance.maxHeartbeats 400000
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

def galD (g : GQ l) : Per.BdRp l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := Per.σDp g
  commutes' z := (GlobalTheory.MemLoc.ActLaws.σDp_aDp g _).trans (congrArg (GlobalTheory.MemLoc.aDp l) ((galA g).commutes z))

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def galOD (g : GQ l) : OD l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (galD g)

variable {O}

theorem TWact_smul_of {G Qp LL R : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL] [Algebra Qp LL] [Algebra O LL]
    [TopologicalSpace LL] [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G Qp LL O) (g : G) (r : R)
    (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y =>
    simp only [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul,
      map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

def rhoD {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l)
    (y : ι → OD l ↥(OL LL)) : ι → OD l ↥(OL LL) :=
  jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem TWact_galOD_smul {LL : FinExt l} (T : QLat LL) (h : GQ l) (g : Gl l) (c : OD l ↥(OL LL))
    (z : TW (OD l ↥(OL LL)) T) :
    TWact (galOD ↥(OL LL) h) T g (c • z) = galOD ↥(OL LL) h c • TWact (galOD ↥(OL LL) h) T g z :=
  TWact_smul_of (galOD ↥(OL LL) h) T g c z


set_option synthInstance.maxHeartbeats 400000 in
theorem rhoD_smul {LL : FinExt l} {ι : Type} (T : QLat LL)
    (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (g : Gl l) (c : OD l ↥(OL LL))
    (y : ι → OD l ↥(OL LL)) : rhoD T jD g (c • y) = galOD ↥(OL LL) (sQ l g) c • rhoD T jD g y := by
  have h1 : jD (c • y) = c • jD y := jD.map_smul c y
  have h2 := TWact_galOD_smul T (sQ l g) g c (jD y)
  have h3 := jD.symm.map_smul (galOD ↥(OL LL) (sQ l g) c) (TWact (galOD ↥(OL LL) (sQ l g)) T g (jD y))
  exact (congrArg (fun z => jD.symm (TWact (galOD ↥(OL LL) (sQ l g)) T g z)) h1).trans
    ((congrArg jD.symm h2).trans h3)

variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type}


open Classical in
open Classical in
variable (O) in
def hatR (f : K⟦X⟧) : Ahat O K l e := if h : f ∈ Rpi O K l e then toHat O K l e ⟨f, h⟩ else 0

theorem hatR_of_mem {f : K⟦X⟧} (h : f ∈ Rpi O K l e) : hatR O f = toHat O K l e ⟨f, h⟩ := by
  rw [hatR, dite_eq_left h]

def YD (v : Vec K a ι) : ι → OD l O := fun i => ϖ.iD t K (fun τ => hatR O (v τ i))


variable (K) in
def ED : OD l O := ϖ.iD t K (fun _ => Ehat O K l e)

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mem_Rpi_of_mem_Man {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (τ : ZMod a) (i : ι) :
    v τ i ∈ Rpi O K l e :=
  mem_tot.1 (P.mem_Man.1 hv) τ i

theorem YD_add {P : PhiMod O K l e a ι} {v v' : Vec K a ι} (hv : v ∈ P.Man) (hv' : v' ∈ P.Man) :
    YD t ϖ (v + v') = YD t ϖ v + YD t ϖ v' := by
  funext i
  simp only [YD, Pi.add_apply]
  rw [← map_add (f := _)]
  congr 1
  funext τ
  rw [Pi.add_apply, hatR_of_mem (O := O) (add_mem (mem_Rpi_of_mem_Man hv τ i) (mem_Rpi_of_mem_Man hv' τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv' τ i), ← map_add]
  rfl

theorem YD_E_pow_smul {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (k : ℕ) :
    YD t ϖ (E K l e ^ k • v) = ED K t ϖ ^ k • YD t ϖ v := by
  funext i
  simp only [YD, ED, Pi.smul_apply, smul_eq_mul]
  rw [← map_pow, ← map_mul]
  congr 1
  funext τ
  have hE : E K l e ∈ Rpi O K l e := E_mem (K := K) l e _
  rw [Pi.mul_apply, Pi.pow_apply, hatR_of_mem (O := O) (mul_mem (pow_mem hE k) (mem_Rpi_of_mem_Man hv τ i)),
    hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i), ← toHat_E, ← map_pow, ← map_mul]
  rfl

theorem iD_eq_YD {P : PhiMod O K l e a ι} {v : Vec K a ι} (hv : v ∈ P.Man) (i : ι) (w : ZMod a → Ahat O K l e)
    (hw : ∀ τ, algebraMap _ (AhatE O K l e) (w τ) = hat O l e (v τ i)) : ϖ.iD t K w = YD t ϖ v i := by
  simp only [YD]
  congr 1
  funext τ
  rw [hatR_of_mem (O := O) (mem_Rpi_of_mem_Man hv τ i)]
  apply algebraMap_AhatE_injective l e
  rw [hw τ]
  exact hat_coe_Rpi l e ⟨v τ i, mem_Rpi_of_mem_Man hv τ i⟩

end GlobalTheory.GalStep

namespace GlobalTheory.GalStep

theorem mem_span_of_pow_mul {R : Type} [CommRing R] {d : R} (hd : ∀ y : R, d * y = 0 → y = 0) (p n : ℕ) {y : R}
    (h : d ^ p * y ∈ Ideal.span {d ^ (p + n)}) : y ∈ Ideal.span {d ^ n} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h0 : d ^ p * (y - z * d ^ n) = 0 := by rw [mul_sub, ← hz, pow_add]; ring
  have h1 : ∀ p : ℕ, ∀ y : R, d ^ p * y = 0 → y = 0 := by
    intro p
    induction p with
    | zero => intro y h; simpa using h
    | succ p ih => intro y h; exact ih y (hd _ (by rw [← h, pow_succ]; ring))
  have := h1 p _ h0
  rw [sub_eq_zero] at this
  exact Ideal.mem_span_singleton'.2 ⟨z, this.symm⟩
end GlobalTheory.GalStep

namespace GlobalTheory.GalStep
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
variable {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tail_step (P : PhiMod O K l e a ι) (hnz : ∀ y : OD l O, ED K t ϖ * y = 0 → y = 0)
    (hman : ∀ α : ℕ, (∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) →
      ∀ w ∈ P.Mext (invL l (S O K e)), E K l e ^ α • P.xiExt w ∈ P.Man)
    (hdesc : ∀ (i : ℕ) (w : Vec K a ι), w ∈ P.Mext (invL l (S O K e)) →
      (fun τ j => descN K i (w τ j)) ∈ P.Mext (invL l (S O K e)))
    (α β₀ n : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) {m : Vec K a ι} (hm : m ∈ P.M)
    (hn : E K l e ^ n • P.EN m ∈ P.Man) {wx : Vec K a ι} (hwx : wx ∈ P.Mext (invL l (S O K e)))
    (hwxdef : P.xiExt wx = E K l e ^ (β₀ + n) • m) (j : ι)
    (hD1 : ED K t ϖ * YD t ϖ (E K l e ^ α • P.xiExt (fun τ k => descN K 1 (wx τ k))) j ∈
      Ideal.span {ED K t ϖ ^ (α + (β₀ + n))}) :
    YD t ϖ (E K l e ^ n • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ n} := by
  obtain ⟨x, hxdef⟩ : ∃ x, x = E K l e ^ (β₀ + n) • m := ⟨_, rfl⟩
  rw [← hxdef] at hwxdef
  obtain ⟨γ, hγ⟩ : ∃ γ, γ = α + (β₀ + n) := ⟨_, rfl⟩
  rw [← hγ] at hD1
  have hwx1 : (fun τ k => descN K 1 (wx τ k)) = fun τ k => N K (wx τ k) := by
    funext τ k
    simp [descN, descPochhammer_one]
  have hconn : P.xiExt (fun τ k => descN K 1 (wx τ k)) = P.conn x := by
    rw [hwx1, ← P.conn_xiExt, hwxdef]
  have hcM : E K l e ^ α • P.conn x ∈ P.Man := by
    rw [← hconn]
    exact hman α hα _ (hdesc 1 wx hwx)
  have hE : E K l e ∈ Rpi O K l e := E_mem l e _
  have hD1' : YD t ϖ (E K l e ^ (α + 1) • P.conn x) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 := congrFun (YD_E_pow_smul t ϖ hcM 1) j
    rw [smul_smul, ← pow_add, add_comm 1 α, Pi.smul_apply, smul_eq_mul, pow_one] at h1
    rw [h1]
    rwa [hconn] at hD1
  have hNE : N K (E K l e) ∈ Rpi O K l e := N_mem (derivative_mem_R l hE)
  obtain ⟨y1, hy1def⟩ : ∃ y1, y1 = (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) • m := ⟨_, rfl⟩
  have hy1 : y1 ∈ P.Man := hy1def ▸ P.smul_mem_Man (mul_mem (natCast_mem _ _) hNE) (P.M_le_Man hm)
  have hkey : E K l e ^ (α + 1) * N K (E K l e ^ (β₀ + n)) =
      E K l e ^ γ * (((β₀ + n : ℕ) : PowerSeries K) * N K (E K l e)) := by
    rw [hγ]
    rcases Nat.eq_zero_or_pos (β₀ + n) with h0 | h0
    · rw [h0, pow_zero, Derivation.map_one_eq_zero, Nat.cast_zero]
      ring
    · obtain ⟨b, hb⟩ : ∃ b, β₀ + n = b + 1 := ⟨β₀ + n - 1, by omega⟩
      rw [hb, Derivation.leibniz_pow, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
      push_cast
      ring
  have hdec : E K l e ^ (α + 1) • P.conn x = E K l e ^ γ • y1 + E K l e ^ γ • P.EN m := by
    funext τ i
    rw [hxdef, P.conn_smul, hy1def, P.EN_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hγ] at hkey ⊢
    linear_combination (m τ i) * hkey
  have hγM : E K l e ^ γ • y1 ∈ P.Man := P.smul_mem_Man (pow_mem hE γ) hy1
  have hENM : E K l e ^ γ • P.EN m ∈ P.Man := by
    have h1 : E K l e ^ (α + 1) • P.conn x ∈ P.Man := by
      rw [pow_succ, mul_comm, mul_smul]
      exact P.smul_mem_Man hE hcM
    have h2 : E K l e ^ γ • P.EN m = E K l e ^ (α + 1) • P.conn x - E K l e ^ γ • y1 := by
      rw [hdec]
      abel
    rw [h2]
    exact sub_mem h1 hγM
  have hsum := congrFun (YD_add t ϖ hγM hENM) j
  rw [← hdec, Pi.add_apply] at hsum
  have hy1' : YD t ϖ (E K l e ^ γ • y1) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    rw [YD_E_pow_smul t ϖ hy1 γ, Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hEN : YD t ϖ (E K l e ^ γ • P.EN m) j ∈ Ideal.span {ED K t ϖ ^ γ} := by
    have h1 : YD t ϖ (E K l e ^ γ • P.EN m) j =
        YD t ϖ (E K l e ^ (α + 1) • P.conn x) j - YD t ϖ (E K l e ^ γ • y1) j := by
      rw [hsum]
      ring
    rw [h1]
    exact sub_mem hD1' hy1'
  have hsplit : E K l e ^ γ • P.EN m = E K l e ^ (α + β₀) • (E K l e ^ n • P.EN m) := by
    rw [smul_smul, ← pow_add, hγ, add_assoc]
  rw [hsplit, YD_E_pow_smul t ϖ hn (α + β₀), Pi.smul_apply, smul_eq_mul, hγ, ← add_assoc] at hEN
  exact mem_span_of_pow_mul hnz (α + β₀) n hEN
end GlobalTheory.GalStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NablaPowApplySmulLeibnizStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nabla_pow_apply_smul_leibniz : ∀ {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι} (C : Conn P) (k : ℕ) (f : ZMod a → K⟦X⟧) (v : Vec K a ι), (C.nabla ^ k) (f • v) = ∑ p ∈ Finset.range (k + 1), (k.choose p : K⟦X⟧) • ((fun τ => (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)) • (C.nabla ^ (k - p)) v) := by
  intro O K _ _ _ _ _ l e a ι _ _ P C k f v
  let D (p : ℕ) (τ : ZMod a) := (⇑(PowerSeries.derivative (R := K)))^[p] (f τ)
  have h (n : ℕ) : (C.nabla ^ n) (f • v) = ∑ p ∈ Finset.range (n + 1),
      n.choose p • (D p • (C.nabla ^ (n - p)) v) := by
    induction n with
    | zero => simp [D]
    | succ n ih =>
      rw [Finset.sum_choose_succ_nsmul (fun i j => D i • (C.nabla ^ j) v) n,
        pow_succ', mul_apply_eq_comp, ih, map_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpn : p ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hp)
      rw [map_nsmul, C.leibniz, smul_add, add_comm]
      congr 2
      · rw [show n + 1 - p = n - p + 1 by omega, pow_succ', mul_apply_eq_comp]
      · congr 1
        funext τ
        exact (Function.iterate_succ_apply' _ _ _).symm
  rw [h k]
  exact Finset.sum_congr rfl fun p _ => (Nat.cast_smul_eq_nsmul K⟦X⟧ _ _).symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatDegreeMinpolyRootNegPrimeUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.InertiaDeg
open Polynomial

theorem natDegree_minpoly_root_neg_l : ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) (π : Om l), 0 < N → π ^ N = -(l : Om l) → ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) → (minpoly E π).natDegree = N := by
  intro l _ N π hN hπ E _ _ hE
  have hl0 : (0 : ℝ) < l := by linarith [Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)]
  set Q : E[X] := Polynomial.X ^ N + Polynomial.C ((l : ℕ) : E) with hQ
  have hQm : Q.Monic := by
    rw [hQ]; exact monic_X_pow_add_C _ hN.ne'
  have hQr : aeval π Q = 0 := by
    rw [hQ]; simp [hπ]
  have hint : IsIntegral E π := ⟨Q, hQm, by rwa [aeval_def] at hQr⟩
  have hdvd : minpoly E π ∣ Q := minpoly.dvd _ _ hQr
  have hQdeg : Q.natDegree = N := by rw [hQ]; exact natDegree_X_pow_add_C
  have hle : (minpoly E π).natDegree ≤ N := by
    rw [← hQdeg]; exact natDegree_le_of_dvd hdvd hQm.ne_zero
  have hpos : 0 < (minpoly E π).natDegree := minpoly.natDegree_pos hint
  have hmon := minpoly.monic hint
  set P := (minpoly E π).map (algebraMap E (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hπn : ‖π‖ ^ N = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hπ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  have hroots : ∀ a ∈ P.roots, ‖a‖ = ‖π‖ := by
    intro a ha
    have h1 : P ∣ Q.map (algebraMap E (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : (Q.map (algebraMap E (Om l))).IsRoot a := (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ N = -(l : Om l) := by
      rw [hQ] at h2
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ N = ‖π‖ ^ N := by
      rw [← norm_pow, h3, ← hπ, norm_pow]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hN.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖π‖ ^ (minpoly E π).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap E (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖π‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = algebraMap E (Om l) ((minpoly E π).eval 0) := by
    rw [hP, Polynomial.eval_map, ← map_zero (algebraMap E (Om l)), Polynomial.eval₂_at_apply]
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne', eq_comm, neg_eq_zero] at hπ
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) hπ
  have hρ : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  have hy0 : algebraMap E (Om l) ((minpoly E π).eval 0) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hρ _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow (hE ((minpoly E π).eval 0)) hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (N : ℤ)) = (l : ℝ) ^ (-((minpoly E π).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hπn, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (N : ℤ) = -((minpoly E π).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 (Formalism.MainNotions.N.PreambleDegrees.Loc.one_lt_l (l := l)).ne' h8
  have h10 : (N : ℤ) ∣ ((minpoly E π).natDegree : ℤ) := ⟨-m, by linarith⟩
  exact le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))

end GlobalTheory.InertiaDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowPlacesSatisfyRowHypothesisAtQAndDStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := by
  first | exact @GlobalTheory.RowBoundB.row_bound | exact GlobalTheory.RowBoundB.row_bound | (intros; apply GlobalTheory.RowBoundB.row_bound <;> assumption)
end

