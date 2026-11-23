module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0910
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLocalGaussSumNormSqEqAbsNormPow
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps
open Formalism.L2.Host (atFin IsUnitAt)

noncomputable section

namespace GlobalTheory.GaussMod

variable {E : Type} [Field E] [NumberField E]

theorem locK_congr {χ : HChar E} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (hχ : χ.LevelLe w a) {x y : 𝓞 E}
    (hx : x ∉ w.asIdeal) (hy : y ∉ w.asIdeal) (hx0 : (x : E) ≠ 0) (hy0 : (y : E) ≠ 0) (h : x - y ∈ w.asIdeal ^ a) :
    χ.locK w (Units.mk0 (x : E) hx0) = χ.locK w (Units.mk0 (y : E) hy0) := by
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hx1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hx
  have hy1 := (w.valuation_eq_one_iff_notMem (K := E)).2 hy
  have h1 : χ.loc w (atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹)) = 1 := by
    have e : ((atFin w (Units.mk0 _ hx0 * (Units.mk0 _ hy0)⁻¹) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) ((x : E) / y) := by
      simp [atFin, div_eq_mul_inv]
    refine hχ _ ?_ ?_
    · rw [IsUnitAt, e, hval, map_div₀, hx1, hy1, div_one]
    · rw [e, ← map_one (algebraMap E (w.adicCompletion E)), ← map_sub, hval, div_sub_one hy0, map_div₀, hy1, div_one]
      exact valuation_sub_le h
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

theorem gaussSumAt_normSq (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (c : Eˣ) (ha : a ≠ 0) (hE : ExpAt χ w a)
    (hu : IsUnitary χ) (hc : w.valuation E (c : E) = WithZero.exp (-((a + diffExp w : ℕ) : ℤ))) :
    ‖gaussSumAt χ w a c‖ ^ 2 = (Ideal.absNorm w.asIdeal : ℝ) ^ a := by
  classical
  have hχ : χ.LevelLe w a := (hE a).2 le_rfl
  have := w.isMaximal
  set P := w.asIdeal with hP
  have hfin : Finite (𝓞 E ⧸ P ^ a) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  haveI : Fintype (𝓞 E ⧸ P ^ a) := Fintype.ofFinite _
  have hval : ∀ z : E, Valued.v (algebraMap E (w.adicCompletion E) z) = w.valuation E z := fun z =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w z
  have hne0 : ∀ x : 𝓞 E, x ∉ P → (x : E) ≠ 0 := fun x hx h0 => hx (by
    have : x = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    rw [this]; exact P.zero_mem)
  let f : 𝓞 E → ℂ := fun x => psiAt w (algebraMap E (w.adicCompletion E) ((x : E) / c))
  have f_add : ∀ x y, f (x + y) = f x * f y := fun x y => by
    have e : ((x + y : 𝓞 E) : E) / c = (x : E) / c + (y : E) / c := by push_cast; ring
    show psiAt w _ = psiAt w _ * psiAt w _
    rw [e, map_add (f := _), psiAt_add]
  have f_zero : ∀ x ∈ P ^ a, f x = 1 := fun x hx => by
    apply psiAt_eq_one
    have h1 := valuation_sub_le (w := w) (y := x) (y' := 0) (by simpa using hx)
    rw [hval, map_div₀, hc, div_le_iff₀ (zero_lt_iff.2 WithZero.exp_ne_zero), ← WithZero.exp_add]
    convert h1 using 2 <;> (push_cast; ring)
  have f_congr : ∀ x y, x - y ∈ P ^ a → f x = f y := fun x y h => by
    rw [show x = y + (x - y) by ring, f_add, f_zero _ h, mul_one]
  let ψb : AddChar (𝓞 E ⧸ P ^ a) ℂ :=
    { toFun := fun q => f (Quotient.out q)
      map_zero_eq_one' := f_zero _ (by rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out])
      map_add_eq_mul' := fun q r => by
        rw [← f_add]
        apply f_congr
        rw [← Ideal.Quotient.eq, map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] }
  have ψb_mk : ∀ x, ψb (Ideal.Quotient.mk _ x) = f x := fun x =>
    f_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hout : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, (Quotient.out (u : 𝓞 E ⧸ P ^ a) : 𝓞 E) ∉ P := out_notMem w ha
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  let χb : (𝓞 E ⧸ P ^ a)ˣ →* ℂˣ :=
    { toFun := fun u => χ.locK w (Units.mk0 _ (hne0 _ (hout u)))
      map_one' := by
        rw [locK_congr hχ (hout 1) h1P _ (hne0 _ h1P)
          (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, map_one, Units.val_one])]
        rw [show (Units.mk0 (((1 : 𝓞 E)) : E) (hne0 _ h1P)) = 1 by ext; simp, map_one]
      map_mul' := fun u v => by
        have hm : (Quotient.out ((u * v : (𝓞 E ⧸ P ^ a)ˣ) : 𝓞 E ⧸ P ^ a) : 𝓞 E) -
            Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∈ P ^ a := by
          rw [← Ideal.Quotient.eq, map_mul, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
            Units.val_mul]
        have hp : Quotient.out (u : 𝓞 E ⧸ P ^ a) * Quotient.out (v : 𝓞 E ⧸ P ^ a) ∉ P := fun h =>
          (w.isPrime.mem_or_mem h).elim (hout u) (hout v)
        rw [locK_congr hχ (hout _) hp _ (hne0 _ hp) hm, ← map_mul]
        congr 1
        ext
        simp }
  have hG : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u)⁻¹ : ℂˣ) : ℂ) * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [gaussSumAt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [gaussTerm, dite_eq_right (hne0 _ (hout u))]
    rfl
  have hM : ∀ q : 𝓞 E ⧸ P ^ a, IsUnit q ↔ q ∉ P.map (Ideal.Quotient.mk (P ^ a)) := fun q => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)]
    constructor
    · intro hu hx
      have h1 := hu.map (Ideal.Quotient.factor (Ideal.pow_le_self ha : P ^ a ≤ P))
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx] at h1
      have := Ideal.Quotient.nontrivial_iff.2 w.isPrime.ne_top
      exact not_isUnit_zero h1
    · exact Ideal.Quotient.isUnit_mk_pow_of_notMem P
  have hψ : ∀ d : 𝓞 E ⧸ P ^ a, (∀ x, ψb (d * x) = 1) → d = 0 := fun d hd => by
    obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine GlobalTheory.GaussModulus.mem_pow_of_psiAt_trivial w a c hc d fun x => ?_
    have := hd (Ideal.Quotient.mk _ x)
    rw [← map_mul, ψb_mk] at this
    simpa [f] using this
  obtain ⟨r, ur, hur, hrP, hr1, hrχ⟩ := GlobalTheory.GaussModulus.exists_int_witness χ w a ha hE
  have hr0 : (r : E) ≠ 0 := hne0 r hrP
  have hur' : ur = Units.mk0 (r : E) hr0 := Units.ext hur
  rw [hur'] at hrχ
  obtain ⟨t, ht⟩ := Ideal.Quotient.isUnit_mk_pow_of_notMem P (n := a) hrP
  have hχt : ∃ t : (𝓞 E ⧸ P ^ a)ˣ, (∀ m ∈ P.map (Ideal.Quotient.mk (P ^ a)), ((t : 𝓞 E ⧸ P ^ a) - 1) * m = 0) ∧
      χb t ≠ 1 := by
    refine ⟨t, fun m hm => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [Ideal.mem_quotient_iff_mem (Ideal.pow_le_self ha)] at hm
      rw [ht, ← map_one (Ideal.Quotient.mk (P ^ a)), ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have e : P ^ (a - 1) * P = P ^ a := by rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 ha)]
      rw [← e]
      exact Ideal.mul_mem_mul hr1 hm
    · show χ.locK w _ ≠ 1
      rwa [locK_congr hχ (hout t) hrP _ hr0 (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out, ht])]
  obtain ⟨t0, ht0, hχ0⟩ := hχt
  have hnorm : ∀ u : (𝓞 E ⧸ P ^ a)ˣ, ‖((χb u : ℂˣ) : ℂ)‖ = 1 := fun u => hu _
  have hG' : gaussSumAt χ w a c = ∑ u : (𝓞 E ⧸ P ^ a)ˣ, (((χb u : ℂˣ) : ℂ))⁻¹ * ψb (u : 𝓞 E ⧸ P ^ a) := by
    rw [hG]
    simp only [Units.val_inv_eq_inv_val]
  rw [hG', GlobalTheory.gauss_units_norm_sq _ hM ψb hψ (fun u => ((χb u : ℂˣ) : ℂ)) (fun u v => by rw [map_mul, Units.val_mul])
    hnorm t0 ht0 (fun h => hχ0 (Units.ext h)), Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    map_pow]
  push_cast
  rfl

end GlobalTheory.GaussMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemMult
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeKeep

variable {D : D7} {V : HSp D}

theorem suppF_iff (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    SuppF V f g ↔ f • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 :=
  ⟨fun h => Matrix.ext fun i j => h i j, fun h i j => congrFun (congrFun h i) j⟩

theorem mt_mul (g h : GA D V) : Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := rfl

theorem mt_one : Formalism.L2.Theta.mt V 1 = 1 := rfl

theorem fix_mul {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : f • (b - 1) = b - 1) : f • (a * b - 1) = a * b - 1 := by
  have e : a * b - 1 = (a - 1) * b + (b - 1) := by rw [sub_mul, one_mul]; abel
  rw [e, smul_add, hb, ← smul_mul_assoc, ha]

theorem fix_inv {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] {f : A} {a b : Matrix n n A}
    (ha : f • (a - 1) = a - 1) (hb : a * b = 1) : f • (b - 1) = b - 1 := by
  have e : b - 1 = -((a - 1) * b) := by rw [sub_mul, one_mul, hb, neg_sub]
  rw [e, smul_neg, ← smul_mul_assoc, ha]

theorem suppF_mul {f : Formalism.L2.Theta.AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  rw [suppF_iff] at ha hb ⊢
  rw [mt_mul]
  exact fix_mul ha hb

theorem suppF_inv {f : Formalism.L2.Theta.AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  rw [suppF_iff] at ha ⊢
  exact fix_inv ha (by rw [← mt_mul, mul_inv_cancel, mt_one])

theorem suppF_one (f : Formalism.L2.Theta.AE D) : SuppF V f 1 := by
  rw [suppF_iff, mt_one, sub_self, smul_zero]

theorem exists_loc (V : HSp D) (f : Formalism.L2.Theta.AE D) : ∃ L : Subgroup (GA D V), ∀ g, g ∈ L ↔ SuppF V f g :=
  ⟨{ carrier := {g | SuppF V f g}, mul_mem' := suppF_mul, one_mem' := suppF_one f, inv_mem' := suppF_inv },
    fun _ => Iff.rfl⟩

end GlobalTheory.HeckeKeep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem pos_iff_smul_toV (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g : grp G β)
    (z : Fin G.n → ℂ) (c : ℂ) : c ≠ 0 →
    (0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ↔ 0 < (star (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)) ⬝ᵥ
      (herm G v β *ᵥ (c • ((toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)))).re) := by
  intro hc
  set M : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ) with hM
  set H := herm G v β
  have hsim := GlobalTheory.LKCx.grp_similitude_herm p G v β g
  have hs : (0 : ℚ) < (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := g.2.2
  set s : ℚ := (((g : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)
  have key : star (c • (M *ᵥ z)) ⬝ᵥ (H *ᵥ (c • (M *ᵥ z))) =
      ((Complex.normSq c * s : ℝ) : ℂ) * (star z ⬝ᵥ (H *ᵥ z)) := by
    have e1 : star (M *ᵥ z) ⬝ᵥ (H *ᵥ (M *ᵥ z)) = star z ⬝ᵥ ((Mᴴ * H * M) *ᵥ z) := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, e1, hsim, Matrix.smul_mulVec,
      dotProduct_smul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    push_cast
    rw [Complex.normSq_eq_conj_mul_self]
    simp [mul_comm]
  rw [key, Complex.re_ofReal_mul]
  have hpos : 0 < Complex.normSq c * (s : ℝ) :=
    mul_pos (Complex.normSq_pos.2 hc) (by exact_mod_cast hs)
  exact (mul_pos_iff_of_pos_left hpos).symm

end GlobalTheory.LKCx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodingerHerm

theorem sesq_apply (D : D7) {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D G x y = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [GlobalTheory.WeilSchrodinger.sesq, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    smul_eq_mul, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sesq_transpose_eq_form (D : D7) {k : ℕ} (J : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    GlobalTheory.WeilSchrodinger.sesq D Jᵀ y x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig J x y := by
  rw [sesq_apply, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rfl

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * M * P.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_neg,
    Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0, mul_zero, zero_mul] at hd
  rw [Fintype.card_fin, one_mul, mul_one] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

variable (D : D7) (B : Base D.host.F D.host.E) {n : ℕ} (X : Spc D.host.F D.host.E n) {r s : ℕ}

theorem det_J_ne_zero (hX : X.IsHerm D.sp.cm.sig B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace D.host.F) := inferInstance
  have h := det_ne_zero_of_hasSig (hX.sig w)
  intro h0
  apply h
  have hm : (X.J.map (B.emb w).1).det = (B.emb w).1 X.J.det := (RingHom.map_det _ _).symm
  rw [hm, h0, map_zero]

theorem mem_one_iff (z : D.host.E) : z ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨o, rfl⟩
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨z, h⟩, rfl⟩

theorem herm_nondeg_unimod (hX : X.IsHerm D.sp.cm.sig B r s) :
    (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
      Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L := by
  have hdet : X.Jᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact det_J_ne_zero D B X hX
  refine ⟨⟨fun x y => ?_⟩, ⟨fun x hx => ?_, fun y hy => ?_⟩, ?_⟩
  ·
    have hs : ∀ i j, star (X.J i j) = X.J j i := fun i j => hX.herm j i
    simp only [sesq_apply, starRingEnd_apply, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, Matrix.transpose_apply, hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  ·
    have h1 : star x ᵥ* X.Jᵀ = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [← Matrix.dotProduct_mulVec, ← sesq_apply]
      exact hx v
    have h2 : star x = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
    simpa using congrArg star h2
  ·
    have h1 : X.Jᵀ *ᵥ y = 0 := by
      refine dotProduct_eq_zero _ fun v => ?_
      rw [dotProduct_comm]
      have := hy (star v)
      rwa [sesq_apply, star_star] at this
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1
  ·
    show Formalism.E.hdual _ X.L = X.L
    ext x
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [hX.dual x]
    refine forall₂_congr fun y _ => ?_
    rw [sesq_transpose_eq_form, mem_one_iff]

end GlobalTheory.WeilSchrodingerHerm

end

theorem GlobalTheory.WeilSchrodingerHerm.main : ∀ (D : D7) (B : Base D.host.F D.host.E), B.IsGood D.sp.cm.sig →
    ∀ (n : ℕ) (X : Spc D.host.F D.host.E n) (r s : ℕ), X.IsHerm D.sp.cm.sig B r s →
      (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).IsSymm ∧ (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ).Nondegenerate ∧
        Formalism.HermitianLatticesTheory.IsUnimodular (GlobalTheory.WeilSchrodinger.sesq D X.Jᵀ) X.L :=
  fun D B _ _ X _ _ hX => GlobalTheory.WeilSchrodingerHerm.herm_nondeg_unimod D B X hX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivialOverRealsOfGramCongruent
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

theorem trivR_of_gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ),
    (∀ v : InfinitePlace G.F, ∃ W : GL (Fin G.n) ℂ, G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C) =
      (W : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (W : Matrix (Fin G.n) (Fin G.n) ℂ)) →
    ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1 := by
  intro p _ G β hW
  choose W hW using hW
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.bijective_realTensor_to_prod_matrixAlgebras_infPlaces p G
  obtain ⟨z, hz⟩ := hsurj (fun v => (W v : Matrix (Fin G.n) (Fin G.n) ℂ))
  obtain ⟨z', hz'⟩ := hsurj (fun v => (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ))
  have hz1 : ∀ v, G.psiR v z = (W v : Matrix (Fin G.n) (Fin G.n) ℂ) := fun v => congrFun hz v
  have hz2 : ∀ v, G.psiR v z' = (((W v)⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) :=
    fun v => congrFun hz' v
  have e1 : z * z' = 1 := hinj (funext fun v => show G.psiR v (z * z') = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.mul_inv])
  have e2 : z' * z = 1 := hinj (funext fun v => show G.psiR v (z' * z) = G.psiR v 1 by
    rw [map_mul, map_one, hz1, hz2, Units.inv_mul])
  refine ⟨⟨z, z', e1, e2⟩, ?_⟩
  unfold Triv
  rw [Units.val_one, map_one]
  apply hinj
  funext v
  show G.psiR v (z * inC G ℝ (β : G.C) * (starT G.star ℝ z).unop) = G.psiR v 1
  have hb : G.psiR v (inC G ℝ (β : G.C)) = G.psi v (β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (β : G.C)) = _
    rw [psiR_tmul, one_smul]
  rw [map_mul, map_mul, psiR_starT, hb, hz1, map_one]
  set Wm : Matrix (Fin G.n) (Fin G.n) ℂ := (W v : Matrix (Fin G.n) (Fin G.n) ℂ)
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  have hM : (G.gram v)⁻¹ * Wmᴴ * G.gram v * Wm = G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Wmᴴ, ← hW v, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hg, Matrix.one_mul]
  have hBA : ((G.gram v)⁻¹ * Wmᴴ * G.gram v) * (Wm * G.psi v (β : G.C)) = 1 := by
    rw [← Matrix.mul_assoc, hM, ← map_mul, Units.inv_mul, map_one]
  have hAB := mul_eq_one_comm.1 hBA
  simpa [Matrix.mul_assoc] using hAB

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndepStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_vanishing_combination_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  first | (exact @GlobalTheory.HomFixUniv.formVanish_chart_indep) | (exact GlobalTheory.HomFixUniv.formVanish_chart_indep) | (intros; apply GlobalTheory.HomFixUniv.formVanish_chart_indep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

variable {p : ℕ} [Fact p.Prime]

def IntC (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) : Prop :=
  ∀ i, coordL G w a i ∈ w.1.adicCompletionIntegers ℚ

end GlobalTheory.FinClsLoc
end
end

