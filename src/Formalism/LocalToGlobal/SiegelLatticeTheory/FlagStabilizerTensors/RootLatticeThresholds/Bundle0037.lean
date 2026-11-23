module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNorm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRho
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.AllRowsRho

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

def RedMatB (p : ℕ) {m : ℕ} (b : Fin m → Fin I.n → I.E) (x : I.Gf) (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∀ i, I.fmat x *ᵥ iv I (b i) - ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w

theorem redMat0_of {p m : ℕ} {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf}
    {M : Matrix (Fin m) (Fin m) (ZMod p)} (h : RedMatB I w p b x M) : RedMat0 I w p x M := ⟨b, hb, h⟩

theorem natSmul_Lq (k : ℕ) {z : Fin I.n → I.E ⊗[I.F] Af I.F} (hz : z ∈ Lq I w) :
    (k : I.E ⊗[I.F] Af I.F) • z ∈ Lq I w := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hz k

theorem redMatB_exists {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} (hx : x ∈ I.Kset) :
    ∃ M : Matrix (Fin m) (Fin m) (ZMod p), RedMatB I w p b x M := by
  have : NeZero p := ⟨hp.ne_zero⟩
  choose c hc using fun i => coords I w hp hcard hb (K_mv I hx (DictLat.iv_mem I (hb.1 i)))
  refine ⟨Matrix.of fun j i => ((c i j : ℤ) : ZMod p), fun i => ?_⟩
  have h2 : ∑ j, ((((c i j : ℤ) : ZMod p).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, (c i j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    exact sum_mem fun j _ => val_sub I w hp hcard (hb.1 j) (c i j)
  have := sub_mem (hc i) h2
  convert this using 1
  simp only [Matrix.of_apply]
  abel

theorem mkQ_natSmul (k : ℕ) (v : Fin I.n → I.E ⊗[I.F] Af I.F) :
    (Lq I w).mkQ ((k : I.E ⊗[I.F] Af I.F) • v) = ((k : ℤ)) • (Lq I w).mkQ v := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, natCast_zsmul]

theorem redMatB_unique {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ} (hm : m = I.n)
    {b : Fin m → Fin I.n → I.E} (hb : IsRedBasis0 I w b) {x : I.Gf} {M M' : Matrix (Fin m) (Fin m) (ZMod p)}
    (h : RedMatB I w p b x M) (h' : RedMatB I w p b x M') : M = M' := by
  subst hm
  have : NeZero p := ⟨hp.ne_zero⟩
  ext j i
  have hdiff : ∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
      ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) ∈ Lq I w := by
    have := sub_mem (h i) (h' i)
    convert this using 1
    abel
  have hz : ∑ l, ((((M' l i).val : ℕ) : ℤ) - (((M l i).val : ℕ) : ℤ)) • (Lq I w).mkQ (iv I (b l)) = 0 := by
    have h0 : (Lq I w).mkQ (∑ l, (((M' l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l) -
        ∑ l, (((M l i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b l)) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hdiff
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, map_sum] at h0
    simp only [mkQ_natSmul] at h0
    rw [← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  have hj := Formalism.L2.SG.Pf.RedConj0Pf.zcoef_A I w p hp hcard hb _ hz j
  have hj' : ((M' j i).val : ZMod p) - ((M j i).val : ZMod p) = 0 := by exact_mod_cast hj
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, sub_eq_zero] at hj'
  exact hj'.symm

theorem redMatB_mul {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → Fin I.n → I.E} (hb : ∀ i, b i ∈ I.L) {x y : I.Gf} (hx : x ∈ I.Kset)
    {M N : Matrix (Fin m) (Fin m) (ZMod p)} (hM : RedMatB I w p b x M) (hN : RedMatB I w p b y N) :
    RedMatB I w p b (x * y) (M * N) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  intro i
  have hAB : I.fmat (x * y) = I.fmat x * I.fmat y := rfl
  have s1 : I.fmat x *ᵥ (I.fmat y *ᵥ iv I (b i)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) ∈ Lq I w := by
    have := stab_w I w hx (hN i)
    rw [Matrix.mulVec_sub, Matrix.mulVec_sum] at this
    simpa only [Matrix.mulVec_smul] using this
  have s2 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (I.fmat x *ᵥ iv I (b k)) -
      ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun k _ => ?_
    rw [← smul_sub]
    exact natSmul_Lq I w _ (hM k)
  have e3 : ∑ k, (((N k i).val : ℕ) : I.E ⊗[I.F] Af I.F) •
        ∑ j, (((M j k).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) := by
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Int.cast_natCast, Nat.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.cast_mul, mul_comm]
  have s3 : ∑ j, (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : I.E ⊗[I.F] Af I.F) • iv I (b j) -
      ∑ j, ((((M * N) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ Lq I w := by
    rw [← Finset.sum_sub_distrib]
    refine sum_mem fun j _ => ?_
    have hc : (((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ) : ZMod p) = (M * N) j i := by
      rw [Int.cast_natCast, Nat.cast_sum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have := val_sub I w hp hcard (hb j) ((∑ k, (M j k).val * (N k i).val : ℕ) : ℤ)
    rw [hc] at this
    have := neg_mem this
    rwa [neg_sub] at this
  rw [e3] at s2
  have := add_mem (add_mem s1 s2) s3
  rw [hAB, ← Matrix.mulVec_mulVec]
  convert this using 1
  abel

theorem redMatB_one {p : ℕ} (hp : p.Prime) {m : ℕ} (b : Fin m → Fin I.n → I.E) :
    RedMatB I w p b 1 (1 : Matrix (Fin m) (Fin m) (ZMod p)) := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  intro i
  have e : ∑ j, ((((1 : Matrix (Fin m) (Fin m) (ZMod p)) j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • iv I (b j) =
      iv I (b i) := by
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.one_apply_eq, ZMod.val_one, Nat.cast_one, one_smul]
    · intro j _ hj; simp [Matrix.one_apply_ne hj]
    · simp
  rw [e, fmat_one, Matrix.one_mulVec, sub_self]
  exact zero_mem _

structure RedB (I : AutInst) (m : ℕ) where
  w : HeightOneSpectrum (𝓞 I.E)
  p : ℕ
  hp : p.Prime
  hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p
  hm : m = I.n
  b : Fin m → Fin I.n → I.E
  hb : IsRedBasis0 I w b

variable {I} {m : ℕ}


open Classical in
def matB (R : RedB I m) (x : I.Gf) : Matrix (Fin m) (Fin m) (ZMod R.p) :=
  if hx : x ∈ I.Kset then Classical.choose (redMatB_exists I R.w R.hp R.hcard R.hb hx) else 0

theorem matB_spec (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) : RedMatB I R.w R.p R.b x (matB R x) := by
  unfold matB; rw [dite_eq_left hx]; exact Classical.choose_spec (redMatB_exists I R.w R.hp R.hcard R.hb hx)

theorem matB_eq (R : RedB I m) {x : I.Gf} (hx : x ∈ I.Kset) {M : Matrix (Fin m) (Fin m) (ZMod R.p)}
    (h : RedMatB I R.w R.p R.b x M) : matB R x = M :=
  redMatB_unique I R.w R.hp R.hcard R.hm R.hb (matB_spec R hx) h

theorem matB_mul (R : RedB I m) {x y : I.Gf} (hx : x ∈ I.Kset) (hy : y ∈ I.Kset) :
    matB R (x * y) = matB R x * matB R y :=
  matB_eq R (K_mul I hx hy) (redMatB_mul I R.w R.hp R.hcard R.hb.1 hx (matB_spec R hx) (matB_spec R hy))

theorem matB_one (R : RedB I m) : matB R 1 = 1 := matB_eq R (K_one I) (redMatB_one I R.w R.hp R.b)

def rhoB (R : RedB I m) : Formalism.L2.SG.AllRowsOf.KSub I →* GL (Fin m) (ZMod R.p) :=
  MonoidHom.toHomUnits
    { toFun := fun x => matB R x
      map_one' := matB_one R
      map_mul' := fun x y => matB_mul R x.2 y.2 }

theorem rhoB_val (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) = matB R x := rfl

theorem rhoB_spec (R : RedB I m) (x : Formalism.L2.SG.AllRowsOf.KSub I) :
    RedMatB I R.w R.p R.b x ((rhoB R x : GL (Fin m) (ZMod R.p)) : Matrix (Fin m) (Fin m) (ZMod R.p)) :=
  matB_spec R x.2

end Formalism.L2.SG.Pf.AllRowsRho
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPinNormSt
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ComplexConjugate Matrix

namespace Formalism.L2.SG.Pf.Carrier.JointPinNormSt

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.JointQuot
  Formalism.L2.SG.Pf.Carrier.JointPin Formalism.L2.SG.Pf.Carrier.JointPinNorm Formalism.L2.SG.HidaSetting

section Lin

variable {n r : ℕ} (ε : Fin n → Bool)

theorem hJ_add_r (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  simp [hJ, Matrix.mulVec_add, dotProduct_add]

theorem hJ_sub_r (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  simp [hJ, Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_smul_r (x : Fin n → ℂ) (c : ℂ) (y : Fin n → ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  simp [hJ, Matrix.mulVec_smul, dotProduct_smul]

theorem hJ_zero_r (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp [hJ]

theorem hJ_sum_r {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (f : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, f i) = ∑ i ∈ s, hJ ε x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hJ_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hJ_add_r, ih]

theorem hJ_unit (M : Matrix (Fin n) (Fin n) ℂ) (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM]

theorem hJ_conj_swap (x y : Fin n → ℂ) : hJ ε x y = conj (hJ ε y x) :=
  Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_conj ε x y

theorem recon (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) : w = ∑ c ∈ s, (hJ ε (u c) w / κ c) • e c := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [Finset.sum_eq_single b]
    · rw [hue, if_pos rfl, div_self (hκ b), one_smul]
    · intro c _ hcb; rw [hue, if_neg hcb, zero_div, zero_smul]
    · intro h; exact absurd hb h
  | zero => simp [hJ_zero_r]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp only [hJ_add_r, add_div, add_smul, Finset.sum_add_distrib]
  | smul t x _ hx =>
    conv_lhs => rw [hx]
    simp only [hJ_smul_r, Finset.smul_sum, smul_smul, mul_div_assoc]

theorem zero_of_pair (e u : Fin r → Fin n → ℂ) (κ : Fin r → ℂ) (hκ : ∀ d, κ d ≠ 0)
    (hue : ∀ d c, hJ ε (u d) (e c) = if d = c then κ d else 0) (s : Finset (Fin r)) (w : Fin n → ℂ)
    (hw : w ∈ Submodule.span ℂ (e '' ↑s)) (h0 : ∀ c ∈ s, hJ ε (u c) w = 0) : w = 0 := by
  rw [recon ε e u κ hκ hue s w hw]
  exact Finset.sum_eq_zero fun c hc => by rw [h0 c hc, zero_div, zero_smul]

theorem orth_span (e : Fin r → Fin n → ℂ) (x : Fin n → ℂ) (s : Set (Fin r)) (hx : ∀ c ∈ s, hJ ε x (e c) = 0)
    (w : Fin n → ℂ) (hw : w ∈ Submodule.span ℂ (e '' s)) : hJ ε x w = 0 := by
  induction hw using Submodule.span_induction with
  | mem y hy => obtain ⟨b, hb, rfl⟩ := hy; exact hx b hb
  | zero => exact hJ_zero_r ε x
  | add y y' _ _ hy hy' => rw [hJ_add_r, hy, hy', add_zero]
  | smul t y _ hy => rw [hJ_smul_r, hy, mul_zero]

theorem spanLt_eq (e : Fin r → Fin n → ℂ) (a : ℕ) :
    spanLt e a = Submodule.span ℂ (e '' ↑(Finset.univ.filter fun b : Fin r => b.1 < a)) := by
  unfold spanLt
  congr 2
  ext b
  simp

theorem st_one_lin (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (G Gi M : Matrix (Fin n) (Fin n) ℂ)
    (hGi : G * Gi = 1) (hG : Gᴴ * Formalism.REAL.Jm ε * G = Formalism.REAL.Jm ε)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) (hee : ∀ a b, hJ ε (e a) (e b) = 0) (cv : Fin r → ℂ)
    (hcv : ∀ a, cv a ≠ 0) (hZ : ∀ a b, hJ ε (e a) (G *ᵥ e b) = if a = b then cv a else 0)
    (hN : InN ε e z M) (hN' : InN ε e z' (Gi * M * G)) : M = 1 := by
  classical
  have hGGi : ∀ x, G *ᵥ (Gi *ᵥ x) = x := fun x => by rw [Matrix.mulVec_mulVec, hGi, Matrix.one_mulVec]
  have hMG : ∀ x, G *ᵥ ((Gi * M * G) *ᵥ x) = M *ᵥ (G *ᵥ x) := fun x => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul]

  have hu1 : ∀ d c, hJ ε (G *ᵥ e d) (e c) = if d = c then conj (cv d) else 0 := by
    intro d c
    rw [hJ_conj_swap, hZ]
    by_cases h : c = d
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  have hu2 : ∀ d c, hJ ε (Gi *ᵥ e d) (e c) = if d = c then cv d else 0 := by
    intro d c
    rw [← hJ_unit ε G hG, hGGi, hZ]
  have hk1 : ∀ d, conj (cv d) ≠ 0 := fun d => by simpa using hcv d
  have hfx : ∀ x y, M *ᵥ x = x → hJ ε x (M *ᵥ y) = hJ ε x y := fun x y hx => by
    conv_lhs => rw [← hx]
    exact hJ_unit ε M hM x y

  have key : ∀ m : ℕ, ∀ c : Fin r, c.1 = m → M *ᵥ e c = e c ∧ M *ᵥ (G *ᵥ e c) = G *ᵥ e c := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro c hc
      have ih' : ∀ d : Fin r, d.1 < c.1 → M *ᵥ e d = e d ∧ M *ᵥ (G *ᵥ e d) = G *ᵥ e d :=
        fun d hd => ih d.1 (hc ▸ hd) d rfl
      have h1 : M *ᵥ e c = e c := by
        have hw := hN.1.1 c
        rw [spanLt_eq] at hw
        have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hw (by
          intro d hd
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
          rw [Matrix.sub_mulVec, Matrix.one_mulVec, hJ_sub_r, hfx _ _ (ih' d hd).2, sub_self])
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
        exact h0
      refine ⟨h1, ?_⟩
      have hw := hN'.1.1 c
      rw [spanLt_eq] at hw
      have h0 := zero_of_pair ε e (fun d => Gi *ᵥ e d) cv hcv hu2 _ _ hw (by
        intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [← hJ_unit ε G hG, hGGi, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, hMG, hJ_sub_r,
          hfx _ _ (ih' d hd).1, sub_self])
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      rw [← hMG, h0]
  have hfix1 : ∀ c, M *ᵥ e c = e c := fun c => (key c.1 c rfl).1
  have hfix2 : ∀ c, M *ᵥ (G *ᵥ e c) = G *ᵥ e c := fun c => (key c.1 c rfl).2

  have hall : ∀ v, M *ᵥ v = v := by
    intro v
    set S1 : Fin n → ℂ := ∑ c, (hJ ε (G *ᵥ e c) v / conj (cv c)) • e c with hS1
    set S2 : Fin n → ℂ := ∑ c, (hJ ε (e c) v / cv c) • (G *ᵥ e c) with hS2
    set v1 := v - S1 - S2 with hv1
    have hGe : ∀ d c, hJ ε (G *ᵥ e d) (G *ᵥ e c) = 0 := fun d c => by rw [hJ_unit ε G hG, hee]
    have ho1 : ∀ d, hJ ε (e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hee, mul_zero, Finset.sum_const_zero, sub_zero, hZ]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hcv d), sub_self]
    have ho2 : ∀ d, hJ ε (G *ᵥ e d) v1 = 0 := by
      intro d
      rw [hv1, hJ_sub_r, hJ_sub_r, hS1, hS2, hJ_sum_r, hJ_sum_r]
      simp only [hJ_smul_r, hGe, mul_zero, Finset.sum_const_zero, sub_zero, hu1]
      rw [Finset.sum_eq_single d (fun c _ hc => by rw [if_neg (Ne.symm hc), mul_zero]) (by simp), if_pos rfl,
        div_mul_cancel₀ _ (hk1 d), sub_self]
    have hv : v = v1 + S1 + S2 := by rw [hv1]; abel
    clear_value v1 S1 S2

    have hX : (M - 1) *ᵥ v1 ∈ spanLt e r := hN.2 v1 ho1
    have hGX : (Gi * M * G - 1) *ᵥ (Gi *ᵥ v1) ∈ spanLt e r :=
      hN'.2 _ (fun a => by rw [← hJ_unit ε G hG, hGGi]; exact ho2 a)
    have hw : (M - 1) *ᵥ v1 = G *ᵥ ((Gi * M * G - 1) *ᵥ (Gi *ᵥ v1)) := by
      rw [Matrix.sub_mulVec (Gi * M * G), Matrix.mulVec_sub, hMG, hGGi, Matrix.one_mulVec, hGGi,
        Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [spanLt_eq] at hX
    have h0 := zero_of_pair ε e (fun d => G *ᵥ e d) (fun d => conj (cv d)) hk1 hu1 _ _ hX (by
      intro d _
      rw [hw, hJ_unit ε G hG]
      exact orth_span ε e (e d) _ (fun c _ => hee d c) _ hGX)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, h0, hS1, hS2, Matrix.mulVec_sum, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hfix1, hfix2]
  exact Matrix.ext_of_mulVec_single fun i => by rw [hall, Matrix.one_mulVec]

end Lin

variable {D : D7}

theorem stOne_holds (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) : StOne X u u' := by
  intro v g cv hcv hZ
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 := fun a b => by
    rw [show X.eR a = X.crd (X.eX a) from rfl, show X.eR b = X.crd (X.eX b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, X.ee, map_zero]
  have hfrm : ∀ (w : D.what₂.Word) (c : Fin D.R.rS), frm X w 1 v (Fin.castSucc c) = rv X.B.I v (X.eR c) := by
    intro w c
    simp [frm, famSc, fam, Fin.snoc_castSucc]
  have hZ' : ∀ a b : Fin D.R.rS, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (uMat g *ᵥ rv X.B.I v (X.eR b)) =
      if a = b then cv (Fin.castSucc a) else 0 := by
    intro a b
    have := congrFun (congrFun hZ (Fin.castSucc a)) (Fin.castSucc b)
    unfold Formalism.L2.SG.RealObj.Zhat at this
    simp only [hfrm, Matrix.diagonal_apply, Fin.castSucc_inj] at this
    exact this
  have hmemUJ : ∀ y : Formalism.REAL.UJ (X.B.I.ε v), (uMat y)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * uMat y = Formalism.REAL.Jm (X.B.I.ε v) :=
    fun y => y.2
  have hone : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ StSet (NV X u v) (NV X u' v) g := by
    have h1 : ∀ w : D.what₂.Word, (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ NV X w v := by
      intro w
      show InN _ _ _ (uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)))
      have : uMat (1 : Formalism.REAL.UJ (X.B.I.ε v)) = 1 := rfl
      rw [this]
      refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> simp [Submodule.zero_mem]
    refine ⟨h1 u, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact h1 u'
  ext y
  refine ⟨fun hy => ?_, fun hy => by rw [Set.mem_singleton_iff.1 hy]; exact hone⟩
  obtain ⟨hy1, hy2⟩ := hy
  have hcoe : uMat (g⁻¹ * y * g) = uMat g⁻¹ * uMat y * uMat g := by
    simp [uMat]
  have hGi : uMat g * uMat g⁻¹ = 1 := by
    simp [uMat]
  have hN' : InN (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u')) (uMat g⁻¹ * uMat y * uMat g) := by
    rw [← hcoe]; exact hy2
  have hM := st_one_lin (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u'))
    (uMat g) (uMat g⁻¹) (uMat y) hGi (hmemUJ g) (hmemUJ y) hee (fun a => cv (Fin.castSucc a))
    (fun a => hcv.1 _) hZ' hy1 hN'
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  exact hM

theorem normBridge_of_zhat {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word} (P : Parts X u u')
    (hr : P.S.G.r = D.R.rS) (hZ : ZhatTr P hr) : NormBridge P hr :=
  normBridge_of_two P hr (stOne_holds X u u') hZ

end Formalism.L2.SG.Pf.Carrier.JointPinNormSt
end
end

