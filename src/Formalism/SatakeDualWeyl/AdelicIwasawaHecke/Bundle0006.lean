module

public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0004
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0001
public import Formalism.SatakeDualWeyl.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0002
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0005

@[expose] public section

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AfsplitB
section
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P
open Formalism.UG

section Tens
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

def afsplitIE (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] v.adicCompletion F →ₙ+* E ⊗[F] (FiniteAdeleRing (𝓞 F) F) where
  toFun := LinearMap.lTensor E (afsplitI v)
  map_zero' := map_zero _
  map_add' := map_add _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), hx, hx']
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy']
      | tmul c d =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, afsplitI_mul]

theorem afsplitIE_tmul (v : HeightOneSpectrum (𝓞 F)) (a : E) (x : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] x) = a ⊗ₜ[F] afsplitI v x := rfl

theorem afsplit_prV_tmul (w : HeightOneSpectrum (𝓞 F)) (a : E) (b : (FiniteAdeleRing (𝓞 F) F)) :
    prV (E := E) w (a ⊗ₜ[F] b) = a ⊗ₜ[F] (b w) := rfl

theorem afsplit_prV_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_self]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem afsplit_prV_IE_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v)
    (x : E ⊗[F] v.adicCompletion F) : prV (E := E) w (afsplitIE v x) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => rw [afsplitIE_tmul, afsplit_prV_tmul, afsplitI_ne v w h, TensorProduct.tmul_zero]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem afsplit_sigR_IE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (afsplitIE v x) = afsplitIE v (sigR σ (v.adicCompletion F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [sigR, afsplitIE_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def afsplitEps (E : Type) [CommRing E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) : E ⊗[F] (FiniteAdeleRing (𝓞 F) F) :=
  afsplitIE v 1

theorem afsplit_decomp (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :
    afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [afsplit_prV_tmul, afsplitIE_tmul, afsplitI_eval, he, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, mul_add]

theorem afsplit_eps_mul_IE (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) :
    afsplitEps E v * afsplitIE v x = afsplitIE v x := by
  have he : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitI v 1 := by
    rw [afsplitEps, Algebra.TensorProduct.one_def, afsplitIE_tmul]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, mul_zero]
  | tmul a b =>
    rw [he, afsplitIE_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← afsplitI_mul, one_mul]
  | add x y hx hy => rw [map_add (f := _), mul_add, hx, hy]

theorem afsplit_eps_idem (v : HeightOneSpectrum (𝓞 F)) :
    afsplitEps E v * afsplitEps E v = afsplitEps E v := by
  exact afsplit_eps_mul_IE (E := E) v 1

theorem afsplit_sigR_eps (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    sigR σ (FiniteAdeleRing (𝓞 F) F) (afsplitEps E v) = afsplitEps E v := by
  rw [afsplitEps, afsplit_sigR_IE, map_one]

theorem afsplit_prV_eps (v : HeightOneSpectrum (𝓞 F)) : prV (E := E) v (afsplitEps E v) = 1 := by
  exact afsplit_prV_IE (E := E) v 1

theorem afsplit_prV_eps_ne (v w : HeightOneSpectrum (𝓞 F)) (h : w ≠ v) :
    prV (E := E) w (afsplitEps E v) = 0 := by
  exact afsplit_prV_IE_ne (E := E) v w h 1

theorem afsplit_prV_inclE (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) (FiniteAdeleRing (𝓞 F) F) e) = inclE (F := F) (v.adicCompletion F) e := rfl

theorem afsplit_prV_comp_sigR (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    (prV (E := E) v).comp (sigR σ (FiniteAdeleRing (𝓞 F) F)) = (sigR σ (v.adicCompletion F)).comp (prV (E := E) v) := by
  refine RingHom.ext fun y => ?_
  simp only [RingHom.comp_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Tens

section Inj
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]

theorem afsplit_coord_prV (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (i : Module.Free.ChooseBasisIndex F E) (w : HeightOneSpectrum (𝓞 F)) (y : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) :
    TensorProduct.lid F (w.adicCompletion F) ((b.coord i).rTensor _ (prV (E := E) w y)) =
      (TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ y)) w := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; rfl
  | tmul a b =>
    rw [afsplit_prV_tmul]
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, afsplit_smul_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, afsplit_add_apply]

theorem afsplit_inj (y : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) (hy : ∀ w : HeightOneSpectrum (𝓞 F), prV (E := E) w y = 0) :
    y = 0 := by
  classical
  set b := Module.Free.chooseBasis F E
  have hc : ∀ i, TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ y) = 0 := by
    intro i
    ext w
    rw [← afsplit_coord_prV b i w y, hy w]
    simp only [map_zero]
    rfl
  have hcoord : ∀ (z : E ⊗[F] (FiniteAdeleRing (𝓞 F) F)) (i : Module.Free.ChooseBasisIndex F E),
      TensorProduct.equivFinsuppOfBasisLeft b z i = TensorProduct.lid F (FiniteAdeleRing (𝓞 F) F) ((b.coord i).rTensor _ z) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add x y hx hy => simp [hx, hy]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := (FiniteAdeleRing (𝓞 F) F)) b).injective
  rw [map_zero]
  ext i
  rw [hcoord, hc i]
  rfl

end Inj
end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawaA
section
open Formalism.UG Matrix

namespace Formalism.UG.P

section FIwasawaGen

variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

def fIwasawaH (x y : Fin n → L) : L := ∑ j, σ (x (Fin.rev j)) * y j

def fIwasawaUn (M : Matrix (Fin n) (Fin n) L) : Prop := cT σ M * antiJ L n * M = antiJ L n

theorem fIwasawa_antiJ (i j : Fin n) : antiJ L n i j = if j = Fin.rev i then 1 else 0 := by
  unfold antiJ
  try simp only [Matrix.of_apply]
  have hi := i.isLt
  have hj := j.isLt
  have hiff : ((i : ℕ) + (j : ℕ) + 1 = n) ↔ (j = Fin.rev i) := by
    rw [Fin.ext_iff, Fin.val_rev]; omega
  by_cases h : j = Fin.rev i
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

private theorem cT_apply' (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ M i j = σ (M j i) := by
  first | rfl | simp [cT] | (unfold cT; simp)

private theorem cT_mul_adelic_iwasawa_hecke (A B : Matrix (Fin n) (Fin n) L) : cT σ (A * B) = cT σ B * cT σ A := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cT_apply', Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem fIwasawa_gram (M : Matrix (Fin n) (Fin n) L) (a b : Fin n) :
    (cT σ M * antiJ L n * M) a b = fIwasawaH σ (fun i => M i a) (fun i => M i b) := by
  unfold fIwasawaH
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev k)]
  · simp [fIwasawa_antiJ, cT_apply']
  · intro l _ hl
    have : k ≠ Fin.rev l := fun h => hl (by rw [h, Fin.rev_rev])
    simp [fIwasawa_antiJ, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_H_single_left (p : Fin n) (w : Fin n → L) :
    fIwasawaH σ (Pi.single p 1) w = w (Fin.rev p) := by
  unfold fIwasawaH
  rw [Finset.sum_eq_single (Fin.rev p)]
  · simp
  · intro j _ hj
    have : Fin.rev j ≠ p := fun h => hj (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem fIwasawa_un_of_isometry (M : Matrix (Fin n) (Fin n) L)
    (h : ∀ x y, fIwasawaH σ (M *ᵥ x) (M *ᵥ y) = fIwasawaH σ x y) : fIwasawaUn σ M := by
  have hc : ∀ a : Fin n, (fun i => M i a) = M *ᵥ Pi.single a 1 := by
    intro a; ext i; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  unfold fIwasawaUn
  ext a b
  rw [fIwasawa_gram, hc a, hc b, h, fIwasawa_H_single_left, fIwasawa_antiJ]
  by_cases hb : b = Fin.rev a
  · subst hb; simp
  · simp [Pi.single_apply, hb, Ne.symm hb]

theorem fIwasawa_un_mul (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by
  unfold fIwasawaUn at *
  rw [cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by
    simp only [Matrix.mul_assoc], hA, hB]

theorem fIwasawa_antiJ_mul_antiJ : antiJ L n * antiJ L n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · rw [fIwasawa_antiJ, fIwasawa_antiJ, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.one_apply, h, Ne.symm h]
  · intro k _ hk
    simp [fIwasawa_antiJ, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

def fIwasawaInv (M : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  antiJ L n * cT σ M * antiJ L n

theorem fIwasawa_inv_mul (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    fIwasawaInv σ M * M = 1 := by
  unfold fIwasawaInv
  unfold fIwasawaUn at hM
  rw [show antiJ L n * cT σ M * antiJ L n * M = antiJ L n * (cT σ M * antiJ L n * M) by
    simp only [Matrix.mul_assoc], hM, fIwasawa_antiJ_mul_antiJ]

theorem fIwasawa_mul_inv (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    M * fIwasawaInv σ M = 1 := by
  have h := fIwasawa_inv_mul σ M hM
  first
  | exact mul_eq_one_comm.mp h
  | (rw [← Matrix.inv_eq_left_inv h]; exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h))

def fIwasawaMk (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) : GU σ n :=
  ⟨⟨M, fIwasawaInv σ M, fIwasawa_mul_inv σ M hM, fIwasawa_inv_mul σ M hM⟩, hM⟩

theorem fIwasawa_mk_val (M : Matrix (Fin n) (Fin n) L) (hM : fIwasawaUn σ M) :
    (((fIwasawaMk σ M hM : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = M := rfl

theorem fIwasawa_mem_un (g : GU σ n) :
    fIwasawaUn σ (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := g.2

end FIwasawaGen

end Formalism.UG.P
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
section
open Formalism.UG

noncomputable section

namespace Formalism.UG.P

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem fSatake_borel_iff (b : GU σ n) :
    IsBorelU b ↔ (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id := Iff.rfl

theorem fSatake_borel_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') :
    IsBorelU (b * b') := by
  rw [fSatake_borel_iff] at hb hb' ⊢
  simpa only [Subgroup.coe_mul, Units.val_mul] using hb.mul hb'

theorem fSatake_borel_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  rw [fSatake_borel_iff] at hb ⊢
  haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  simpa [Matrix.coe_units_inv] using this

theorem fSatake_diag_mul {M N : Matrix (Fin n) (Fin n) L} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (i : Fin n) : (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem fSatake_borel_diag_mul {b b' : GU σ n} (hb : IsBorelU b) (hb' : IsBorelU b') (i : Fin n) :
    (((b * b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b' : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
  have := fSatake_diag_mul ((fSatake_borel_iff b).1 hb) ((fSatake_borel_iff b').1 hb') i
  simpa only [Subgroup.coe_mul, Units.val_mul] using this

theorem fSatake_borel_diag_inv {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    (((b⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
  rw [← fSatake_borel_diag_mul (fSatake_borel_inv hb) hb i]
  simp

theorem fSatake_rev_iff (k l : Fin n) : (k : ℕ) + l + 1 = n ↔ k = l.rev := by
  have := k.isLt
  have := l.isLt
  rw [Fin.ext_iff, Fin.val_rev]
  omega

theorem fSatake_cTJ (M : Matrix (Fin n) (Fin n) L) (i l : Fin n) :
    (cT σ M * antiJ L n) i l = σ (M l.rev i) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l.rev]
  · rw [show antiJ L n l.rev l = 1 from if_pos ((fSatake_rev_iff l.rev l).2 rfl), mul_one]
    rfl
  · intro j _ hj
    rw [show antiJ L n j l = 0 from if_neg (fun h => hj ((fSatake_rev_iff j l).1 h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag_mat {M : Matrix (Fin n) (Fin n) L} (hb : ∀ i j : Fin n, j < i → M i j = 0)
    (hU : cT σ M * antiJ L n * M = antiJ L n) (i : Fin n) : σ (M i i) * M i.rev i.rev = 1 := by
  have h := congrFun (congrFun hU i) i.rev
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev] at h
  · rw [fSatake_cTJ, Fin.rev_rev,
      show antiJ L n i i.rev = 1 from if_pos ((fSatake_rev_iff i i.rev).2 (Fin.rev_rev i).symm)] at h
    exact h
  · intro l _ hl
    rw [fSatake_cTJ]
    rcases lt_or_gt_of_ne hl with h1 | h1
    · have h2 : i < l.rev := by
        simp only [Fin.lt_iff_val_lt_val, Fin.val_rev] at h1 ⊢
        omega
      rw [hb _ _ h2, map_zero, zero_mul]
    · rw [hb l i.rev h1, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fSatake_unit_diag {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    σ ((((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i.rev i.rev = 1 :=
  fSatake_unit_diag_mat hb b.2 i

theorem fSatake_diag_exists (e : Fin n → L) (he : ∀ i, σ (e i) * e i.rev = 1) :
    ∃ d : GU σ n, (((d : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal e ∧
      (((d⁻¹ : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        Matrix.diagonal (fun i => (e i)⁻¹) := by
  have hne : ∀ i, e i ≠ 0 := fun i h => by
    have := he i.rev
    rw [Fin.rev_rev, h, mul_zero] at this
    exact zero_ne_one this
  let g : GL (Fin n) L := ⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹),
    by simp [Matrix.diagonal_mul_diagonal, mul_inv_cancel₀ (hne _)],
    by simp [Matrix.diagonal_mul_diagonal, inv_mul_cancel₀ (hne _)]⟩
  have hc : cT σ (Matrix.diagonal e) = Matrix.diagonal (fun i => σ (e i)) := by
    ext a c
    by_cases h : a = c
    · subst h
      simp [cT]
    · simp [cT, Matrix.diagonal_apply, h, Ne.symm h]
  have hg : g ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    ext i l
    rw [hc, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [antiJ]
    split_ifs with h
    · have hl : l = i.rev := (fSatake_rev_iff l i).1 (by omega)
      subst hl
      simp [he i]
    · simp
  exact ⟨⟨g, hg⟩, rfl, rfl⟩

end Formalism.UG.P
end
end

-- bundled from Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LocalAlgebraInertPrime
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gen

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

end Gen

section Int

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

end Int

section Main

variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

end Main

end Formalism.UG.P
end
end

