module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseIdealsCompletionEqOfModulusUnit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairIdealAt

theorem completion_eq_of_modul_unit : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) (ρ : ℕ) (v : GlobalTheory.FinPl.Pl D), 0 < ρ → GlobalTheory.SeeSaw.idV ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) v = GlobalTheory.SeeSaw.idV 1 v → (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹) ≠ 0) ∧ (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹) ≠ 0) ∧ ∀ s, s ∈ GlobalTheory.SeeSaw.idV ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ - 1 + 1))⁻¹ * (P.stA sc ^ (2 * ρ - (ρ - 1)) * (P.stAbar sc ^ (ρ - 1 + 1))⁻¹))⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹) v := by
  intro D T L P sc ρ v hρ hM
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D
  have hMo : ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact P.modul_ne_bot sc
  have hS : P.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).1
  have hT : P.stAbar sc ≠ 0 := mul_ne_zero hAb (inv_ne_zero hMo)
  have e1 : ρ - 1 + 1 = ρ := by omega
  have e2 : 2 * ρ - (ρ - 1) = ρ + 1 := by omega
  have hneg : ∀ k : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ k)⁻¹ =
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 ^ k)⁻¹ := by
    intro k
    rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_pow]
    congr 1
    congr 1
    apply FractionalIdeal.spanSingleton_eq_spanSingleton.2
    refine ⟨-1, ?_⟩
    rw [Units.smul_def]
    simp
  rw [e1, e2, hneg, hneg]
  set X := FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 with hXdef
  have hX : X ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hx
  refine ⟨mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))),
    mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX)) (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT))), ?_⟩
  have key : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ *
      ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ =
      FractionalIdeal.spanSingleton _ D.host.xi0⁻¹ * ((X ^ (ρ + 1))⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ (ρ + 1))⁻¹))⁻¹ := by
    rw [← FractionalIdeal.spanSingleton_inv, ← hXdef]
    have hTd : P.stAbar sc = D.host.AAbar * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := rfl
    rw [hTd]
    simp only [mul_inv, inv_inv, pow_succ, mul_pow]
    calc _ = (X⁻¹ * X) * (D.host.AAbar * ((X ^ ρ) * ((P.stA sc ^ ρ * P.stA sc)⁻¹ * ((D.host.AAbar : GlobalTheory.SeeSaw.FI D) ^ ρ *
          (((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) ^ ρ))) * ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) := by
          rw [inv_mul_cancel₀ hX, one_mul, mul_inv]
      _ = _ := by ring
  have hB0 : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) * ((X ^ ρ)⁻¹ * (P.stA sc ^ (ρ + 1) * (P.stAbar sc ^ ρ)⁻¹))⁻¹ ≠ 0 :=
    mul_ne_zero hAb (inv_ne_zero (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hX))
      (mul_ne_zero (pow_ne_zero _ hS) (inv_ne_zero (pow_ne_zero _ hT)))))
  obtain ⟨y, hy0, hy⟩ := GlobalTheory.IdVGen.idV_gen D v _ hB0
  have h1 := GlobalTheory.Core.Mi.LatMatch.DiUnit.eq_one_iff.1 (GlobalTheory.Core.Mi.LatMatch.DiUnit.inv_eq_one hM)
  have hp := GlobalTheory.SeeSaw.IdVMul.idV_mul_gen D v _ _ y 1 hy0 one_ne_zero hy h1
  rw [mul_one, key] at hp
  intro s
  rw [hp, hy]

end GlobalTheory.StairIdealAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.StairLine

variable {D : D7}

open GlobalTheory.SeeSaw

theorem incA_mul_mem_idV {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} (x : D.host.E) {t : AE D} (ht : t ∈ idV 𝔟 v) :
    incA D x * t ∈ idV (FractionalIdeal.spanSingleton _ x * 𝔟) v := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
    rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
    exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv
      (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ x) hb)
  | zero => rw [mul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem mem_idV_inv_mul {𝔟 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : D.host.E} (hx : x ≠ 0) (s : AE D) :
    s ∈ idV (FractionalIdeal.spanSingleton _ x⁻¹ * 𝔟) v ↔ incA D x * s ∈ idV 𝔟 v := by
  constructor
  · intro h
    have := incA_mul_mem_idV x h
    rwa [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ hx,
      FractionalIdeal.spanSingleton_one, one_mul] at this
  · intro h
    have := incA_mul_mem_idV x⁻¹ h
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ hx, map_one, one_mul] at this

theorem hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) :
    (d.aᴴ * B.gram * d.a) ⟨c - 1 - p.1, by omega⟩ = Pi.single p 1 ∧
      (d.aᴴ * B.gram * frameMat B A d.ι) = 0 := by
  refine ⟨?_, ?_⟩
  · have e := d.gram
    change d.aᴴ * B.gram * d.a = _ at e
    rw [e]
    funext q
    simp only [GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, Pi.single_apply, Fin.ext_iff]
    have := p.2; have := q.2
    by_cases hq : q.1 = p.1
    · rw [if_pos (by omega), if_neg (by omega), if_pos hq]
    · rw [if_neg (by omega), if_neg hq]
  · have e := d.perp
    change (frameMat B A d.ι)ᴴ * B.gram * d.a = 0 at e
    have hg : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq (B.frame j) (B.frame i)
    have := congrArg Matrix.conjTranspose e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hg,
      Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at this

theorem line_mem {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FI D) (v : GlobalTheory.FinPl.Pl D) (p : Fin c) (hp : 2 * p.1 + 1 ≠ c) (t : AE D) :
    (fun k => t * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ t ∈ idV (𝔟 p) v := by
  classical
  obtain ⟨hf1, hf2⟩ := hermOrthExt_gram_entry_eq_single_and_frame_gram_eq_zero d p hp
  generalize (⟨c - 1 - p.1, by omega⟩ : Fin c) = q at hf1
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin B.rank → D.host.E, φ = (d.aᴴ * B.gram) q := ⟨_, rfl⟩
  have hφa : ∀ u : Fin c → D.host.E, φ ⬝ᵥ (d.a *ᵥ u) = u p := by
    intro u
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* d.a = (d.aᴴ * B.gram * d.a) q := rfl
    rw [this, hf1]
    simp [Pi.single_apply, dotProduct]
  have hφM : ∀ y, φ ⬝ᵥ (frameMat B A d.ι *ᵥ y) = 0 := by
    intro y
    rw [Matrix.dotProduct_mulVec, hφ]
    have : (d.aᴴ * B.gram) q ᵥ* frameMat B A d.ι = (d.aᴴ * B.gram * frameMat B A d.ι) q := rfl
    rw [this, hf2]
    exact zero_dotProduct y
  have h3 : ∑ l, φ l * d.a l p = 1 := by
    have := congrFun hf1 p
    rw [Pi.single_eq_same, Matrix.mul_apply] at this
    rw [hφ]; exact this
  let Φ : (Fin B.rank → AE D) →+ AE D :=
    { toFun := fun z => ∑ l, incA D (φ l) * z l
      map_zero' := by simp
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib] }
  constructor
  · intro h
    have hle : latV B (d.lat Λ 𝔟) (· = v) ≤ (idV (𝔟 p) v).comap Φ := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨α, hα, hαv, a', ha', x, hx, rfl⟩
      rw [Set.mem_singleton_iff] at ha'
      subst ha'
      obtain ⟨y, -, u, hu, rfl⟩ := hx
      rw [SetLike.mem_coe, AddSubgroup.mem_comap]
      show ∑ l, incA D (φ l) * _ ∈ _
      simp only [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_sum]
      have : ∑ l, φ l * (frameMat B A d.ι *ᵥ y + d.a *ᵥ u) l = u p := by
        have h1 := hφa u
        have h2 := hφM y
        rw [← h1, ← add_zero (φ ⬝ᵥ (d.a *ᵥ u)), ← h2, ← dotProduct_add, add_comm]
        rfl
      rw [this]
      exact GlobalTheory.SeeSaw.IdVMul.gen_mem hα hαv (hu p)
    have h2 : Φ (fun k => t * incA D (d.a k p)) ∈ idV (𝔟 p) v := hle h
    have e : Φ (fun k => t * incA D (d.a k p)) = t := by
      show ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t
      calc ∑ l, incA D (φ l) * (t * incA D (d.a l p)) = t * incA D (∑ l, φ l * d.a l p) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [map_mul, mul_left_comm]
        _ = t := by rw [h3, map_one, mul_one]
    rwa [e] at h2
  · intro h
    induction h using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hs
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, d.a *ᵥ Pi.single p b,
        ⟨0, Λ.zero_mem, Pi.single p b, fun r => ?_, by simp⟩, ?_⟩
      · by_cases hr : r = p
        · subst hr; simpa using hb
        · rw [Pi.single_eq_of_ne hr]; exact (𝔟 r).zero_mem
      · funext k
        rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
        congr 1
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    | zero =>
      convert (latV B (d.lat Λ 𝔟) (· = v)).zero_mem using 1
      funext k; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      funext k; simp [add_mul]
    | neg x _ hx =>
      convert neg_mem hx using 1
      funext k; simp [neg_mul]


open GlobalTheory.ChiGrid in
theorem colMul_dJ_mem_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h v i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hx : ((-D.host.xi0) ^ (i.1 + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a = fun k => (incA D ((-D.host.xi0) ^ (i.1 + 1)) * a) *
      incA D ((G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) i)) := by
    funext k
    show a * incA D ((F.dJ ρ h).e k i) = _
    rw [he]
    show a * incA D ((-D.host.xi0) ^ (i.1 + 1) * _) = _
    rw [map_mul, ← mul_assoc, mul_comm a]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat _ _ _
  have hi := i.2
  rw [e1, e2, line_mem _ _ _ v _ (by simp only [Fin.val_castLE]; omega), mem_idV_inv_mul hx]
  simp only [stairId, Fin.val_castLE, Nat.add_sub_cancel]

end GlobalTheory.StairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hQ T L μ0 hL sc G W M hM F hF
  have t1 := _root_.GlobalTheory.AscFin.primAt_jac_std D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := _root_.GlobalTheory.ColsFB.cols_fb D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := _root_.GlobalTheory.RowLoc.latRow_at D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := _root_.GlobalTheory.RowInt.smul_mem_latO_at D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := _root_.GlobalTheory.BigLoc.latBig_at D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardLatticeOffS0
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.FinPlLoc (idem mem_idOff_iff idem_mul_self)
open GlobalTheory.AscFinWit (mem_latO_at idem_mem_latO mxAt_mul mxAt_mul')

noncomputable section

namespace GlobalTheory.AscFin.StdOff

theorem latO_le_negSp {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO (negSp S) T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp_le' {D : D7} (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P ≤ latO S T LS LT P := by
  unfold latO
  rw [AddSubgroup.closure_le]
  rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  rw [← neg_neg (Matrix.of _)]
  refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
  funext i j
  simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem depLat_iff_at {D : D7} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    {v : GlobalTheory.FinPl.Pl D} {W0 : Finset (Formalism.L2.DIV.Pl D.host.E)} (hoff : ∀ PP ∈ W0, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v)
    (H : AddSubgroup (WO S T)) {u : WO S T} (hu : MxAt (· = v) u) :
    (u ∈ latO (negSp S) T (LS : Set _) (LT : Set _) (fun _ => True) ∧ ∀ e : AE D, IsIdemSum e W0 → e • u ∈ H) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
  constructor
  · rintro ⟨h1, -⟩
    exact latO_negSp_le' S T _ _ _ ((mem_latO_at (S := negSp S) hu).1 h1)
  · intro h1
    refine ⟨(mem_latO_at (S := negSp S) hu).2 (latO_le_negSp S T _ _ _ h1), fun e he => ?_⟩
    have : e • u = 0 := Matrix.ext fun i j => (GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff h1 i j).1
    rw [this]
    exact zero_mem _

theorem pair_tmul_scale {D : D7} (α' : Af D.host.F) (d : D.host.F) (X : D.host.E) :
    pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) ⊗ₜ[D.host.F] X =
      pairA D.host.F 0 α' ⊗ₜ[D.host.F] ((d : D.host.E) * X) := by
  have e : (d : D.host.E) * X = d • X := rfl
  have e2 : pairA D.host.F 0 (α' * algebraMap D.host.F (Af D.host.F) d) = d • pairA D.host.F 0 α' := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = d • (0 : Ainf D.host.F)
      rw [smul_zero]
    · show α' * algebraMap D.host.F (Af D.host.F) d = d • α'
      rw [Algebra.smul_def, mul_comm]
  rw [e, e2, ← TensorProduct.smul_tmul']
  exact ((TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 α')).map_smul d X).symm

def gen {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin U.rank → D.host.E) :
    WO S U :=
  Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)

theorem gen_zero {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) :
    gen S U α a s 0 = 0 := by
  ext i j
  rw [gen, Matrix.of_apply, Matrix.zero_apply, Pi.zero_apply, mul_zero, zero_mul, TensorProduct.tmul_zero]

theorem gen_add {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (t t' : Fin U.rank → D.host.E) : gen S U α a s (t + t') = gen S U α a s t + gen S U α a s t' := by
  ext i j
  rw [Matrix.add_apply, gen, gen, gen, Matrix.of_apply, Matrix.of_apply, Matrix.of_apply, Pi.add_apply, mul_add, add_mul,
    TensorProduct.tmul_add]

theorem gen_smul {D : D7} (S U : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E)
    (c : 𝓞 D.host.E) (t : Fin U.rank → D.host.E) : gen S U α a s (c • t) = gen S U α (a * (c : D.host.E)) s t := by
  ext i j
  have hc : c • t i = (c : D.host.E) * t i := Algebra.smul_def c (t i)
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, hc, ← mul_assoc]

theorem gen_smulE {D : D7} (S U : HSp D) (α : Af D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) : gen S U α a s (b • t) = gen S U α (a * b) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc]

theorem gen_scale {D : D7} (S U : HSp D) (α : Af D.host.F) (d : D.host.F) (a b : D.host.E) (s : Fin S.rank → D.host.E)
    (t : Fin U.rank → D.host.E) :
    gen S U (α * algebraMap D.host.F (Af D.host.F) d) a s (b • t) = gen S U α (a * ((d : D.host.E) * b)) s t := by
  ext i j
  rw [gen, gen, Matrix.of_apply, Matrix.of_apply, pair_tmul_scale, Pi.smul_apply, smul_eq_mul]
  congr 1
  ring

theorem latO_idLat_at {D : D7} (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) (d : D.host.F) (hdI : (d : D.host.E) ∈ I)
    (hdI' : ∀ x ∈ I, ∃ y : 𝓞 D.host.E, (y : D.host.E) = (d : D.host.E) * x)
    (hsc : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) →
      ∃ α' ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α' = 0) ∧ α = α' * algebraMap D.host.F (Af D.host.F) d) :
    latO S U LS (idLat I LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  have hAA : ∀ a ∈ D.host.AA, ∀ c : 𝓞 D.host.E, a * (c : D.host.E) ∈ D.host.AA := fun a ha c => by
    have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) c ha
    rwa [Algebra.smul_def, mul_comm] at this
  have hgen : ∀ α ∈ intAf D.host.F, (∀ w, ¬ w = v → evalV D.host.F w α = 0) → ∀ a ∈ D.host.AA, ∀ s ∈ LS, ∀ t ∈ LU,
      gen S U α a s t ∈ latO S U LS (LU : Set _) (· = v) := fun α hα hP a ha s hs t ht =>
    AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
  refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ((AddSubgroup.closure_le _).2 ?_)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (LU : Set _) (· = v) : Set (WO S U))
    rw [SetLike.mem_coe]
    induction ht using Submodule.span_induction generalizing a with
    | mem z hz =>
      obtain ⟨s', hs', y, hy, rfl⟩ := hz
      obtain ⟨yy, hyy⟩ := hdI' s' hs'
      rw [gen_scale, ← hyy]
      exact hgen α' hα' hP' _ (hAA a ha yy) s hs y hy
    | zero =>
      rw [gen_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [gen_add]
      exact add_mem (hx a ha) (hy a ha)
    | smul c x _ hx =>
      rw [gen_smul]
      exact hx _ (hAA a ha c)
  · rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    obtain ⟨α', hα', hP', rfl⟩ := hsc α hα hP
    show gen S U (α' * algebraMap D.host.F (Af D.host.F) d) a s t ∈ (latO S U LS (idLat I LU : Set _) (· = v) : Set (WO S U))
    have e := gen_scale S U α' d a 1 s t
    rw [one_smul, mul_one, mul_comm a] at e
    rw [SetLike.mem_coe, e, mul_comm (d : D.host.E) a, ← gen_smulE]
    exact AddSubgroup.subset_closure ⟨α', hα', hP', a, ha, s, hs, _, Submodule.subset_span ⟨_, hdI, t, ht, rfl⟩, rfl⟩

theorem latO_shiftId {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (v : GlobalTheory.FinPl.Pl D)
    (hv : v ∉ G.pl.S0) (S U : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LU : GlobalTheory.FinPl.Lat U) :
    latO S U LS (idLat (shiftId G) LU : Set _) (· = v) = latO S U LS (LU : Set _) (· = v) := by
  obtain ⟨d, hdv, hdI, hdI'⟩ := _root_.GlobalTheory.ShiftUnit.exists_d G v hv
  exact latO_idLat_at S U LS LU _ v (d : D.host.F) hdI hdI' (GlobalTheory.T.integralFiniteAdele_supported_div_prime_to_place D v d hdv)

end GlobalTheory.AscFin.StdOff

open GlobalTheory.AscFin.StdOff GlobalTheory.FinZeta.VacOff

theorem GlobalTheory.AscFin.stdAt_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0,
    StdAt (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  classical
  intro D _ T L _ _ sc G W _ _ F _ ρ h v hv
  have hoff : ∀ PP ∈ G.pl.W0, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v := fun PP hPP e => by
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hPP
    exact hv (by rw [← e, G.pl.under_w hu]; exact hu)
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun ξ hξ => ?_⟩
  · have hu := mxAt_mul' ha (F.dB ρ h).pX
    exact depLat_iff_at hoff _ hu
  · refine ⟨idem D (· = v) • a, fun i j => (mem_idOff_iff _ _).2 (by
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub, ← mul_assoc, idem_mul_self, sub_self]), ?_⟩
    rw [HypDec.extX_apply, Matrix.smul_mul]
    exact idem_mem_latO (latO_negSp_le' _ _ _ _ _ ha.1)
  · have hu := mxAt_mul' (mxAt_mul (F.dJ ρ h).jX hξ) (F.dB ρ h).p0
    show (F.dB ρ h).ext0 _ ((F.dJ ρ h).incX _ ξ) ∈ latBig G (2 * ρ + 1) ↔ _
    exact (mem_latO_at hu).trans (by rw [latO_shiftId G v hv]; exact Iff.rfl)

end
end

