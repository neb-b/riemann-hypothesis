module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetEquationMulRightCongruentOneModDepthIdealAl
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

noncomputable section
namespace GlobalTheory.CosDualStep

variable {D : D7}

theorem actO_one_left (S T : HSp D) (h : GA D T) (Z : WO S T) :
    actO S T 1 h Z = HMul.hMul (Formalism.L2.Theta.mt T h) (Z : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
  unfold actO
  simp [Formalism.L2.Theta.mt]

theorem infPart_idemSum {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : infPart D e = 0 := by
  classical
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  subst hsum
  induction P using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

def finLift {m n : ℕ} (c : Matrix (Fin m) (Fin n) D.host.E) : Mx D m n :=
  Matrix.of fun a b => pairA D.host.F 0 1 ⊗ₜ[D.host.F] c a b

theorem smul_map_incA {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {m n : ℕ}
    (c : Matrix (Fin m) (Fin n) D.host.E) :
    e • c.map (incA D) = e • finLift c := by
  ext a b
  simp only [finLift, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [map_mul, map_mul, infPart_idemSum he, zero_mul, zero_mul]
  · rw [map_mul, map_mul, GlobalTheory.LatVac.finPart_pair, GlobalTheory.LatVac.finPart_incA]

theorem homLat_mul {a b c : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ homLat Λ Λ'' := by
  show ∀ v ∈ Λ, (x * y) *ᵥ v ∈ Λ''
  intro v hv
  rw [← Matrix.mulVec_mulVec]
  exact hx _ (hy v hv)

theorem smul_homLat_mul {a b c : ℕ} {𝔪 : Ideal (𝓞 D.host.E)} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin c → D.host.E)}
    {x : Matrix (Fin c) (Fin b) D.host.E} {y : Matrix (Fin b) (Fin a) D.host.E}
    (hx : x ∈ 𝔪 • homLat Λ' Λ'') (hy : y ∈ homLat Λ Λ') : x * y ∈ 𝔪 • homLat Λ Λ'' := by
  refine Submodule.smul_induction_on hx (fun r hr n hn => ?_) (fun p q hp hq => ?_)
  · rw [Matrix.smul_mul]
    exact Submodule.smul_mem_smul hr (homLat_mul hn hy)
  · rw [Matrix.add_mul]
    exact Submodule.add_mem _ hp hq

theorem hatMx_mul {a b c : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin b) D.host.E)}
    {N : Submodule (𝓞 D.host.E) (Matrix (Fin c) (Fin a) D.host.E)} (y : Matrix (Fin b) (Fin a) D.host.E)
    (hMN : ∀ x ∈ M, x * y ∈ N) {u : Mx D c b} (hu : u ∈ hatMx M) : u * y.map (incA D) ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, x * y, hMN x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply]
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show _ * (Algebra.TensorProduct.includeRight (y k j)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add p q _ _ hp hq => rw [Matrix.add_mul]; exact add_mem hp hq
  | neg p _ hp => rw [Matrix.neg_mul]; exact neg_mem hp

theorem smul_one_sub {n : ℕ} (e : AE D) (A A' C : Matrix (Fin n) (Fin n) (AE D)) (h : e • A = e • C) :
    e • (1 - (A' - C)) = e • (1 + A - A') := by
  rw [smul_sub, smul_sub, smul_sub, smul_add, h]
  abel

theorem core_step {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) {n n' : ℕ}
    (x₀ : Matrix (Fin n) (Fin n') D.host.E) (y₀ : Matrix (Fin n') (Fin n) D.host.E)
    (mg : Matrix (Fin n) (Fin n) (AE D)) (u u' : Matrix (Fin n) (Fin n') (AE D))
    (heq : e • (x₀.map (incA D) - u) = HMul.hMul mg (e • (x₀.map (incA D) - u'))) :
    e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
      HMul.hMul mg (e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul u' (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1)))) := by
  have hxy : x₀ * y₀ = 1 + (x₀ * y₀ - 1) := by abel
  have hXY : HMul.hMul (x₀.map (incA D)) (y₀.map (incA D)) = (1 : Matrix (Fin n) (Fin n) (AE D)) + (x₀ * y₀ - 1).map (incA D) := by
    rw [← Matrix.map_mul]
    conv_lhs => rw [hxy]
    rw [Matrix.map_add (incA D) (fun a b => RingHom.map_add _ a b),
      Matrix.map_one (incA D) (RingHom.map_zero _) (RingHom.map_one _)]
  have hce := smul_map_incA he (x₀ * y₀ - 1)
  have key : ∀ v : Matrix (Fin n) (Fin n') (AE D),
      e • ((1 : Matrix (Fin n) (Fin n) (AE D)) - (HMul.hMul v (y₀.map (incA D)) -
        finLift (x₀ * y₀ - 1))) =
        HMul.hMul (e • (x₀.map (incA D) - v)) (y₀.map (incA D)) := by
    intro v
    rw [Matrix.smul_mul, Matrix.sub_mul, hXY]
    exact smul_one_sub e _ _ _ hce
  rw [key u, key u', heq, Matrix.mul_assoc]

theorem coset_equation_mul_right_congruent_one_mod_depthIdeal : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ x₀, IsOntoMod G i x₀ → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ u ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))), ∀ u' ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.latS (.core i)) (G.latT (.core i))),
    e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u) =
      actO (G.pS (.core i)) (G.pT (.core i)) 1 g (e • ((x₀.map (incA D) : WO (G.pS (.core i)) (G.pT (.core i))) - u')) →
    ∃ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∃ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
      e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) := by
  intro D _ T L μ0 _ sc G W M _ i _ x₀ hx₀ e he g u hu u' hu' heq
  obtain ⟨-, y₀, hy₀, hc⟩ := hx₀
  have h1 : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by simp
  have hcf : finLift (x₀ * y₀ - 1) ∈
      hatMx (G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i))) :=
    AddSubgroup.subset_closure ⟨1, h1, x₀ * y₀ - 1, hc, rfl⟩
  have hmul : ∀ x ∈ G.modul • homLat (G.latS (.core i)) (G.latT (.core i)),
      x * y₀ ∈ G.modul • homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun x hx => smul_homLat_mul hx hy₀
  refine ⟨_, sub_mem (hatMx_mul y₀ hmul hu) hcf, _, sub_mem (hatMx_mul y₀ hmul hu') hcf, ?_⟩
  rw [actO_one_left] at heq ⊢
  exact core_step he x₀ y₀ _ u u' heq

end GlobalTheory.CosDualStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso


open GlobalTheory.AscFin.BesIso in
theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelSupportedClassSubsetSplitLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq_halves (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem heisO_add_fix {f : WO S T → ℂ} {w w' : WO S T} (h : heisO ψ S T w f = f) (h' : heisO ψ S T w' f = f)
    (hc : ψ (symplOH S T w w') = 1) : heisO ψ S T (w + w') f = f := by
  have e := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) w w' f
  rw [h', h, hc, one_smul] at e
  exact e.symm

theorem psi_four {t : AF D.host.F} (h : ψ (t + t) = 1) : ψ ((t + t) + (t + t)) = 1 := by
  rw [AddChar.map_add_eq_mul, h, one_mul]

theorem psi_symplO_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplO S T x (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h ⊢
  rw [two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

theorem psi_symplOH_two {x y : WO S T} (h : ψ (symplO S T x y) = 1) : ψ (symplOH S T (2 • x) (2 • y)) = 1 := by
  rw [symplO_eq_halves] at h
  rw [two_nsmul, two_nsmul, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  exact psi_four h

variable {m n k : ℕ} {e : AE D}

theorem isHalf_add' {x y : Mx D m n} (hx : IsHalf e x) (hy : IsHalf e y) : IsHalf e (x + y) := fun i j => by
  rw [Matrix.add_apply, mul_add, hx i j, hy i j]

theorem isHalf_mul_right' {x : Mx D m n} (hx : IsHalf e x) (M : Mx D n k) : IsHalf e (x * M) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hx i]

theorem isHalf_mul_left' (M : Mx D k m) {x : Mx D m n} (hx : IsHalf e x) : IsHalf e (M * x) := fun i j => by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hx l j]

theorem symplOH_half (he : e * cA D e = 0) {x y : WO S T} (hx : IsHalf e x) (hy : IsHalf e y) :
    symplOH S T x y = 0 := by
  have h0 : hO S T x y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    rw [← hx d a, ← hy c b, map_mul]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * x d a) * he
  unfold symplOH symplO
  rw [h0, mul_zero, map_zero, mul_zero]

end GlobalTheory.AscFin.SplitVac

namespace GlobalTheory.AscFin.SplitVac

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} {dV : HypDec V V₀ ρ} {dW : HypDec W W₀ σ}
  {p : Pieces V₀ W W₀ ρ σ} {x : Mx D W.rank ρ} {y : Mx D V₀.rank σ} {Γ : AddSubgroup (WO V W)} {Φ : WO V W → ℂ}

theorem fix_two (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (u : WO V W) (hu : u ∈ Γ) :
    heisO ψ V W (2 • u) Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have e1 : 2 • (dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w)) =
      dV.extX W (2 • a) + (dV.extY W (2 • a') + (dV.ext0 W (dW.incX V₀ (2 • ξ)) +
        (dV.ext0 W (dW.incY V₀ (2 • η)) + dV.ext0 W (dW.inc0 V₀ (2 • w))))) := by
    simp only [map_nsmul, map_add (f := _), nsmul_add]
    abel
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  have fX : heisO ψ V W (dV.extX W (2 • a)) Φ = Φ := hA1 _ (nsmul_mem ha 2)
  have fY : heisO ψ V W (dV.extY W (2 • a')) Φ = Φ := by
    rw [hA2 _ (nsmul_mem ha' 2), map_nsmul, psi_symplO_two hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ (2 • ξ))) Φ = Φ := by
    rw [hB1 _ (nsmul_mem hξ 2), map_nsmul, psi_symplO_two hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ (2 • η))) Φ = Φ := hB2 _ (nsmul_mem hη 2)
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ (2 • w))) Φ = Φ := by
    have h := hvac.1 _ (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
    rw [AddMonoidHom.comp_apply, ← map_nsmul, ← map_nsmul] at h
    exact h
  have cAB : ψ (symplO V W (dV.extX W a) (dV.extY W a')) = 1 := (hp.dualA a (hp.a₁.fin a ha)).1 ha a' ha'
  have cXY : ψ (symplO V₀ W (dW.incX V₀ ξ) (dW.incY V₀ η)) = 1 := (hp.dualB ξ (hp.b₁.fin ξ hξ)).1 hξ η hη
  refine heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR ?_) ?_) ?_) ?_
  · rw [HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_inclDual_inclAnisotropic, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic,
      HypDec.wittDecomp_sympl_inclIsotropic_inclAnisotropic, add_zero, map_nsmul, map_nsmul]
    exact psi_symplOH_two cXY
  · simp only [GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.wittDecomp_sympl_extDual_extAnisotropic, add_zero, AddChar.map_zero_eq_one]
  · rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
      HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero, add_zero, add_zero,
      map_nsmul, map_nsmul]
    exact psi_symplOH_two cAB

theorem fix_half (hs : Splits dV dW p x y ψ Γ) (hΦ : Φ ∈ cls dV dW p x y ψ) (e : AE D) (he : IsSplitIdem D e) (u : WO V W)
    (hu : u ∈ Γ) (hh : IsHalf e u) : heisO ψ V W u Φ = Φ := by
  obtain ⟨hθ, hA1, hA2, hB1, hB2, hvac⟩ := hΦ
  obtain ⟨a, ha, a', ha', ξ, hξ, η, hη, w, hw, rfl, hx', hy'⟩ := hs.comp u hu
  have he0 : e * cA D e = 0 := he.2.1
  have e1 : dV.extX W a + dV.extY W a' + dV.ext0 W (dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w) =
      dV.extX W a + (dV.extY W a' + (dV.ext0 W (dW.incX V₀ ξ) +
      (dV.ext0 W (dW.incY V₀ η) + dV.ext0 W (dW.inc0 V₀ w)))) := by
    rw [map_add (f := _), map_add (f := _)]
    abel
  obtain ⟨z, hz⟩ : ∃ z, dW.incX V₀ ξ + dW.incY V₀ η + dW.inc0 V₀ w = z := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, dV.extX W a + dV.extY W a' + dV.ext0 W z = U := ⟨_, rfl⟩
  rw [hz, hU] at hh
  have hUa : U * dV.jX = a := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pY_jX, HypDec.p0_jX, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hUa' : U * dV.jY = a' := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_jY, HypDec.pY_jY, HypDec.p0_jY, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hUz : U * dV.j0 = z := by
    rw [← hU]
    simp only [HypDec.extX_apply, HypDec.extY_apply, HypDec.matrixExtendByZero_apply, Matrix.add_mul, Matrix.mul_assoc,
      HypDec.pX_j0, HypDec.pY_j0, HypDec.p0_j0, Matrix.mul_one, Matrix.mul_zero, add_zero, zero_add]
  have hzξ : dW.pX * z = ξ := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pX_jX, HypDec.pX_jY, HypDec.pX_j0, Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hzη : dW.pY * z = η := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.pY_jX, HypDec.pY_jY, HypDec.pY_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzw : dW.p0 * z = w := by
    rw [← hz]
    simp only [HypDec.incX_apply, HypDec.incY_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_add, ← Matrix.mul_assoc,
      HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add]
  have hzh : IsHalf e z := hUz ▸ isHalf_mul_right' hh _
  have hX : IsHalf e (dV.extX W a) := by
    rw [HypDec.extX_apply, ← hUa]; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hY : IsHalf e (dV.extY W a') := by
    rw [HypDec.extY_apply, ← hUa']; exact isHalf_mul_right' (isHalf_mul_right' hh _) _
  have hP : IsHalf e (dV.ext0 W (dW.incX V₀ ξ)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, ← hzξ]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hQ : IsHalf e (dV.ext0 W (dW.incY V₀ η)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, ← hzη]
    exact isHalf_mul_right' (isHalf_mul_left' _ (isHalf_mul_left' _ hzh)) _
  have hR : IsHalf e (dV.ext0 W (dW.inc0 V₀ w)) := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, ← hzw]
    exact isHalf_mul_right' (isHalf_mul_left' dW.j0 (isHalf_mul_left' dW.p0 hzh)) dV.p0
  have fX : heisO ψ V W (dV.extX W a) Φ = Φ := hA1 _ ha
  have fY : heisO ψ V W (dV.extY W a') Φ = Φ := by rw [hA2 _ ha', hx', one_smul]
  have fP : heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) Φ = Φ := by rw [hB1 _ hξ, hy', one_smul]
  have fQ : heisO ψ V W (dV.ext0 W (dW.incY V₀ η)) Φ = Φ := hB2 _ hη
  have fR : heisO ψ V W (dV.ext0 W (dW.inc0 V₀ w)) Φ = Φ := by
    have h := hvac.2 e he ((dV.ext0 W).comp (dW.inc0 V₀) w) (AddSubgroup.mem_map_of_mem ((dV.ext0 W).comp (dW.inc0 V₀)) hw)
      (by rw [AddMonoidHom.comp_apply]; exact hR)
    rw [AddMonoidHom.comp_apply] at h
    exact h
  have z0 : ∀ {s t : WO V W}, IsHalf e s → IsHalf e t → ψ (symplOH V W s t) = 1 := fun hs ht => by
    rw [symplOH_half he0 hs ht, AddChar.map_zero_eq_one]
  show heisO ψ V W _ Φ = Φ
  rw [e1]
  exact heisO_add_fix fX (heisO_add_fix fY (heisO_add_fix fP (heisO_add_fix fQ fR (z0 hQ hR))
    (z0 hP (isHalf_add' hQ hR))) (z0 hY (isHalf_add' hP (isHalf_add' hQ hR))))
    (z0 hX (isHalf_add' hY (isHalf_add' hP (isHalf_add' hQ hR))))

theorem cls_vac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ)
    (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ)
    (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp hs _ hΦ =>
    ⟨hΦ.1, fun u hu => fix_two hp hs hΦ u hu, fun e he u hu hh => fix_half hs hΦ e he u hu hh⟩

end GlobalTheory.AscFin.SplitVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLattice
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac.BlocksPreserved

theorem blocks_keep {R : Type} [CommRing R] {d : ℕ} (S : AddSubgroup (Fin d → R))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R)
    (h : ∀ z : Fin d ⊕ Fin d → R, z ∘ Sum.inl ∈ S → z ∘ Sum.inr ∈ S →
      (M *ᵥ z) ∘ Sum.inl ∈ S ∧ (M *ᵥ z) ∘ Sum.inr ∈ S) :
    (∀ z ∈ S, M.toBlocks₁₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₁₂ *ᵥ z ∈ S) ∧
    (∀ z ∈ S, M.toBlocks₂₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₂₂ *ᵥ z ∈ S) := by
  have eL : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inl = z := fun z => rfl
  have eR : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inr = 0 := fun z => rfl
  have fL : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inl = 0 := fun z => rfl
  have fR : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inr = z := fun z => rfl
  have a11 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inl = M.toBlocks₁₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  have a21 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inr = M.toBlocks₂₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]
  have a12 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inl = M.toBlocks₁₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂]
  have a22 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).1
    rwa [a11] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).1
    rwa [a12] at this
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).2
    rwa [a21] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).2
    rwa [a22] at this

end GlobalTheory.DblVac.BlocksPreserved

namespace GlobalTheory.DblVac

theorem KD_blocks_keep : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl (F := F)), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ σ d W v g hg
  have h1 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).1)
  have h2 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g⁻¹)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).2)
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

end GlobalTheory.DblVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegralAdeleMulVecMemLatticeClosureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_integral_adele_mulVec_mem_lattice_closure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (L : Submodule (𝓞 E) (Fin n → E)), L.IsFullLattice E →
    ∃ S₁ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ w ∉ S₁, ∀ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) a →
      GlobalTheory.AdelicU.evFin F w a ∈ w.adicCompletionIntegers F → ∀ y ∈ L,
      a • (M *ᵥ fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y i)) ∈
        AddSubgroup.closure {z | ∃ b : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F w) b ∧
          GlobalTheory.AdelicU.evFin F w b ∈ w.adicCompletionIntegers F ∧
          ∃ y' ∈ L, z = b • fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (y' i)} := by
  intro F E _ _ _ _ _ n M L hL
  first
  | exact GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure F E n M L hL
  | exact GlobalTheory.AdelicLatticeIntegral.exists_finset_smul_mulVec_mem_closure F E n M L hL.toIsLattice
end

