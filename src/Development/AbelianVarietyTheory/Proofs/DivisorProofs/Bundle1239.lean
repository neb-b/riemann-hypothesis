module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdPowOfZeros
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.HyperplaneFactor

theorem eval_lin {K : Type} [Field K] {N : ℕ} (x : Fin 1 × Fin N → K) (y : Fin N → K) :
    eval x (lin y) = ∑ j, x (0, j) * y j := by
  simp [lin]

theorem coeff_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) (j : Fin N) :
    AddMonoidAlgebra.coeff (lin y) (Finsupp.single ((0 : Fin 1), j) 1) = y j := by
  classical
  rw [lin, coeff_sum]
  simp only [mul_comm (X _) (C _), coeff_C_mul, coeff_X', Finsupp.single_left_inj (one_ne_zero' ℕ)]
  simp

theorem isHomogeneous_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X K _).mul (isHomogeneous_C _ _)

theorem irreducible_lin {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : Irreducible (lin y) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have h0 : lin y ≠ 0 := fun h => hj (by
    have := coeff_lin y j
    simp only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
    exact this.symm)
  refine irreducible_of_totalDegree_eq_one ((isHomogeneous_lin y).totalDegree h0) fun x hx => ?_
  have hd := hx (Finsupp.single (0, j) 1)
  rw [coeff_lin] at hd
  exact isUnit_of_dvd_unit hd (IsUnit.mk0 _ hj)

theorem exists_dvd_pow_of_zeros {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {a b : MvPolynomial (Fin 1 × Fin N) K}
    (h : ∀ x, eval x a = 0 → eval x b = 0) : ∃ n : ℕ, a ∣ b ^ n := by
  have hb : b ∈ (Ideal.span {a}).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have h1 := hx a (Ideal.subset_span rfl)
    have e : ∀ p : MvPolynomial (Fin 1 × Fin N) K, aeval x p = eval x p := fun p =>
      DFunLike.congr_fun (coe_aeval_eq_eval x) p
    rw [e] at h1
    change aeval x b = 0
    rw [e]
    exact h x h1
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem eq_C_mul_prod_lin : ∀ (K : Type) [Field K] [IsAlgClosed K] (N δ m : ℕ) (g : MvPolynomial (Fin 1 × Fin N) K)
    (y : Fin m → Fin N → K), g.IsHomogeneous δ → NoSquare g → (∀ q, y q ≠ 0) →
    (∀ q q' (c : K), y q' = c • y q → q = q') →
    (∀ ξ : Fin N → K, eval (fun p => ξ p.2) g = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0) →
    m = δ ∧ ∃ c : K, c ≠ 0 ∧ g = C c * ∏ q, lin (y q) := by
  intro K _ _ N δ m g y hg hns hy hinj hz
  classical
  have hz' : ∀ x : Fin 1 × Fin N → K, eval x g = 0 ↔ ∃ q, eval x (lin (y q)) = 0 := by
    intro x
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz fun j => x (0, j)
    simp only [e] at h1
    simpa only [eval_lin] using h1
  have irr : ∀ q, Irreducible (lin (y q)) := fun q => irreducible_lin (hy q)
  have dvdg : ∀ q, lin (y q) ∣ g := fun q => by
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := lin (y q)) (b := g) fun x hx => (hz' x).2 ⟨q, hx⟩
    exact (irr q).prime.dvd_of_dvd_pow hn
  have nondvd : ∀ q q', q ≠ q' → ¬ lin (y q) ∣ lin (y q') := by
    intro q q' hne hd
    obtain ⟨a, ha⟩ := (irr q).associated_of_dvd (irr q') hd
    obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
    rw [ht, mul_comm] at ha
    refine hne (hinj q q' t (funext fun j => ?_))
    have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single ((0 : Fin 1), j) 1)) ha
    rw [coeff_C_mul, coeff_lin, coeff_lin] at h1
    simpa using h1.symm
  have Pdvd : (∏ q, lin (y q)) ∣ g := Finset.prod_dvd_of_isRelPrime
    (fun q _ q' _ hne => (irr q).isRelPrime_iff_not_dvd.2 (nondvd q q' hne)) fun q _ => dvdg q
  obtain ⟨h, hh⟩ := Pdvd
  have h0 : h ≠ 0 := fun e => hns.1 (by rw [hh, e, mul_zero])
  have hu : IsUnit h := by
    by_contra hu
    obtain ⟨p, pirr, pd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := g) (b := ∏ q, lin (y q)) fun x hx => by
      obtain ⟨q, hq⟩ := (hz' x).1 hx
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hq
    have pg : p ∣ g := hh ▸ pd.mul_left _
    obtain ⟨q, -, hq⟩ := (Prime.exists_mem_finset_dvd pirr.prime (pirr.prime.dvd_of_dvd_pow (pg.trans hn)))
    have hl : lin (y q) ∣ p := ((pirr.associated_of_dvd (irr q) hq).symm).dvd
    refine hns.2 (y q) (hy q) ?_
    rw [hh, pow_two]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (hl.trans pd)
  obtain ⟨c, hc, hcC⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hgC : g = C c * ∏ q, lin (y q) := by rw [hh, hcC, mul_comm]
  have hP : (∏ q, lin (y q)).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun q => lin (y q)) (fun _ => 1) fun q _ => isHomogeneous_lin (y q)
  have hgm : g.IsHomogeneous m := by
    rw [hgC]
    simpa using (isHomogeneous_C (Fin 1 × Fin N) c).mul hP
  exact ⟨(hgm.totalDegree hns.1).symm.trans (hg.totalDegree hns.1), c, hc.ne_zero, hgC⟩

end GlobalTheory.HSChoice.HyperplaneFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RegSeqKer

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (s : L.Sec)

theorem map_cutHom {l m : ℤ} (h : l + 1 = m) (h' : -1 + m = l) :
    Twist.map (lbZPow L m) (GlobalTheory.cutHom F hL s) =
      (twistZAddIso F hL h').hom ≫ mulSecOfEq F (zofSec s) h :=
  zhom_ext fun V u i => by
    change _ = zcoord ((mulSecOfEq F (zofSec s) h).app V ((twistZAddIso F hL h').hom.app V u)) i
    rw [zcoord_map_app, cutHom_app F hL s i inf_le_right, zcoord_mulSecOfEq_app, zcoord_twistZAddIso_hom_app,
      zchartEquiv_apply, zfun_zofSec]

theorem mul_comp_π {l m : ℤ} (h : l + 1 = m) :
    mulSecOfEq F (zofSec s) h ≫ Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s) = 0 := by
  have h' : -1 + m = l := by omega
  rw [← cancel_epi (twistZAddIso F hL h').hom, ← Category.assoc, ← map_cutHom hL F s h h', Limits.comp_zero]
  exact ((cutComplex F hL s).map (twistFunctor (lbZPow L m))).zero

def twistComplex {l m : ℤ} (h : l + 1 = m) : ShortComplex Y.Modules :=
  .mk (mulSecOfEq F (zofSec s) h) (Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s)) (mul_comp_π hL F s h)

theorem shortExact_twistComplex [Mono (GlobalTheory.cutHom F hL s)] {l m : ℤ} (h : l + 1 = m) :
    (twistComplex hL F s h).ShortExact := by
  have h' : -1 + m = l := by omega
  have hS : (cutComplex F hL s).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (cutHom F hL s))
      (inferInstanceAs (Mono (cutHom F hL s))) (epi_cutπ F hL s)
  refine ShortComplex.shortExact_of_iso ?_
    (Twist.shortExact_map (isLB_lbZPow hL m) hS)
  refine ShortComplex.isoMk (twistZAddIso F hL h') (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (map_cutHom hL F s h h').symm.trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem vanishFrom_cut [Mono (GlobalTheory.cutHom F hL s)] {j₀ : ℤ} (hv : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL s) (j₀ + 1) := fun j hj q hq =>
  cohOn.subsingleton₃ (shortExact_twistComplex hL F s (l := j - 1) (m := j) (by omega)) ⊤ q
    (hv j (by omega) q hq) (hv (j - 1) (by omega) (q + 1) (by omega))

theorem exists_global (n : ℕ) : ∀ (t : Fin n → L.Sec) (F : Y.Modules) (j₀ l : ℤ), RegSeq hL F (List.ofFn t) →
    VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤),
    (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)),
      (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f =
        ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app W (m i)) →
    ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app ⊤ (m i) := by
  induction n with
  | zero =>
    intro t F j₀ l _ _ _ f hf
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    obtain ⟨W, hW, m, hm⟩ := hf x
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hW, hm, map_zero]
  | succ n ih =>
    intro t F j₀ l hr hv hj f hf
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have nat : ∀ (a : L.Sec) (W : Y.Opens) (u : Γ(GlobalTheory.twistZ F L l, W)),
        (Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W ((mulSecOfEq F (zofSec a) rfl).app W u) =
          (mulSecOfEq (cut F hL (t 0)) (zofSec a) rfl).app W
            ((Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W u) := fun a W u => by
      apply zsec_ext fun i => ?_
      rw [zcoord_map_app, zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, zcoord_map_app,
        Scheme.Modules.Hom.app_smul]
    have hS := shortExact_twistComplex hL F (t 0) (l := l) rfl
    have := hS.mono_f
    have hex : ∀ W : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) (rfl : l + 1 = l + 1)).app W)
        ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W) := exact_app_of_exact_of_mono hS.exact
    obtain ⟨m', hm'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l hr (vanishFrom_cut hL F (t 0) hv)
      (by push_cast at hj; omega) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app ⊤ f) fun y => by
        obtain ⟨W, hW, m, hm⟩ := hf y
        refine ⟨W, hW, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W (m i.succ), ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← app_res, hm, Fin.sum_univ_succ, map_add (f := _), (hex W).apply_apply_eq_zero, zero_add, map_sum]
        exact Finset.sum_congr rfl fun i _ => nat _ _ _
    have hlift : ∀ i, ∃ u : Γ(GlobalTheory.twistZ F L l, ⊤),
        (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app ⊤ u = m' i := fun i => by
      have hi := i.pos
      exact cohOn.app_surjective (shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)) ⊤
        (hv (l - 1) (by push_cast at hj; omega) 1 one_pos) (m' i)
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex ⊤ (f - ∑ i, (mulSecOfEq F (zofSec (t i.succ)) rfl).app ⊤ (u i))).1 (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hm', map_sum, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [nat, hu])
    refine ⟨Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqKer

theorem GlobalTheory.HSCore.exists_global_of_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k (X := Y)) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) :=
  fun _ _ _ _ _ _ hL n t F _ j₀ l => RegSeqKer.exists_global hL n t F j₀ l
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIndefiniteUnitaryLieAlgAddISmulEq
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem jm_conjTranspose (p q : ℕ) : (Formalism.BasicNotions.TH.Jm p q)ᴴ = Formalism.BasicNotions.TH.Jm p q := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_conjTranspose]
  simp

theorem jm_mul_self (p q : ℕ) : Formalism.BasicNotions.TH.Jm p q * Formalism.BasicNotions.TH.Jm p q = 1 := by
  unfold Formalism.BasicNotions.TH.Jm Formalism.UG.Jpq
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

theorem upq_span (p q : ℕ) (Z : Mat p q) : ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  obtain ⟨J, hJ⟩ : ∃ J, J = Formalism.BasicNotions.TH.Jm p q := ⟨_, rfl⟩
  have hJh : Jᴴ = J := hJ ▸ jm_conjTranspose p q
  have hJJ : J * J = 1 := hJ ▸ jm_mul_self p q
  refine ⟨(1/2 : ℂ) • (Z - J * Zᴴ * J), ?_, (-(Complex.I / 2)) • (Z + J * Zᴴ * J), ?_, ?_⟩
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp [star_div₀]
    rw [this]
    module
  · show _ = _
    rw [← hJ]
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hJh, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc, hJJ, Matrix.mul_one]
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul]
    have : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [star_div₀]; ring
    rw [this]
    module
  · rw [smul_smul]
    have : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, mul_div_assoc', Complex.I_mul_I]; ring
    rw [this]
    module

end GlobalTheory.HoweD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertBridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Chart (σ : E →ₐ[F] E) (B : Base F E) {a a' : ℕ} (G : Geo σ a a') (v : Pl (F := F)) {L : Type} [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L) (JS : GL (Fin a') L)
    (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
    (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (AE F E))
    (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
    (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J) : Prop :=
  Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
  JS ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) ∧ JT ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) ∧
  (∀ i j, σL ((JS : Matrix (Fin a') (Fin a') L) i j) = (JS : Matrix (Fin a') (Fin a') L) j i) ∧
  (∀ i j, σL ((JT : Matrix (Fin (a + a')) (Fin (a + a')) L) i j) = (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) j i) ∧
  (Valued.v δ = 1 ∧ σL δ = -δ) ∧
  (∀ z ∈ Formalism.UG.intL L, σL z = z → ψL z = 1) ∧
  (∃ z ∈ Formalism.UG.intL L, σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
  (∀ x, At (evFin F v) (κ x)) ∧
  (∀ γ : Matrix (Fin a') (Fin (a + a')) (AE F E), At (evFin F v) γ → ∃ x, κ x = γ) ∧
  (∀ x, (∀ i j, x i j ∈ Formalism.UG.intL L) ↔ κ x ∈ latAtV G.V' G.W v) ∧
  (∀ x y, ψL ((GlobalTheory.Hk3.locH σL δ JS JT x y + σL (GlobalTheory.Hk3.locH σL δ JS JT x y)) / 2) =
    B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (κ x) (κ y))) ∧
  (∀ g h x, actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (ιS g, ιT h) (κ x) =
    κ (((h : GL (Fin (a + a')) L) : Matrix (Fin (a + a')) (Fin (a + a')) L) * x *
      (((g : GL (Fin a') L)⁻¹ : GL (Fin a') L) : Matrix (Fin a') (Fin a') L))) ∧
  (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) ∧ (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) ∧
  (∀ g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L),
    (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) → ιS g ∈ GlobalTheory.InertSph.KAt σ G.V' v) ∧
  (∀ h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L),
    (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ιT h ∈ GlobalTheory.InertSph.KAt σ G.W v)

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
open MeasureTheory GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.GelfandKazhdanHerm

open scoped InnerProductSpace

theorem exists_invariant_hermitian : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ, (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) ∧ (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) ∧ (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) ∧ (∀ k φ ψ, H (π.op (.cpt k) φ) (π.op (.cpt k) ψ) = H φ ψ) ∧ ∀ X φ ψ, H (π.op (.lie X) φ) ψ + H φ (π.op (.lie X) ψ) = 0 := by
  intro hB E _ _ _ a π hπ
  let μ : Measure (GA E a) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hc : ∀ φ ∈ π.V, Continuous φ.1 := fun φ hφ =>
    ContAut.continuous_of_isOpen_stab E a φ (π.cusp φ hφ).1.level
  have hm : ∀ φ ∈ π.V, MemL2Quotient (latticeGL E a) μ φ.1 := fun φ hφ => by
    obtain ⟨C, hC⟩ := hB.of_invariant (π.cusp φ hφ) (hπ φ hφ)
    exact (memL2_iff_isSqInt (hc φ hφ) (π.cusp φ hφ).1.left (hπ φ hφ)).2
      (GlobalTheory.DiscChar.isSqInt_of_bounded (hπ φ hφ) hC)
  let T := toL2ₗ μ π.V hm
  have hinj : Function.Injective T := toL2ₗ_injective hm hc
  have hR : ∀ (g : GA E a) (x y : L2 (latticeGL E a) μ),
      ⟪R (latticeGL E a) μ g x, R (latticeGL E a) μ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y => by
    let U : L2 (latticeGL E a) μ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
      ⟨(R (latticeGL E a) μ g).toLinearMap, fun v => norm_R _ v⟩
    exact U.inner_map_map x y
  refine ⟨((innerₛₗ ℂ).comp T).compl₂ T, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ
    exact inner_conj_symm (T ψ) (T φ)
  · intro φ h0
    have hT : T φ ≠ 0 := fun e => h0 (hinj (e.trans (map_zero T).symm))
    change 0 < (⟪T φ, T φ⟫_ℂ).re
    first
      | exact (re_inner_self_pos (𝕜 := ℂ)).2 hT
      | exact inner_self_pos.2 hT
      | exact (RCLike.inner_self_pos).2 hT
      | (rw [inner_self_eq_norm_sq_to_K]; norm_cast; simpa using hT)
  · intro k φ ψ
    change ⟪T (π.op (.fin k) φ), T (π.op (.fin k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (finGL E a k) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.fin k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.fin k) _ ψ.2)).symm
  · intro k φ ψ
    change ⟪T (π.op (.cpt k) φ), T (π.op (.cpt k) ψ)⟫_ℂ = ⟪T φ, T ψ⟫_ℂ
    rw [← hR (infGL E a (Unitary.toUnits k)) (T φ) (T ψ)]
    congr 1
    · exact (R_toL2ₗ hm φ (π.stable (.cpt k) _ φ.2)).symm
    · exact (R_toL2ₗ hm ψ (π.stable (.cpt k) _ ψ.2)).symm
  · intro X φ ψ
    change ⟪T (π.op (.lie X) φ), T ψ⟫_ℂ + ⟪T φ, T (π.op (.lie X) ψ)⟫_ℂ = 0
    have := _root_.GlobalTheory.LieSkew.lie_skew E a μ π.V hm π.stable (fun θ hθ => (π.cusp θ hθ).1) X φ ψ
    rw [eq_neg_iff_add_eq_zero] at this
    exact this

end GlobalTheory.GelfandKazhdanHerm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisationSectionNonemptyNonvanishing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.FibreTheta

theorem exists_sec_nonempty : ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ S),
    IsIntegral (Over.mk t ⊗ P.A).left → ∃ θ : LB.Sec (LB.LinComb P.L (K := Fin 1) ![(snd (Over.mk t) P.A).left] ![1]),
      (nonzeroLocus θ : Set (Over.mk t ⊗ P.A).left).Nonempty := by
  intro S P K _ t hI
  let T : Over S := Over.mk t
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.abelianSchemeLaws_all.2.secTwist S P 1 le_rfl K t (1 : T ⟶ P.A)
  have := P.isAb.comm
  have e : translPt P.A (1 : T ⟶ P.A) = snd T P.A := by
    show (fst T P.A ≫ 1) * snd T P.A = _
    rw [MonObj.comp_one, _root_.one_mul]
  have i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  have su : ∀ {M : Type} [AddCommMonoid M] (q : Fin (1 ^ P.g) → M), ∑ i, q i = q i₀ := fun q =>
    Finset.sum_eq_single i₀ (fun a _ h => absurd (Fin.ext (by have := a.2; have := i₀.2; simp at *; omega)) h) (by simp)

  have nz : ∃ j, (b i₀).f j ≠ 0 := by
    by_contra hz
    push_neg at hz
    obtain ⟨r, -, hu⟩ := hb (b i₀)
    have h0 : ∀ r' : Fin (1 ^ P.g) → Γ(T.left, ⊤), ∀ j, (b i₀).f j = ∑ i, ((T ⊗ P.A).left.presheaf.map
        (homOfLE le_top).op).hom ((fst T P.A).left.appTop.hom (r' i)) * (b i).f j := fun r' j => by
      rw [su, hz j, mul_zero]
    have := (hu (fun _ => 0) (h0 _)).trans (hu (fun _ => 1) (h0 _)).symm
    exact zero_ne_one ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm.injective
      ((map_zero _).trans ((congrFun this i₀).trans (map_one _).symm)))
  obtain ⟨j, hj⟩ := nz
  haveI : IsReduced (T ⊗ P.A).left := inferInstance
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (T ⊗ P.A).left.basicOpen ((b i₀).f j) := by
    by_contra h
    push_neg at h
    exact hj (eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy' => (h y hy').elim))
  have hy₀ : y ∈ nonzeroLocus (b i₀) := TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩
  have hF : FormEq (![(snd T P.A).left, (translPt P.A (1 : T ⟶ P.A)).left] : Fin 2 → _)
      ![((1 : ℕ) : ℤ) - 1, 1] (![(snd T P.A).left] : Fin 1 → _) ![1] := by
    intro U _ h
    rw [e]; simp [Fin.prod_univ_succ]
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec P.isLB hF (b i₀)
  choose J hJ using fun χ : (T ⊗ P.A).left ⟶ P.A.left => exists_chart P.isLB (χ y)
  have hJ' : Good P.L y J := hJ
  refine ⟨s, y, ?_⟩
  show y ∈ nonzeroLocus s
  rw [GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval s y hJ', hs _ (𝟙 _) y J hJ']
  exact (GlobalTheory.AbVarProj.mem_nonzeroLocus_iff_sval (b i₀) y hJ').1 hy₀

end GlobalTheory.FibreTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueRingHomOfSqZeroExtPointAffineStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ringHom_of_sqZeroExt_point_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (U : X.affineOpens) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (ρ : Sec s U.1 →+* B) (z : Sp (TrivSqZeroExt B M) ⟶ X), spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z = spMap ρ ≫ affPt s U → ∃! c : Sec s U.1 →+* TrivSqZeroExt B M, spMap c ≫ affPt s U = z ∧ ∀ b, (c b).fst = ρ b := by
  first | exact @GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | exact GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero | (intros; apply GlobalTheory.AbTan.exists_unique_ringHom_of_sqZero <;> assumption)
end

