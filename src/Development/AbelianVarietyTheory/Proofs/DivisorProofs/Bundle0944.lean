module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0914

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalPointsTransferIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.Loc

theorem smul_conj_iff {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (f : A) {N N' : Matrix n n A}
    (h : N * N' = 1) (h' : N' * N = 1) (X : Matrix n n A) :
    f • (N * X * N' - 1) = N * X * N' - 1 ↔ f • (X - 1) = X - 1 := by
  have e : N * X * N' - 1 = N * (X - 1) * N' := by rw [mul_sub, sub_mul, mul_one, h]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul]
  refine ⟨fun k => ?_, fun k => by rw [k]⟩
  have := congrArg (fun Y => N' * Y * N) k
  simpa only [← mul_assoc, h', one_mul, mul_assoc _ N' N, mul_one] using this

variable {D : D7}

theorem parts_ext {a b : Formalism.L2.Theta.AE D} (h1 : infPart D a = infPart D b) (h2 : finPart D a = finPart D b) :
    a = b := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  apply e.injective
  exact Prod.ext (by rw [he1, he1, h1]) (by rw [he2, he2, h2])

theorem map_one_apply {A B n : Type} [CommRing A] [CommRing B] [DecidableEq n] (φ : A →+* B) (i j : n) :
    φ ((1 : Matrix n n A) i j) = (1 : Matrix n n B) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem suppF_iff_fin (V : HSp D) (f : Formalism.L2.Theta.AE D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) :
    SuppF V f g ↔ finPart D f • (finMat D.sp.cm.sig V.gram g - 1) = finMat D.sp.cm.sig V.gram g - 1 := by
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have e2 : finPart D ((Formalism.L2.Theta.mt V g - 1) i j) = (finMat D.sp.cm.sig V.gram g - 1) i j := by
    rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, map_one_apply]
    rfl
  have e1 : infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_one_apply, sub_eq_zero]
    have : infHom V g = 1 := hg
    exact congrArg (fun m : GL (Fin V.rank) _ => m.1 i j) this
  rw [Matrix.smul_apply, smul_eq_mul, ← e2]
  refine ⟨fun h => by rw [← RingHom.map_mul, h], fun h => parts_ext ?_ ?_⟩
  · rw [RingHom.map_mul, e1, mul_zero]
  · rw [RingHom.map_mul, h]

theorem comp_of_isPrimeIdem {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem P e f)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 1) ∧
    (Q.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D f) Q = 0) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, ⟨α, rfl, h1, h0⟩, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ h
  have e : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (finPart D (algebraMap _ (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α))) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) := by
    rw [GlobalTheory.LFun.finAdEquiv_apply rfl]
    change GlobalTheory.LFun.toCompl rfl ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α) ⊗ₜ[D.host.F]
      (1 : D.host.E)) = _
    rw [GlobalTheory.LFun.toCompl_tmul, map_one, mul_one]
    rfl
  rw [e]
  refine ⟨fun hQ => ?_, fun hQ => by rw [h0 _ hQ, map_zero]⟩
  have h2 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F (Q.under (𝓞 D.host.F)) α = 1 := by
    revert h1
    generalize P.under (𝓞 D.host.F) = v at hQ
    subst hQ
    exact id
  rw [h2, map_one]

theorem supp_iff_loc [IsCMField D.host.E] {n : ℕ} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D}
    (h : IsPrimeIdem P e f) (x : UA D.host.E n) :
    finPart D f • (((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) =
      ((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1 ↔
    ∀ u : HeightOneSpectrum (𝓞 D.host.E), u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
  have key : ∀ i j (u : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      ((((x : GL (Fin n) (Ad D.host.E)) : Matrix (Fin n) (Fin n) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) - 1) i j) u =
      (cLoc u x).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j := by
    intro i j u
    rw [Matrix.sub_apply, map_sub, Matrix.map_apply, RingEquiv.apply_symm_apply,
      ← map_one_apply ((pLoc D.host.E u).comp (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom)]
    rfl
  have ev : ∀ (a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (u : HeightOneSpectrum (𝓞 D.host.E)),
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (a * b) u =
        GlobalTheory.LFun.finAdEquiv D.host.F D.host.E a u * GlobalTheory.LFun.finAdEquiv D.host.F D.host.E b u := by
    intro a b u
    rw [map_mul]; rfl
  constructor
  · intro k u hu
    refine Units.ext (Matrix.ext fun i j => ?_)
    have := congrArg (fun m => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (m i j) u) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    rw [ev, (comp_of_isPrimeIdem h u).2 hu, zero_mul, key, eq_comm, sub_eq_zero] at this
    exact this
  · intro k
    refine Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
      (FiniteAdeleRing.ext _ fun u => ?_)
    rw [Matrix.smul_apply, smul_eq_mul, ev]
    by_cases hu : u.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
    · rw [(comp_of_isPrimeIdem h u).1 hu, one_mul]
    · rw [key, k u hu, Units.val_one, sub_self, mul_zero]

theorem finMat_mul (V : HSp D) (g h : Formalism.L2.Theta.GA D V) :
    finMat D.sp.cm.sig V.gram (g * h) = finMat D.sp.cm.sig V.gram g * finMat D.sp.cm.sig V.gram h := by
  have := congrArg Units.val ((finHom V).map_mul g h)
  rw [Units.val_mul] at this
  exact this

theorem finMat_one (V : HSp D) : finMat D.sp.cm.sig V.gram (1 : Formalism.L2.Theta.GA D V) = 1 :=
  congrArg Units.val (finHom V).map_one

theorem map_mul_inv {K A n : Type} [Field K] [CommRing A] [Fintype n] [DecidableEq n] {T : Type} [FunLike T K A]
    [RingHomClass T K A] (φ : T) {M : Matrix n n K} (hu : IsUnit M.det) : M.map φ * M⁻¹.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem locU_iff : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* Formalism.L2.Theta.GA D V) (h₀ : Formalism.L2.Theta.GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU (E := D.host.E) (n := V.rank) ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e f, IsPrimeIdem P e f) ∧ (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) := by
  intro D _ V j h₀ M hM hh hfin hmat _
  refine ⟨fun P => ?_, fun P e f h x => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
    exact GlobalTheory.IdemSupport.exists_isPrimeIdem hΦ P
  have hu : IsUnit M.det := Matrix.isUnit_det_of_left_inverse hM
  have hG : cj j h₀ x ∈ GfC V ↔ x ∈ finU (E := D.host.E) (n := V.rank) := by
    rw [hfin, cj_apply, Subgroup.mul_mem_cancel_right _ hh, Subgroup.mul_mem_cancel_left _ (inv_mem hh)]
  have hL : x ∈ locU V.rank P ↔ x ∈ finU (E := D.host.E) (n := V.rank) ∧ ∀ u : HeightOneSpectrum (𝓞 D.host.E),
      u.under (𝓞 D.host.F) ≠ P.under (𝓞 D.host.F) → cLoc u x = 1 := by
    simp only [locU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rw [hL, ← hG]
  refine and_congr_right fun hx => ?_
  have m1 := map_mul_inv (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F]
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) hu
  have m2 := mul_eq_one_comm.1 m1
  have e1 : finMat D.sp.cm.sig V.gram (cj j h₀ x) =
      finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram (j x) * finMat D.sp.cm.sig V.gram h₀ := by
    rw [cj_apply, finMat_mul, finMat_mul]
  have k1 : finMat D.sp.cm.sig V.gram h₀⁻¹ * finMat D.sp.cm.sig V.gram h₀ = 1 := by
    rw [← finMat_mul, inv_mul_cancel, finMat_one]
  refine ((suppF_iff_fin V f hx).trans ?_).symm
  rw [e1]
  refine (smul_conj_iff _ k1 (mul_eq_one_comm.1 k1) _).trans ?_
  rw [hmat]
  exact (smul_conj_iff _ m1 m2 _).trans (supp_iff_loc h x)

end GlobalTheory.DefTransfer.Loc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagOfUpTOfPreserves
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

private theorem eq_diagonal_of_lower_upper_zero {n : ℕ} (b : Mt n) (hlow : ∀ a c : Fin n, c < a → b a c = 0)
    (hup : ∀ a c : Fin n, a < c → b a c = 0) : b = diagonal fun a => b a a := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [hup i j hij, diagonal_apply_ne _ (ne_of_lt hij)]
  · rw [diagonal_apply_eq]
  · rw [hlow i j hij, diagonal_apply_ne _ (ne_of_gt hij)]

private theorem eq_exp_arg_mul_I_of_star_mul_self_eq_one (z : ℂ) (hz : star z * z = 1) :
    z = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
  have hn : Complex.normSq z = 1 := by
    have h1 : (Complex.normSq z : ℂ) = 1 := (Complex.normSq_eq_conj_mul_self).trans hz
    exact_mod_cast h1
  have habs : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hn
    have h3 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  have key := Complex.norm_mul_exp_arg_mul_I z
  rw [habs, Complex.ofReal_one, one_mul] at key
  exact key.symm

theorem diag_of_upT_of_preserves {n : ℕ} (d : Fin n → ℂ) (hd : ∀ a, d a * d a = 1) (b : Mt n) (hb : UpT b)
    (h : bᴴ * diagonal d * b = diagonal d) :
    ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  classical
  have hDD : diagonal d * diagonal d = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact hd a
  have hdne : ∀ a, d a ≠ 0 := by
    intro a h0
    have h1 := hd a
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1

  have hleft : diagonal d * bᴴ * diagonal d * b = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc bᴴ, h, hDD]
  letI : Invertible b.det := (Ne.isUnit hb.1).invertible
  letI : Invertible b := Matrix.invertibleOfDetInvertible b
  have hinv : b⁻¹ = diagonal d * bᴴ * diagonal d := Matrix.inv_eq_left_inv hleft

  have hbt : Matrix.BlockTriangular b id := fun i j hij => hb.2 i j hij
  have hbit := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have hup : ∀ a c : Fin n, a < c → b a c = 0 := by
    intro a c hac
    have h0 : b⁻¹ c a = 0 := hbit hac
    rw [hinv, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (hdne c)
      · exact star_eq_zero.1 h2
    · exact absurd h1 (hdne a)
  have hdiag := eq_diagonal_of_lower_upper_zero b hb.2 hup

  have hh := h
  rw [hdiag, Matrix.diagonal_conjTranspose, diagonal_mul_diagonal, diagonal_mul_diagonal] at hh
  have hu : ∀ a, star (b a a) * b a a = 1 := by
    intro a
    have h1 := congrFun (Matrix.diagonal_injective hh) a
    simp only [Pi.star_apply] at h1
    have h2 : d a * (star (b a a) * b a a) = d a * 1 := by linear_combination h1
    exact mul_left_cancel₀ (hdne a) h2
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  calc b = diagonal fun a => b a a := hdiag
    _ = _ := by
      congr 1
      funext a
      exact eq_exp_arg_mul_I_of_star_mul_self_eq_one _ (hu a)

theorem diag_of_upT_unitary : ∀ (n : ℕ) (Hm : Mt n) (q : ℕ) (x₀ : Mt n), OrthFr Hm q x₀ → ∀ b : Mt n, UpT b → x₀ * b * x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH Hm → ∃ s : Fin n → ℝ, b = diagonal fun a => Complex.exp ((s a : ℂ) * Complex.I) := by
  intro n Hm q x₀ hx b hb hu
  obtain ⟨-, hx⟩ := hx
  set d : Fin n → ℂ := fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) with hd_def
  have hd : ∀ a, d a * d a = 1 := by
    intro a
    simp only [hd_def, ReciprocityTheory.ChartRestriction.G.FD.sgn]
    split_ifs <;> norm_num
  have hdet : x₀.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hx
    rw [det_mul, det_mul, h0, mul_zero, det_diagonal] at h1
    refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
    intro h2
    have h3 := hd a
    rw [h2, zero_mul] at h3
    exact zero_ne_one h3
  have hu' : (x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹) = Hm := hu
  have hcx : x₀ * b * x₀⁻¹ * x₀ = x₀ * b := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), Matrix.mul_one]

  have key : bᴴ * diagonal d * b = diagonal d := by
    calc bᴴ * diagonal d * b = bᴴ * (x₀ᴴ * Hm * x₀) * b := by rw [hx]
      _ = (x₀ * b)ᴴ * Hm * (x₀ * b) := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (x₀ * b * x₀⁻¹ * x₀)ᴴ * Hm * (x₀ * b * x₀⁻¹ * x₀) := by rw [hcx]
      _ = x₀ᴴ * ((x₀ * b * x₀⁻¹)ᴴ * Hm * (x₀ * b * x₀⁻¹)) * x₀ := by
        rw [conjTranspose_mul (x₀ * b * x₀⁻¹) x₀]; simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hu', hx]
  exact diag_of_upT_of_preserves d hd b hb key

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharacterTrivialOnPrincipalLevel
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MuLevel

theorem det_cong_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : N ≠ 0) (k : GA D V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ w ∈ intAE D, (finHom V k).1.det - 1 = N • w := by
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) :=
    V.L0.map (V.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))
  have hL : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold Formalism.L2.Pj.latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hspan : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
          Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : V.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : V.hT y (e z) = 0 := by
          have hh := V.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  rw [hL] at hk
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]
  exact GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F L hfg hsp N hN _ hk


set_option maxHeartbeats 1000000 in
theorem exists_root_of_level {D : D7} (V : HSp D) (N : ℕ) (hN : Odd N) (k : GA D V) (hf : k ∈ GfC V)
    (hk : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y) :
    ∃ x : (AE D)ˣ, IsDetRoot V k x ∧ FinUnit x ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y := by
  obtain ⟨w, hw, hwe⟩ := det_cong_of_level V N hN.pos.ne' k hk
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ?_, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, p, hp, hY2 ▸ hpe⟩
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have he1 : ∀ z, (e z).1 = infPart D z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart D z := fun z => (he z).2
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have h1 : infHom V k = 1 := hf
  have hs : infPart D (sigR (AF D.host.F) D.sp.cm.sig (Y : AE D)) =
      sigR (Ainf D.host.F) D.sp.cm.sig (infPart D (Y : AE D)) := GlobalTheory.DetRootCong.map_sigR _ _ _
  refine e.injective (Prod.ext ?_ ?_)
  · rw [he1, he1, RingHom.map_mul, hs, ← hdet', h1, hY1, RingHom.map_one, mul_one]
    exact Matrix.det_one.symm
  · have hs' := GlobalTheory.DetRootCong.finPart_sigR D (Y : AE D)
    rw [hY2] at hs'
    rw [hdet, ← hs', ← RingHom.map_mul] at hroot
    exact (he2 _).trans ((hY2.trans hroot).trans (he2 _).symm)

theorem exists_ext {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : K →+* ℂ) :
    ∃ τ : L →+* ℂ, τ.comp (algebraMap K L) = σ := by
  letI : Algebra K ℂ := σ.toAlgebra
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨f.toRingHom, RingHom.ext fun x => f.commutes x⟩


set_option maxHeartbeats 1000000 in
theorem mu_eq_one_of_mem_level : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, ∀ k ∈ T.Kf ((i : ℕ) + 1) σ, T.mu ((i : ℕ) + 1) σ k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL h _ i σ hσ _ k hk
  have hj := inR i
  obtain ⟨τ, rfl⟩ := exists_ext (L := D.what₂.LL) σ
  obtain ⟨hf, hk'⟩ := (h.laws.levelK _ hj _ hσ k).1 hk
  have hodd : Odd (D.host.g 0 * D.host.g 1) := h.laws.pins.2.1.1 ▸ T.Q.l.odd
  obtain ⟨x, hx, hu, hc⟩ := exists_root_of_level _ _ hodd k hf hk'
  have hm := R.C.isMu0 i
  have h1 : R.mu0 ((i : ℕ) + 1) x = 1 := by
    refine GlobalTheory.tame_heckeChar_eq_one_of_finUnit D _ _ (hL.mu0 i) hm.tame _ (fun P hP => hm.unr P fun a ha => hP ?_) x hu hc
    rw [Nat.cast_mul]
    fin_cases a
    · exact Ideal.mul_mem_right _ _ ha
    · exact Ideal.mul_mem_left _ _ ha
  obtain ⟨y, hy1, hy2⟩ := (h.chiR i τ hσ).2.2.2.1 x hu.1
  have h2 : algebraMap T.Q.c.F D.what₂.LL y = 1 :=
    D.what₂.embLL.injective (by rw [← hy1, h1, map_one, Circle.coe_one])
  rw [(h.laws.muVal _ hj _ hσ).2 k x hx, hy2, h2, map_one]

end GlobalTheory.MuLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpairEigenRootNormSq
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKDef

theorem DPair.form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : DPair G) (v : InfinitePlace G.F) :
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v P.γ
      = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKDef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueNormSqOfSimilitudeHermitianSignatureStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvalue_normSq_of_similitude_hermitian_signature : ∀ (n : ℕ) (h Q Γ : Matrix (Fin n) (Fin n) ℂ) (hh : h.IsHermitian) (Z : GL (Fin n) ℂ) (c : ℝ),
    sigPosH hh ≤ 1 → sigPosH hh + sigNegH hh = n → Q = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * Z → c ≠ 0 →
    Γᴴ * Q * Γ = (c : ℂ) • Q →
    (sigPosH hh = 0 ∨ ∃ (μ : ℂ) (x₀ : Fin n → ℂ), Γ *ᵥ x₀ = μ • x₀ ∧ 0 < (star x₀ ⬝ᵥ (Q *ᵥ x₀)).re) →
    ∀ (w : ℂ) (x : Fin n → ℂ), x ≠ 0 → Γ *ᵥ x = w • x → ‖w‖ ^ 2 = c := by
  first | (exact @GlobalTheory.eig_norm_sq_of_similitude) | (exact GlobalTheory.eig_norm_sq_of_similitude) | (intros; apply GlobalTheory.eig_norm_sq_of_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRatHomologyStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rat_homology_eq_finrank_int : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ), Module.Finite ℤ (C.homology n) → Module.finrank ℚ ((((ModuleCat.extendScalars (Int.castRingHom ℚ)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).homology n) = Module.finrank ℤ (C.homology n) := by
  first | exact @GlobalTheory.RatHomology.finrank_rat_homology | exact GlobalTheory.RatHomology.finrank_rat_homology | (intros; apply GlobalTheory.RatHomology.finrank_rat_homology <;> assumption)
end

