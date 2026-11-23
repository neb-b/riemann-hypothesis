module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeExponentsAinfComparison
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.GLq.Leibniz

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, wh ψ (f j) := by
  unfold wh tr
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_mul_const (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_gl_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Subsingleton.elim _ _)
  have huniv : (Finset.univ : Finset (Gn g 0)) = {1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hsub x
  have hP : IsUniUp ((1 : Gn g 0) : Mt g 0) := fun a _ => a.elim0
  unfold wh tr eU eDat
  rw [huniv, Finset.sum_singleton]
  rw [Finset.filter_singleton, if_pos hP, Finset.sum_singleton, Finset.card_singleton]
  simp

theorem degL_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) :
    degL ((I.sort (· ≤ ·)).map L.get) = ∑ j ∈ I, (L.get j).1 := by
  unfold degL
  rw [List.map_map]
  have := Finset.sort_eq I (· ≤ ·)
  rw [Finset.sum_eq_multiset_sum, ← this, Multiset.map_coe, Multiset.sum_coe]
  rfl

theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  have h := degL_sort_map L Finset.univ
  rw [Fin.sort_univ, List.map_get_finRange] at h
  exact h

theorem mem_of_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) {p : Pc g}
    (hp : p ∈ (I.sort (· ≤ ·)).map L.get) : p ∈ L := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  exact List.get_mem L j

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (hcL L (degL L)) = 1 := by
  intro L
  induction L with
  | nil => intro _; exact wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL' q hq).1.2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.1.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul]
      rw [wh_mul_const, ih hL', hp.2, one_mul]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem wh_hcL_of_deg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g)) (n : ℕ) (hn : degL L = n)
    (hL : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L n) = 1 := by
  subst hn
  exact wh_hcL ψ hψ L hL

theorem main : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ),
    degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) →
      wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  intro g _ ψ hψ L n i hn hi hL
  refine ⟨?_, wh_hcL_of_deg ψ hψ L n hn hL⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hcusp : ∀ p ∈ L, IsCusp p.2 := fun p hp => (hL p hp).1
  have htot : ∑ j : Fin L.length, (L.get j).1 = i + k := by rw [← degL_eq_sum]; exact hn
  have hsub : ∀ (I : Finset (Fin L.length)), ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2 ∧ wh ψ p.2 = 1 :=
    fun I p hp => hL p (mem_of_sort_map L I hp)
  have hB : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    refine wh_hcL_of_deg ψ hψ _ k ?_ (hsub Iᶜ)
    rw [degL_sort_map]
    have := Finset.sum_compl_add_sum I (fun j => (L.get j).1)
    omega
  have hA : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((I.sort (· ≤ ·)).map L.get) i) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    exact wh_hcL_of_deg ψ hψ _ i (by rw [degL_sort_map]; exact hI.2) (hsub I)
  have key : ∀ b, b = k → ∀ h : Gn g i, wh ψ (res i b (hcL L (i + k)) h) =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) := by
    intro b hb h
    subst hb
    have hr : res i b (hcL L (i + b)) h = fun y => ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i),
          hcL ((I.sort (· ≤ ·)).map L.get) i h * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y :=
      funext fun y => GlobalTheory.GLq.ResCuspProd.main g L i b hn hcusp h y
    rw [hr, wh_sum]
    exact Finset.sum_congr rfl fun I _ => wh_const_mul ψ _ _
  have hder : der ψ i (hcL L (i + k)) = fun h =>
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) :=
    funext fun h => key (i + k - i) (by omega) h
  rw [hder, wh_sum, Finset.sum_congr rfl fun I hI => by rw [wh_mul_const, hA I hI, hB I hI, one_mul]]
  simp

end GlobalTheory.GLq.Leibniz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturality
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrisComparison

theorem toB_tmul' {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O) (w : Ainf l) :
    toB l O (o ⊗ₜ w) = o ⊗ₜ acrisToBcris l (ainfToAcris l w) := rfl

theorem toB_frobOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (x : OA l O) :
    toB l O (frobOA l O x) = frobOB l O (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, frobOB_toOB, frobOCr_toOCr]

theorem toB_galOA {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OA l O) :
    toB l O (galOA O g x) = galOB O g (toB l O x) := by
  simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]

theorem map_smul_tw {O R N : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup N] [Module O N]
    (σ : R →ₐ[O] R) (h : N →ₗ[O] N) (r : R) (z : R ⊗[O] N) :
    TensorProduct.map σ.toLinearMap h (r • z) = σ r • TensorProduct.map σ.toLinearMap h z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul x y => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem inclL_smul' {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (r : OA l O) (c : ι → OA l O) : inclL t ϖ P (r • c) = inclO l O r • inclL t ϖ P c := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem exists_Y : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → ∃ Y : Matrix ι ι (OA l O), (∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) ∧ Y i j = ϖ.iTot t K f) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hα
  have key : ∀ i j, ∃ f : ZMod a → A O K, (∀ τ, (f τ : K⟦X⟧) = E K l e ^ α * P.mx τ i j) := by
    intro i j
    have hv : (fun τ k => P.mx τ k j : Vec K a ι) ∈ P.L := mem_tot.2 fun τ => P.mem_extc.2
      ⟨Pi.single j 1, fun k => by
        by_cases hk : k = j
        · subst hk; simp only [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hk]; exact zero_mem _, by
        ext1 k; simp [Matrix.mulVec_single]⟩
    have h := hα _ hv
    exact ⟨fun τ => ⟨E K l e ^ α * P.mx τ i j, mem_tot.1 h τ i⟩, fun τ => rfl⟩
  choose f hf using key
  exact ⟨fun i j => ϖ.iTot t K (f i j), fun i j => ⟨f i j, hf i j, rfl⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), (∃ jB, IsCrisCmp I jB) ∧ ∀ (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → (∀ (m m' : P.MMl), m'.1 = P.phi m.1 → jB (toBcris t ϖ P m') = TWmap (frobOB l O) T (jB (toBcris t ϖ P m))) ∧ (∀ w b b', IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB w b' → b = b') ∧ (∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (phiW t ϖ P w) (TWmap (frobOB l O) T b)) ∧ (∀ x : ↥T.L.T, IsCrisVal t ϖ P jB (I.ofT x) ((1 : OB l O) ⊗ₜ[O] x)) ∧ (∀ g : Gl l, (∀ v ∈ LA t ϖ P, I.act (sQ l g) g v ∈ LA t ϖ P) → ∀ w b, IsCrisVal t ϖ P jB w b → IsCrisVal t ϖ P jB (I.act (sQ l g) g w) (actB (sQ l) T g b)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨ε, hε⟩ := (_root_.GlobalTheory.MuOfEps.main l).1
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, hμB, -, -, -⟩ := (_root_.GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨-, -, hK3, hK4⟩ := _root_.GlobalTheory.BKExp.exponents l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  have hunit : ∀ n : ℕ, IsUnit (toB l O (1 ⊗ₜ (muOf ε ^ n))) := fun n => by
    rw [toB_tmul', map_pow, map_pow]
    exact (hμB.pow n).map (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
  obtain ⟨Y, hY⟩ := exists_Y l a e O K t ϖ ι P α hα
  have hEu := _root_.GlobalTheory.BKGal.FrobEis.isUnit_toB_frob_eis l a e O ϖ
  have hYphi := _root_.GlobalTheory.BKReal.phiW_inclL_E_pow l a e O K t ϖ ι P α Y hY
  have hSl := _root_.GlobalTheory.BKGal.FrobCoord.toBcris_phi l a e O K t ϖ ι P α Y hY
  refine ⟨_root_.GlobalTheory.BKGal.exists_isCrisCmp l a e O K t ϖ ι P T I, fun jB hjB => ?_⟩
  have hμL : ∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O (1 ⊗ₜ (muOf ε ^ α)) • v) = TWincl (inclO l O) T z :=
    hK4
  have keyφ := _root_.GlobalTheory.BKGal.cmp_semilinear_pair l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (frobOA l O) (frobOW l O) (frobOB l O)
    LinearMap.id (phiW t ϖ P) (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α) (Y.map (frobOA l O))
    (fun x => (frobOW_inclO x).symm) toB_frobOA (fun v => I.j_φ v) (phiW_smul t ϖ P)
    (fun c => by rw [map_pow]; exact hYphi c)
  refine ⟨fun m m' hmm => ?_, fun w b b' hb hb' => ?_, fun w b hb => ?_, fun x => ?_, fun g hg w b hb => ?_⟩
  · refine (hEu.pow α).smul_left_cancel.1 ?_
    rw [← LinearEquiv.map_smul, hSl m m' hmm, keyφ, map_pow]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨m', c', hm', hw', hb'⟩ := hb'
    have h1 : m' • c = m • c' := inclL_injective t ϖ P (by
      rw [inclL_smul', inclL_smul', ← hw, ← hw', smul_smul, smul_smul, ← map_mul, ← map_mul, mul_comm])
    have h2 : ∀ (r : OA l O) (d : ι → OA l O), toB l O r • (fun i => toB l O (d i)) = fun i => toB l O ((r • d) i) :=
      fun r d => funext fun i => by simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    refine ((hm.mul hm').smul_left_cancel).1 ?_
    rw [mul_comm, mul_smul, hb, mul_comm, mul_smul, hb', ← LinearEquiv.map_smul, ← LinearEquiv.map_smul, h2, h2, h1]
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    refine ⟨frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobOA l O m, Y.map (frobOA l O) *ᵥ fun i => frobOA l O (c i), ?_, ?_, ?_⟩
    · rw [map_mul, map_pow, toB_frobOA m]
      exact (hEu.pow α).mul (hm.map _)
    · rw [map_mul, map_pow, mul_smul, ← frobOW_inclO m, ← phiW_smul, hw]
      exact hYphi c
    · have h3 := keyφ (fun i => toB l O (c i))
      rw [map_mul, mul_smul, toB_frobOA m]
      change _ • frobOB l O (toB l O m) • TensorProduct.map (frobOB l O).toLinearMap LinearMap.id b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toB_frobOA]
  · obtain ⟨c, hc⟩ := hK3 x
    refine ⟨1 ⊗ₜ (muOf ε ^ β), c, hunit β, hc.symm, ?_⟩
    have h4 := hjB c ((1 ⊗ₜ (muOf ε ^ β)) ⊗ₜ x) (by
      rw [hc, LinearEquiv.map_smul, I.j_ofT, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl)
    rw [h4, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  · obtain ⟨m, c, hm, hw, hb⟩ := hb
    obtain ⟨Γ, hΓ⟩ := (I.exists_isLMat_iff (sQ l g) g).2 hg
    have key := _root_.GlobalTheory.BKGal.cmp_semilinear_pair l a e O K t ϖ ι P T I jB hjB _ (hunit α) hμL (galOA O (sQ l g)) (galOW O (sQ l g))
      (galOB O (sQ l g)) (T.actT g) (I.act (sQ l g) g) 1 Γ (fun x => (galOW_inclO _ x).symm) (toB_galOA _)
      (fun v => I.j_act _ _ v) (I.act_smul _ _) (fun c => by rw [map_one, one_smul]; exact hΓ c)
    refine ⟨galOA O (sQ l g) m, Γ *ᵥ fun i => galOA O (sQ l g) (c i), ?_, ?_, ?_⟩
    · rw [toB_galOA]
      exact hm.map _
    · rw [← galOW_inclO, ← I.act_smul, hw]
      exact hΓ c
    · have h3 := key (fun i => toB l O (c i))
      rw [map_one, one_smul] at h3
      rw [toB_galOA]
      change _ • TensorProduct.map (galOB O (sQ l g)).toLinearMap (T.actT g) b = _
      rw [← map_smul_tw, hb, ← h3]
      congr 1
      ext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul, toB_galOA]

end GlobalTheory.CrisComparison
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal


open GlobalTheory.BKGal.HatVal in
theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using _root_.GlobalTheory.BKGal.HatVal.coord_E_pow_basis l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := _root_.GlobalTheory.BKGal.HatVal.Epow_smul_jB_toBcris_eq_sum l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := _root_.GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply _root_.GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => _root_.GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMemStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ), N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') → (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) → ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  first
  | exact @GlobalTheory.NabScale.nabAtr_smul_pow_mem
  | intro E K _ _ _ _ ι _ n emb lam M M' N hN hM hM' h1 h2
    exact GlobalTheory.NabScale.nabAtr_smul_pow_mem E K ι n emb lam M M' N hN
      hM.toIsLattice hM'.toIsLattice h1 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalListHarishChandraPairingNeZeroStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_list_harishChandra_pairing_ne_zero : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (χ : Gn g n → ℂ), IsIrr χ → ∃ L : List (Pc g), (∀ p ∈ L, IsCusp p.2) ∧ degL L = n ∧ ip χ (hcL L n) ≠ 0 := by
  first | exact @GlobalTheory.GLq.SuppCusp.exists_cusp_list | exact GlobalTheory.GLq.SuppCusp.exists_cusp_list | (intros; apply GlobalTheory.GLq.SuppCusp.exists_cusp_list <;> assumption)
end

