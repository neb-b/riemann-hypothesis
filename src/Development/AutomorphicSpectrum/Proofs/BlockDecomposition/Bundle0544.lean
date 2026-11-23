module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

def sh (x : Tl l) : ℂ_[l] := ((PreTilt.untilt x : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l])

def omC : Om l →+* ℂ_[l] := algebraMap (Om l) ℂ_[l]

theorem omC_apply (y : Om l) : omC y = (y : ℂ_[l]) := (PadicComplex.coe_eq _ y).symm

theorem norm_omC (y : Om l) : ‖omC y‖ = ‖y‖ := by
  rw [omC_apply, PadicComplex.norm_extends]

def oc (K : FinExt l) : ↥(OL K) →+* ℂ_[l] :=
  (omC (l := l)).comp ((K.1.val : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

theorem oc_apply (K : FinExt l) (c : ↥(OL K)) : oc K c = (((c : ↥K.1) : Om l) : ℂ_[l]) :=
  omC_apply _

theorem norm_oc_le_one (K : FinExt l) (c : ↥(OL K)) : ‖oc K c‖ ≤ 1 := by
  have h := (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K (c : ↥K.1)).1 (GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K c).2
  rw [oc_apply, PadicComplex.norm_extends]
  exact h

@[simp] theorem sh_zero : sh (0 : Tl l) = 0 := by
  simp [sh, GroundTheory.PAdicHodge.untilt_zero]

@[simp] theorem sh_one : sh (1 : Tl l) = 1 := by
  simp [sh]

theorem sh_mul (x y : Tl l) : sh (x * y) = sh x * sh y := by
  simp [sh, GroundTheory.PAdicHodge.untilt_mul]

theorem sh_pow (x : Tl l) (n : ℕ) : sh (x ^ n) = sh x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, sh_mul, ih]

theorem norm_eq_norm_sh (x : Tl l) : ‖x‖ = ‖sh x‖ := rfl

theorem norm_sh_le_one (x : Tl l) : ‖sh x‖ ≤ 1 := GroundTheory.PAdicHodge.norm_untilt_le_one x

theorem norm_sh_add_sub_le (x y : Tl l) : ‖sh (x + y) - (sh x + sh y)‖ ≤ ‖(l : ℂ_[l])‖ := by
  simpa [sh] using GroundTheory.PAdicHodge.norm_untilt_add_sub_le x y

theorem exists_sh_near (y : ℂ_[l]) (hy : ‖y‖ ≤ 1) : ∃ x : Tl l, ‖sh x - y‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨x, hx⟩ := GroundTheory.PAdicHodge.exists_mk_untilt_eq (K := ℂ_[l]) (p := l)
    ⟨y, GroundTheory.PAdicHodge.mem_normInteger.2 hy⟩
  exact ⟨x, by simpa [sh] using (GroundTheory.PAdicHodge.mk_eq_mk_iff_norm_sub_le (p := l)).1 hx⟩

theorem thB_tch (x : Tl l) : thB l (tch l x) = sh x := by
  show GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField l (wB l (WittVector.teichmuller l x)) = _
  rw [wB, GroundTheory.PAdicHodge.IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus,
    WittVector.fontaineTheta_teichmuller]
  rfl

theorem thB_rB (y : Om l) : thB l (rB l y) = (y : ℂ_[l]) :=
  GroundTheory.PAdicHodge.thetaAlgHom_algClToBdR l y

theorem tch_mul (x y : Tl l) : tch l (x * y) = tch l x * tch l y := by
  simp [tch, map_mul]

theorem tch_pow (x : Tl l) (n : ℕ) : tch l (x ^ n) = tch l x ^ n := by
  induction n with
  | zero => simp [tch]
  | succ n ih => rw [pow_succ, pow_succ, tch_mul, ih]

theorem sh_actT (g : GQ l) (x : Tl l) :
    sh (actT g x) = GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (sh x) :=
  GroundTheory.PAdicHodge.AInf.coe_untilt_gal (Formalism.Per6.toBot g) x

theorem galCp_omC (g : GQ l) (y : Om l) :
    GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) (omC y) = omC (g y) := by
  rw [omC_apply, omC_apply]
  exact GroundTheory.PAdicHodge.galCp_coe (Formalism.Per6.toBot g) y

theorem norm_galCp (g : GQ l) (x : ℂ_[l]) : ‖GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) x‖ = ‖x‖ :=
  GroundTheory.PAdicHodge.norm_galCp _ x

theorem norm_sub_pow (x y : Tl l) (f : ℕ) : ‖x ^ l ^ f - y ^ l ^ f‖ = ‖x - y‖ ^ l ^ f := by
  rw [← sub_pow_char_pow, norm_pow]

section Near

variable {ρ : ℝ}

theorem near_add (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x + y) - (A + B)‖ ≤ ρ := by
  have e : sh (x + y) - (A + B) = (sh (x + y) - (sh x + sh y)) + ((sh x - A) + (sh y - B)) := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((norm_sh_add_sub_le x y).trans hρ)
    ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)))

theorem near_mul {x y : Tl l} {A B : ℂ_[l]} (hB : ‖B‖ ≤ 1) (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x * y) - A * B‖ ≤ ρ := by
  have e : sh (x * y) - A * B = sh x * (sh y - B) + (sh x - A) * B := by rw [sh_mul]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_sh_le_one x)).trans hy
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hB).trans hx

theorem near_neg (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ) :
    ‖sh (-x) - (-A)‖ ≤ ρ := by
  have h := norm_sh_add_sub_le x (-x)
  rw [add_neg_cancel, sh_zero, zero_sub, norm_neg] at h
  have e : sh (-x) - (-A) = (sh x + sh (-x)) - (sh x - A) := by ring
  rw [e, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (h.trans hρ) (by rw [norm_neg]; exact hx))

theorem near_sub (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} {A B : ℂ_[l]} (hx : ‖sh x - A‖ ≤ ρ)
    (hy : ‖sh y - B‖ ≤ ρ) : ‖sh (x - y) - (A - B)‖ ≤ ρ := by
  rw [sub_eq_add_neg x y, sub_eq_add_neg A B]
  exact near_add hρ hx (near_neg hρ hy)

theorem near_pow (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x : Tl l} {A : ℂ_[l]} (hA : ‖A‖ ≤ 1)
    (hx : ‖sh x - A‖ ≤ ρ) (n : ℕ) : ‖sh (x ^ n) - A ^ n‖ ≤ ρ := by
  induction n with
  | zero => simpa using (norm_nonneg _).trans hρ
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact near_mul hA ih hx

theorem near_sum (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {ι : Type*} (s : Finset ι) {x : ι → Tl l}
    {A : ι → ℂ_[l]} (hx : ∀ i ∈ s, ‖sh (x i) - A i‖ ≤ ρ) :
    ‖sh (∑ i ∈ s, x i) - ∑ i ∈ s, A i‖ ≤ ρ := by
  induction s using Finset.induction_on with
  | empty => simpa using (norm_nonneg _).trans hρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact near_add hρ (hx a (Finset.mem_insert_self _ _))
      (ih fun i hi => hx i (Finset.mem_insert_of_mem hi))

theorem near_of_norm_sub_le (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖x - y‖ ≤ ρ) :
    ‖sh x - sh y‖ ≤ ρ := by
  have h1 : ‖sh (x - y) - 0‖ ≤ ρ := by rw [sub_zero]; exact h
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  simpa using near_add hρ h1 h2

theorem norm_sub_le_of_near (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) {x y : Tl l} (h : ‖sh x - sh y‖ ≤ ρ) :
    ‖x - y‖ ≤ ρ := by
  have h1 : ‖sh x - sh x‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h2 : ‖sh y - sh y‖ ≤ ρ := by simpa using (norm_nonneg _).trans hρ
  have h3 := near_sub hρ h1 h2
  have e : sh (x - y) = (sh (x - y) - (sh x - sh y)) + (sh x - sh y) := by ring
  rw [norm_eq_norm_sh, e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h3 h)

end Near

theorem fixed_unique {f : ℕ} (hf : 0 < f) {x y : Tl l} (hx : x ^ l ^ f = x) (hy : y ^ l ^ f = y)
    (h : ‖x - y‖ < 1) : x = y := by
  have h1 : ‖x - y‖ = ‖x - y‖ ^ l ^ f := by rw [← norm_sub_pow, hx, hy]
  have hq : 1 < l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have := pow_lt_self_of_lt_one₀ hpos h hq
  linarith

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem ptCoord_ptChart (x : MP ℤ m n) (k : Fin (m + 1)) : ptCoord x ⟨k, ptChart x k⟩ = 1 := by
  simp [ptCoord]

theorem isMultiProjPrime_ptIdeal (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) :
    Geo.IsMultiProjPrime (ptIdeal x) :=
  ⟨RingHom.ker_isPrime _, GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal (ptCoord x),
    GroundTheory.Heights₂.Heights.CoordinateConeArithVar.relevant (ptCoord x) (ptChart x) fun k => by
      rw [ptCoord_ptChart]; exact one_ne_zero⟩

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProdNormPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PullRep

def plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U) :
    Γ(X, U)ˣ →* Γ(Y, W)ˣ := (res h).comp (pullU f U)

theorem res_plU {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {W V : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (l : V ≤ W) (x : Γ(X, U)ˣ) : res l (plU f h x) = plU f (l.trans h) x :=
  Units.ext (resG_appLE f h l (x : Γ(X, U)))

theorem plU_res {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens} (l : U' ≤ U)
    (h : W ≤ f ⁻¹ᵁ U') (x : Γ(X, U)ˣ) : plU f h (res l x) = plU f (h.trans (f.preimage_mono l)) x :=
  Units.ext (appLE_resG f l h (x : Γ(X, U)))

theorem plU_plU {X Y Z : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {W : Z.Opens}
    (h : V ≤ f ⁻¹ᵁ U) (h' : W ≤ g ⁻¹ᵁ V) (x : Γ(X, U)ˣ) :
    plU g h' (plU f h x) = plU (g ≫ f) (h'.trans (g.preimage_mono h)) x :=
  Units.ext (appLE_appLE g f h h' (x : Γ(X, U)))

theorem lbPull_g {X Y : Scheme.{0}} (B : LB X) (f : Y ⟶ X) (i j : PUnit → B.ι) :
    (B.pull f).g i j = plU f (le_inf (inf_le_left.trans (LB.wchart_le B (fun _ => f) i PUnit.unit))
      (inf_le_right.trans (LB.wchart_le B (fun _ => f) j PUnit.unit)) :
        (B.pull f).U i ⊓ (B.pull f).U j ≤ f ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (j PUnit.unit)))
      (B.g (i PUnit.unit) (j PUnit.unit)) := by
  show ∏ k : PUnit, (plU f _ (B.g (i k) (j k))) ^ ((fun _ => (1 : ℤ)) k) = _
  rw [Fintype.prod_unique]
  exact zpow_one _

variable {n' m : ℕ} {n : Fin (m + 1) → ℕ}

abbrev qq (n' m : ℕ) (n : Fin (m + 1) → ℕ) : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n

theorem qq_str (n' m : ℕ) (n : Fin (m + 1) → ℕ) : qq n' m n ≫ mpStr ℤ m n = mpStr ℤ (m + 1) (consN n' n) :=
  qpSnd_str n' m n

def tl (c : ∀ k, Bk (consN n' n) k) : ∀ k, Bk n k := fun k => c k.succ

theorem mchart_le_pull (c : ∀ k, Bk (consN n' n) k) :
    mchart c ≤ qq n' m n ⁻¹ᵁ mchart (tl c) :=
  fun _ hx => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k.succ

theorem pullDeg_zero (a : Fin (m + 1) → ℤ) : pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a 0 = 0 := by
  unfold pullDeg
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨k, hk⟩
    exact Fin.succ_ne_zero k hk

theorem pullDeg_succ (a : Fin (m + 1) → ℤ) (k : Fin (m + 1)) :
    pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k.succ = a k :=
  (Fin.succ_injective _).extend_apply _ _ _

theorem blockUnit_succ {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {W₀ : (MP ℤ m n).Opens} (h : W ≤ prB (consN n' n) k.succ ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (H : W ≤ qq n' m n ⁻¹ᵁ W₀) (h₀ : W₀ ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    blockUnit (n := consN n' n) (k := k.succ) i j h = plU (qq n' m n) H (blockUnit i j h₀) :=
  (plU_plU (qq n' m n) (prB n k) h₀ H _).symm

theorem prod_blockUnit (c c' : ∀ k, Bk (consN n' n) k) {W : (MP ℤ (m + 1) (consN n' n)).Opens}
    {V : (MP ℤ m n).Opens} (HV : W ≤ qq n' m n ⁻¹ᵁ V) (hW : W ≤ mchart c ⊓ mchart c')
    (hV : V ≤ mchart (tl c) ⊓ mchart (tl c')) (a : Fin (m + 1) → ℤ) :
    ∏ k, blockUnit (c k) (c' k) (fun _ hx => ⟨mchart_le c k (hW hx).1, mchart_le c' k (hW hx).2⟩ :
        W ≤ prB (consN n' n) k ⁻¹ᵁ (chart ℤ (consN n' n k) (c k) ⊓ chart ℤ (consN n' n k) (c' k))) ^
          pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      plU (qq n' m n) HV (∏ k, blockUnit (tl c k) (tl c' k)
        (fun _ hx => ⟨mchart_le (tl c) k (hV hx).1, mchart_le (tl c') k (hV hx).2⟩ :
          V ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) (tl c k) ⊓ chart ℤ (n k) (tl c' k))) ^ a k) := by
  rw [map_prod, Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, pullDeg_succ]
  exact congrArg (· ^ a k) (blockUnit_succ _ _ _ HV _)

theorem prod_norm_pull (z : (Σ k, Bk (consN n' n) k) → ℂ) (c : ∀ k, Bk (consN n' n) k) (a : Fin (m + 1) → ℤ) :
    ∏ k, ‖z ⟨k, c k⟩‖ ^ pullDeg (Fin.succ : Fin (m + 1) → Fin (m + 2)) a k =
      ∏ k, ‖z (sv n' n ⟨k, tl c k⟩)‖ ^ a k := by
  rw [Fin.prod_univ_succ, pullDeg_zero, zpow_zero, one_mul]
  simp only [pullDeg_succ]
  rfl

theorem isUnder_map {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {z' : (Σ k, Bk (consN n' n) k) → ℂ}
    (h : IsUnder y' z') :
    IsUnder (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') (fun p => z' (sv n' n p)) := by
  intro k i
  refine ⟨(h k.succ i).1, fun j hy => ?_⟩
  have e := (h k.succ i).2 j hy
  calc CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j)
        (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y')
      = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          ((qq n' m n).app _ (pullRatio (prB n k) _ i le_rfl j)) y' :=
        (ev_app (qq n' m n) (qq_str n' m n) _ _ y').symm
    _ = CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ (qq n' m n ⁻¹ᵁ blockChart n k i)
          (pullRatio (qq n' m n ≫ prB n k) _ i le_rfl j) y' := by
        rw [Scheme.Hom.app_eq_appLE, appLE_pullRatio]
    _ = _ := e

theorem ev_plU {y' : CxPts (mpStr ℤ (m + 1) (consN n' n)) σ₀} {U : (MP ℤ m n).Opens}
    {W : (MP ℤ (m + 1) (consN n' n)).Opens} (H : W ≤ qq n' m n ⁻¹ᵁ U)
    (hy : y' ∈ ptsIn (mpStr ℤ (m + 1) (consN n' n)) σ₀ W) (x : Γ(MP ℤ m n, U)ˣ) :
    CxPts.ev (mpStr ℤ (m + 1) (consN n' n)) σ₀ W (plU (qq n' m n) H x : Γ(MP ℤ (m + 1) (consN n' n), W)) y' =
      CxPts.ev (mpStr ℤ m n) σ₀ U (x : Γ(MP ℤ m n, U)) (Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y') :=
  (ev_res H hy _).trans (ev_app (qq n' m n) (qq_str n' m n) U _ y')

end GlobalTheory.CompanionTheory.MPDict.PullRep

namespace GlobalTheory.CompanionTheory.MPDict

open GlobalTheory.CompanionTheory.MPDict.PullRep

theorem isHermRep_pull (n' m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n))
    (hM : IsHermRep M A) :
    IsHermRep (m := m + 1) (n := consN n' n) (M.pull (qpSnd n' m n) (qpSnd_str n' m n)) (pullLine n' A) := by
  show IsHermRep (M.pull (qq n' m n) (qq_str n' m n)) (pullLine n' A)
  obtain ⟨u, h1, h2, h3⟩ := hM
  have Hu : ∀ (i : PUnit → M.B.ι) (c : ∀ k, Bk (consN n' n) k),
      (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓ mchart c ≤
        qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) := fun i c x hx =>
    ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2⟩
  refine ⟨fun i c => plU (qq n' m n) (Hu i c) (u (i PUnit.unit) (tl c)), ?_, ?_, ?_⟩
  · intro i j c
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (M.pull (qq n' m n) (qq_str n' m n)).B.U j ⊓ mchart c ≤
          qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ M.B.U (j PUnit.unit) ⊓ mchart (tl c)) := fun x hx =>
      ⟨⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1.1,
        LB.wchart_le M.B (fun _ => qq n' m n) j PUnit.unit hx.1.2⟩, mchart_le_pull c hx.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h1 (i PUnit.unit) (j PUnit.unit) (tl c))
    rw [map_mul, plU_res, plU_res, plU_res] at e
    exact (res_plU _ _ _ _).trans (e.trans (congrArg₂ (· * ·)
      ((congrArg (Semi.res _) (lbPull_g M.B (qq n' m n) i j)).trans (res_plU _ _ _ _)).symm
      (res_plU _ _ _ _).symm))
  · intro i c c'
    have HV : (M.pull (qq n' m n) (qq_str n' m n)).B.U i ⊓
        (mchart c ⊓ mchart c') ≤ qq n' m n ⁻¹ᵁ (M.B.U (i PUnit.unit) ⊓ (mchart (tl c) ⊓ mchart (tl c'))) :=
      fun x hx => ⟨LB.wchart_le M.B (fun _ => qq n' m n) i PUnit.unit hx.1, mchart_le_pull c hx.2.1,
        mchart_le_pull c' hx.2.2⟩
    have e := congrArg (plU (qq n' m n) HV) (h2 (i PUnit.unit) (tl c) (tl c'))
    rw [map_mul, plU_res, plU_res] at e
    rw [res_plU, res_plU]
    refine e.trans (congrArg₂ (· * ·) rfl ?_)
    exact (prod_blockUnit c c' HV (fun _ hx => hx.2) (fun _ hx => hx.2) A.a).symm
  · intro i c y z hz hy
    have hy0 : Points.PtsOver.map (qq n' m n) (qq_str n' m n) _ y ∈
        ptsIn (mpStr ℤ m n) σ₀ (M.B.U (i PUnit.unit) ⊓ mchart (tl c)) :=
      Points.le_preimage_comp y.1 (qq n' m n) (Hu i c) hy
    have e := h3 (i PUnit.unit) (tl c) _ _ (isUnder_map hz) hy0
    have ev_e := ev_plU (Hu i c) hy (u (i PUnit.unit) (tl c))
    have φ_e := (M.φ σ₀).pull_φ (qq n' m n) (qq_str n' m n) i y
    show A.h (fun p => z (sv n' n p)) = _
    rw [e]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_pull z c A.a).symm ?_) ?_
    · exact congrArg (‖·‖) ev_e.symm
    · exact congrArg (fun t => Real.exp (t / 2)) φ_e.symm

end GlobalTheory.CompanionTheory.MPDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductPreservesSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenMulti

theorem multiProd_isSubquotient_of_forall (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {d : ℕ} (N : Fin d → ℕ) (M : ℕ) (hM : ∑ i, N i = M)
    (X Y : Fin d → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
    (ρ : ∀ i, Representation ℂ (GL (Fin (N i)) k) (X i))
    (ρ' : ∀ i, Representation ℂ (GL (Fin (N i)) k) (Y i))
    (hs : ∀ i, IsSmooth (ρ' i)) (hq : ∀ i, IsSubquotient (ρ i) (ρ' i)) :
    IsSubquotient (multiProd (stdBlocks N hM) ρ) (multiProd (stdBlocks N hM) ρ') :=
  GlobalTheory.ParIndSubquot.parInd_isSubquotient k _ _ _ (GlobalTheory.SmGL.stdBlocks N hM) _ _ _ _
    (GlobalTheory.SmGL.isSmooth_piTensor hs)
    (GlobalTheory.piTensor_isSubquotient_of_forall _ _ X Y ρ ρ' hq)

end GlobalTheory.CompanionTheory.GenMulti
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRatioTopEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Unique

theorem pullRatio_top_eq {N : ℕ} {x x' : Sp ℂ ⟶ PSpace ℤ N} (i j : Fin (N + 1))
    (h : ⊤ ≤ x ⁻¹ᵁ chart ℤ N i) (h' : ⊤ ≤ x' ⁻¹ᵁ chart ℤ N i)
    (e : valR x (chart ℤ N i) (ratio ℤ N i j) = valR x' (chart ℤ N i) (ratio ℤ N i j)) :
    pullRatio x ⊤ i h j = pullRatio x' ⊤ i h' j := by
  rw [valR, valR, dite_eq_left h, dite_eq_left h'] at e
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 e

theorem valR_comp_prB {m : ℕ} {n : Fin (m + 1) → ℕ} (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) =
      valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dite_eq_left h, dite_eq_left h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

end GlobalTheory.CompanionTheory.MPDict.Unique


open GlobalTheory.CompanionTheory.MPDict.Unique in
theorem GlobalTheory.CompanionTheory.MPDict.isUnder_unique : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ)
    (y y' : CxPts (mpStr ℤ m n) σ₀), IsUnder y z → IsUnder y' z → y = y' := by
  intro m n z y y' h h'
  refine Subtype.ext (GroundTheory.Arith.SchemeCoh.ProjSpace.hom_ext m n _ _ fun k => ?_)
  have hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (ptChart (y.1 (IsLocalRing.closedPoint ℂ)) k)) :=
    mem_ptsIn.2 (mem_ptChart _ k)
  obtain ⟨i, hi⟩ : ∃ i, y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ⟨_, hy⟩
  have hz : z ⟨k, i⟩ ≠ 0 := ((h k i).1).1 hi
  have hi' : y' ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k i) := ((h' k i).1).2 hz
  refine GlobalTheory.ProjSpace.hom_ext ?_ fun t => ⟨⊤, trivial, i, hi, hi', fun j => ?_⟩
  · have s : pr ℤ m n k ≫ PSpace.str ℤ (n k) = mpStr ℤ m n := pr_toSpecBase ℤ m n k
    rw [Category.assoc, Category.assoc, s, y.2, y'.2]
  · have a : ⊤ ≤ y.1 ⁻¹ᵁ blockChart n k i := hi
    have a' : ⊤ ≤ y'.1 ⁻¹ᵁ blockChart n k i := hi'
    refine pullRatio_top_eq (x := y.1 ≫ prB n k) (x' := y'.1 ≫ prB n k) i j a a' ?_
    rw [valR_comp_prB y.1 i j a, valR_comp_prB y'.1 i j a']
    exact ((h k i).2 j hi).trans ((h' k i).2 j hi').symm
end
end

