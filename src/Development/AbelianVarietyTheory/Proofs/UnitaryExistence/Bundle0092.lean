module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyComplex
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CyclotomicCharacterEqCmMultiplierNorm
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.MultiplierNorm

def InOrder (d : ℕ) (z : ℂ) : Prop := ∃ m n : ℤ, z = (m : ℂ) + n * ((1 + Complex.I * Real.sqrt d) / 2)

theorem exists_form_eq_one {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hg : 1 ≤ g)
    (u : HolUnif A L g) (Ef : LinearMap.BilinForm ℤ u.Λ) (hE : Function.Bijective Ef) :
    ∃ a b : u.Λ, Ef a b = 1 := by
  haveI := u.discrete
  haveI : IsZLattice ℝ u.Λ := ⟨u.full⟩
  haveI : Module.Free ℤ u.Λ := ZLattice.module_free ℝ u.Λ
  have hnt : Nontrivial u.Λ := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have hb : u.Λ = ⊥ := Submodule.eq_bot_of_subsingleton
    have := u.full
    rw [hb] at this
    simp only [Submodule.bot_coe, Submodule.span_zero_singleton] at this
    haveI hne : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
    exact bot_ne_top this
  let B := Module.Free.chooseBasis ℤ u.Λ
  obtain ⟨i⟩ := B.index_nonempty
  obtain ⟨a, ha⟩ := hE.2 (B.coord i)
  exact ⟨a, B i, by rw [ha]; simp⟩

theorem ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (n : ℕ) (z : Fin g → ℂ) :
    u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  have h0 : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem hermForm_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b : ℂ) (v : Fin g → ℂ) :
    hermForm Hm (a • v) (b • v) = a * starRingEnd ℂ b * hermForm Hm v v := by
  rw [hermForm, hermForm, smul_dotProduct, star_smul, Matrix.mulVec_smul, dotProduct_smul, RCLike.star_def,
    smul_eq_mul, smul_eq_mul, _root_.mul_assoc]

theorem hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (v : Fin g → ℂ) :
    (hermForm Hm v v).im = 0 := by
  rw [← Complex.conj_eq_iff_im, hermForm, ← RCLike.star_def, ← Matrix.star_dotProduct_star,
    Matrix.star_mulVec, star_star, h.eq, ← Matrix.dotProduct_mulVec]

theorem weilIs_of_quadLattice (P Q : Out.PolAV (Sp ℂ)) (hP : P.g = 1) (hQ : Q.g = 1) (u : HolUnif P.A P.L P.g)
    {d : ℕ} (hd : 0 < d) {c : ℂ} (hc : c ≠ 0) (hΛ : IsQuadLattice u.Λ d c) (f : P.A ⟶ Q.A) (hf : IsMonHom f)
    (hinj : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ P.A, x ≫ f = 1 → x = 1) {α β : ℂ} (hα : InOrder d α) (hβ : InOrder d β)
    {e : ℤ} (he : (e : ℝ) * (√d / 2) = (α * starRingEnd ℂ β).im) {n : ℕ} (hn : 0 < n) (ζ : ℂˣ)
    (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (e : ℂ) / n)) :
    Out.WeilIs Q.A Q.L n (u.ex (fun _ => c * (α / n)) ≫ f) (u.ex (fun _ => c * (β / n)) ≫ f) (unitOn ζ) := by
  obtain ⟨rig, hr⟩ := Q.rigid
  obtain ⟨u₁, Hm, χ, Ef, hAH, -, -, -, -, -, hIm, hE, hw⟩ := thetaUnifAV_all Q rig hr
  obtain ⟨F, hF⟩ := exists_linear_lift_of_isMonHom_polAV P Q _ _ u u₁ f hf
  have hd' : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  let i₀ : Fin P.g := ⟨0, by omega⟩
  let v : Fin Q.g → ℂ := F fun _ => c
  have hv : ∀ z : ℂ, z • v = F fun _ => c * z := fun z => by
    rw [← map_smul]; congr 1; funext _; simp [_root_.mul_comm]
  have mem : ∀ z : ℂ, z • v ∈ u₁.Λ ↔ InOrder d z := fun z => by
    rw [← u₁.ker, hv, hF]
    constructor
    · intro h
      obtain ⟨m, k, h'⟩ := (hΛ _).1 ((u.ker _).1 (hinj _ h))
      exact ⟨m, k, mul_left_cancel₀ hc (congrFun h' i₀)⟩
    · rintro ⟨m, k, rfl⟩
      rw [(u.ker _).2 ((hΛ _).2 ⟨m, k, rfl⟩), MonObj.one_comp]
  have v0 : v ≠ 0 := fun h => by
    obtain ⟨m, k, h'⟩ := (mem (1 / 2)).1 (by rw [h, smul_zero]; exact u₁.Λ.zero_mem)
    have h1 := congrArg Complex.im h'
    have h2 := congrArg Complex.re h'
    simp at h1 h2
    have hk : k = 0 := by
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hd.ne'
    subst hk
    have h3 : ((2 * m : ℤ) : ℝ) = (1 : ℤ) := by push_cast at h2 ⊢; linarith
    have := Int.cast_injective h3
    omega
  have span : ∀ l : Fin Q.g → ℂ, ∃ z : ℂ, l = z • v := fun l => by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 v0
    refine ⟨l j / v j, funext fun i => ?_⟩
    have : i = j := Fin.ext (by omega)
    subst this
    simp only [Pi.zero_apply] at hj
    simp [hj]
  have hpos : 0 < (hermForm Hm v v).re := hAH.2.1 v v0
  have val : ∀ (a b : ℂ) (ha : a • v ∈ u₁.Λ) (hb : b • v ∈ u₁.Λ),
      (Ef ⟨_, ha⟩ ⟨_, hb⟩ : ℝ) = (a * starRingEnd ℂ b).im * (hermForm Hm v v).re := fun a b ha hb => by
    rw [hIm, hermForm_smul, Complex.mul_im, hermForm_self_im hAH.1, mul_zero, zero_add]
  have one : √d / 2 * (hermForm Hm v v).re = 1 := by
    have ha₀ := (mem _).2 ⟨0, 1, rfl⟩
    have hb₀ := (mem _).2 ⟨1, 0, rfl⟩
    have h₀ : (Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ : ℝ) = √d / 2 * (hermForm Hm v v).re := by
      rw [val]; simp
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_form_eq_one hQ.ge u₁ Ef hE
    obtain ⟨a, rfl⟩ := span a
    obtain ⟨b, rfl⟩ := span b
    obtain ⟨m, k, rfl⟩ := (mem a).1 ha
    obtain ⟨m', k', rfl⟩ := (mem b).1 hb
    have hdvd : Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ ∣ 1 := by
      refine ⟨k * m' - m * k', Int.cast_injective (α := ℝ) ?_⟩
      rw [Int.cast_mul, h₀, ← hab, val]
      simp [map_ofNat]
      ring
    have hp : 0 < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by
      have : (0 : ℝ) < Ef ⟨_, ha₀⟩ ⟨_, hb₀⟩ := by rw [h₀]; positivity
      exact_mod_cast this
    rw [← h₀, Int.eq_one_of_dvd_one hp.le hdvd, Int.cast_one]
  have hEe : Ef ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ = e := Int.cast_injective (α := ℝ) (by
    rw [val, ← he, _root_.mul_assoc, one, _root_.mul_one])
  have H := hw n ⟨_, (mem _).2 hα⟩ ⟨_, (mem _).2 hβ⟩ ζ hn (by rw [hEe, hζ])
  have sc : ∀ a : ℂ, u₁.ex ((n : ℂ)⁻¹ • a • v) = u.ex (fun _ => c * (a / n)) ≫ f := fun a => by
    rw [smul_smul, hv, hF, ← div_eq_inv_mul]
  rw [← sc, ← sc]
  exact H

def pullPol {R R' : Type} [CommRing R] [CommRing R'] (P : Out.PolAV (Sp R)) {s : R →+* R'} {A : Over (Sp R')}
    [GrpObj A] {φ : A.left ⟶ P.A.left} (h : IsGrpPullback A P.A (spMap s) φ) : Out.PolAV (Sp R') :=
  have hL := pull_isLB P.isLB φ
  have H := pol_pull _ _ P.A A _ φ P.L _ P.isLB hL P.isAb h (PolBaseChange.lbIso_refl hL)
  { A := A, isAb := H.1, g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull φ, isLB := hL, rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym, ample := H.2.1 P.ample, ktriv := H.2.2 P.ktriv }

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cmHost_rootComplex_eq_pm_sqrt (H : Host E) : H.rt0 = Complex.I * Real.sqrt H.d ∨ H.rt0 = -(Complex.I * Real.sqrt H.d) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.1
  rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  simp

theorem inOrder_wC (H : Host E) (a : ℤ × ℤ) : InOrder H.d (wC H a) := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem four_mul_div (H : Host E) : (4 : ℂ) * ((((H.d : ℤ) + 1) / 4 : ℤ) : ℂ) = H.d + 1 := by
  have := H.d_mod
  have h : (4 : ℤ) * (((H.d : ℤ) + 1) / 4) = H.d + 1 := by omega
  exact_mod_cast congrArg (Int.cast : ℤ → ℂ) h

theorem wC_mul (H : Host E) (s a : ℤ × ℤ) : ∃ b, wC H s * wC H a = wC H b := by
  refine ⟨(s.1 * a.1 - s.2 * a.2 * (((H.d : ℤ) + 1) / 4), s.1 * a.2 + s.2 * a.1 + s.2 * a.2), ?_⟩
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_sub, Int.cast_mul, Int.cast_add]
  linear_combination (s.2 * a.2 / 4 : ℂ) * h + (s.2 * a.2 / 4 : ℂ) * h'

theorem wC_norm (H : Host E) (s : ℤ × ℤ) : wC H s * starRingEnd ℂ (wC H s) =
    ((s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) : ℤ) : ℂ) := by
  have hc : starRingEnd ℂ H.rt0 = -H.rt0 := by
    rcases cmHost_rootComplex_eq_pm_sqrt H with h | h <;> rw [h] <;> simp
  have h := four_mul_div H
  have h' := H.sqrt_neg_disc_sq
  simp only [wC, Int.cast_pow, Int.cast_mul, Int.cast_add, map_add (f := _), map_mul, map_div₀, map_intCast, map_one,
    map_ofNat, hc]
  linear_combination (-s.2 ^ 2 / 4 : ℂ) * h - (s.2 ^ 2 / 4 : ℂ) * h'

theorem exists_pair (H : Host E) :
    ∃ a b, ((-1 : ℤ) : ℝ) * (√H.d / 2) = (wC H a * starRingEnd ℂ (wC H b)).im := by
  rcases cmHost_rootComplex_eq_pm_sqrt H with h | h
  · exact ⟨(1, 0), (0, 1), by simp [wC, h, map_ofNat]; ring⟩
  · exact ⟨(0, 1), (1, 0), by simp [wC, h]; ring⟩

theorem map_zeta_eq_zpow_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (io : C.P.A.left ⟶ C.P.A.left) (n : ℕ) (s : ℤ × ℤ), 0 < n → C.ActsBy τ io n s → τ (zeta n) = zeta n ^ (s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4)) := by
  intro E _ _ _ H C τ _ io n s hn ⟨hp, hact⟩
  have hL := firstFiveLaws.1
  have hd := H.d_prime.pos
  obtain ⟨a, b, hab⟩ := exists_pair H
  set N : ℤ := s.1 ^ 2 + s.1 * s.2 + s.2 ^ 2 * (((H.d : ℤ) + 1) / 4) with hN
  let Q := pullPol C.P hp
  let ζ : ℂˣ := Units.mk0 (zeta n) (Complex.exp_ne_zero _)
  have hs : ∀ a, InOrder H.d (wC H s * wC H a) := fun a => by
    obtain ⟨b, hb⟩ := wC_mul H s a
    rw [hb]; exact inOrder_wC H b
  have W₀ := weilIs_of_quadLattice C.P C.P C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 _) inferInstance
    (fun x hx => by rwa [Category.comp_id] at hx) (inOrder_wC H a) (inOrder_wC H b) hab hn ζ
    (by simp [ζ, zeta])
  have W₁ := weilIs_of_quadLattice C.P Q C.g_eq C.g_eq C.u hd C.c_ne C.lat (𝟙 C.P.A)
    (inferInstanceAs (IsMonHom (𝟙 C.P.A)))
    (fun x hx => (Category.comp_id x).symm.trans hx) (hs a) (hs b) (e := -N) (by
      have e : wC H s * wC H a * starRingEnd ℂ (wC H s * wC H b) = (N : ℝ) * (wC H a * starRingEnd ℂ (wC H b)) := by
        rw [Complex.ofReal_intCast, hN, ← wC_norm, map_mul]; ring
      rw [e, Complex.im_ofReal_mul, ← hab]
      push_cast; ring) hn (ζ ^ N) (by
      rw [Units.val_zpow_eq_zpow_val]
      show zeta n ^ N = _
      rw [zeta, ← Complex.exp_int_mul]
      congr 1
      push_cast; ring)
  rw [Category.comp_id, Category.comp_id] at W₀
  have tor : ∀ z, InOrder H.d z → (C.u.ex fun _ => C.c * (z / n)) ^ n = 1 := by
    rintro z ⟨m, k, hz⟩
    rw [ex_pow, C.u.ker]
    refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
    have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [← hz, Pi.smul_apply, smul_eq_mul]
    field_simp
  obtain ⟨r, hr, ⟨cub⟩⟩ := PolAV_exists_cubical hL.cube Q
  obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl Q.isLB
  have := Q.isAb.comm
  have W₂ := WeilCube.weilIs_pull cub hL.globalFns Q.isAb C.P.isLB hp w hw (T := 𝟙_ _) (T₀ := 𝟙_ _)
    (spMap (τ : ℂ →+* ℂ)) (by simp) (tor _ (hs a)) (tor _ (hs b)) (hact a).symm (hact b).symm W₀
  obtain ⟨c₀, -, hc₀⟩ := (hL.weil _ Q n _).1 _ _ (tor _ (hs a)) (tor _ (hs b))
  have W₁' : Out.WeilIs Q.A Q.L n (C.u.ex fun _ => C.c * (wC H s * wC H a / n))
      (C.u.ex fun _ => C.c * (wC H s * wC H b / n)) (unitOn (ζ ^ N)) := by
    have e₁ : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ C.P.A, x ≫ 𝟙 C.P.A = x := fun x => Category.comp_id x
    erw [e₁, e₁] at W₁
    exact W₁
  have e := (hc₀ _ W₂).trans (hc₀ _ W₁').symm
  have e' : unitOn (Units.map (τ : ℂ →+* ℂ).toMonoidHom ζ) = unitOn (ζ ^ N) := by
    refine Eq.trans (Units.ext ?_) e
    exact congrArg (fun q => q.hom (ζ : ℂ)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : ℂ →+* ℂ)))
  have e'' := congrArg Units.val (H1.unitOn_injective e')
  rw [Units.val_zpow_eq_zpow_val] at e''
  exact e''

end GlobalTheory.MultiplierNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCharacter
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RootOfUnityFn

theorem evR_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (m : ℕ) :
    evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact evalAt_one _ _ y h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact evalAt_mul _ _ _ _ y

theorem exists_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n) (m : ℕ), 0 < m → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → d.cδ ^ m = 1 → (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) → ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false := by
  intro E _ _ _ H Dw l Xo c n d m hm hsec hpow hval
  choose a ha using hval
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : IsReduced (CAt d.c₂.F.val.toRingHom) := (inferInstance : IsReduced ℂ)
  have hinj : Function.Injective (algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)) :=
    (d.c₂.F.val.toRingHom).injective
  have hroot : ∀ y, a y ^ m = 1 := by
    intro y
    have hT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y
    have h1 := evR_pow d.Xo₂ d.c₂ d.cδ y hT m
    have h0 := evR_pow d.Xo₂ d.c₂ d.cδ y hT 0
    rw [pow_zero, pow_zero] at h0
    rw [hpow, h0, ha, ← map_pow] at h1
    exact hinj (by rw [map_one]; exact h1.symm)
  refine ⟨rootsOfUnity m d.c₂.F, inferInstance, inferInstance, (rootsOfUnity m d.c₂.F).subtype,
    fun y => rootsOfUnity.mkOfPowEq (a y) (hroot y), hsec, fun y => ?_⟩
  rw [ha]
  rfl

end GlobalTheory.RootOfUnityFn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVector
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_hom_of_pureType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmCurveHomOfPureTypeVectorAnyLevel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_hom_of_pureType_of_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ C : Curve H, ∀ (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), ∀ (ε : ℤˣ), ∀ a ∈ lat hP (((ε : ℤ) : ℂ) * H.rt0), ∃ φ : C.P.A.left ⟶ Xo.univ.t.G.left, φ ≫ Xo.univ.t.G.hom = C.P.A.hom ≫ F.u i P ∧ ∀ z : ℂ, C.pt z ≫ φ = (F.ex i P (z • P a)).left := by
  intro E _ _ _ H D l Xo σ g ty F _ _ _ C i P hP ε a ha
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (F.u i P) Xo.univ.t
  obtain ⟨φ, -, hφ⟩ := exists_isHomFamily_complex thetaUnifAV_closed firstFiveLaws.1.weil F i hP m C.u C.g_eq
    C.theta C.c_ne C.lat (ρ := ((ε : ℤ) : ℂ) * H.rt0) (by
      rw [mul_pow, H.sqrt_neg_disc_sq, ← Int.cast_pow, ← Units.val_pow_eq_pow_val, Int.units_sq]
      simp)
  refine ⟨(φ ⟨a, ha⟩).left ≫ m.φ, ?_, fun z => hφ ⟨a, ha⟩ z⟩
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CurveField

open GlobalTheory.Ex.UnifModel GlobalTheory.Ex.TorsionField

theorem exists_finset_fixed (hM : Out.MulNSt) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (P : Out.PolAV (Sp M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsIntegral ℚ z) ∧ ∀ τ : ℂ →+* ℂ, (∀ x ∈ M, τ x = x) → (∀ z ∈ s, τ z = z) →
      ∀ x : Over.mk (spMap (algebraMap M ℂ)) ⟶ P.A, x ^ n = 1 → spMap τ ≫ x.left = x.left := by
  classical
  let F := algebraicClosure M ℂ
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure M ℂ).isAlgClosed
  obtain ⟨s, hs⟩ := exists_finset (F := F) hM P hn
  refine ⟨s.image Subtype.val, fun z hz => ?_, fun τ h₁ h₂ x hx => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hz
    exact isIntegral_trans (A := M) _ (mem_algebraicClosure_iff'.1 y.2)
  · let k : Subfield F := RingHom.eqLocusField (τ.comp (algebraMap F ℂ)) (algebraMap F ℂ)
    obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hM P (algebraMap M F) (algebraMap F ℂ) (algebraMap M ℂ)
      (fun _ => rfl) hn x hx
    obtain ⟨z, hz⟩ := hs k k.subtype (fun c => ⟨⟨algebraMap M F c, h₁ c c.2⟩, rfl⟩)
      (fun c hc => ⟨⟨c, h₂ c (Finset.mem_image_of_mem _ hc)⟩, rfl⟩) y hy
    have e₁ : spMap (algebraMap F ℂ) ≫ spMap k.subtype = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun _ => rfl
    have e₂ : spMap τ ≫ spMap ((algebraMap F ℂ).comp k.subtype) = spMap ((algebraMap F ℂ).comp k.subtype) :=
      spMap_comp fun c => c.2
    rw [← hy', ← hz, reassoc_of% e₁, reassoc_of% e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_wC_eq (H : Host E) (a : ℤ × ℤ) :
    ∃ m k : ℤ, wC H a = (m : ℂ) + k * ((1 + Complex.I * Real.sqrt H.d) / 2) := by
  have h : H.rt0 ^ 2 = (Complex.I * Real.sqrt H.d) ^ 2 := by
    rw [H.sqrt_neg_disc_sq, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact ⟨a.1, a.2, by rw [wC, h]⟩
  · exact ⟨a.1 + a.2, -a.2, by rw [wC, h]; push_cast; ring⟩

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (z : Fin g → ℂ) (n : ℕ) :
    u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (u.ker 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_pow_eq_one (C : Curve H) {n : ℕ} (hn : 0 < n) (a : ℤ × ℤ) :
    (C.u.ex fun _ => C.c * (wC H a / n)) ^ n = 1 := by
  obtain ⟨m, k, h⟩ := exists_wC_eq H a
  rw [← ex_nsmul, C.u.ker]
  refine (C.lat _).2 ⟨m, k, funext fun _ => ?_⟩
  have : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [← h, Pi.smul_apply, nsmul_eq_mul]
  field_simp

theorem exists_model (H : Host E) : ∃ (M : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ M)
    (P : Out.PolAV (Sp M)) (C : Curve H) (ψ : C.P.A.left ⟶ P.A.left),
    IsGrpPullback C.P.A P.A (spMap (algebraMap M ℂ)) ψ := by
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg (d := H.d) H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, -, ⟨P₀, π, -, -, ⟨hg₀, hπ, hL₀⟩, -⟩, hcm, -⟩ :=
    cmCurve_closed H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := exists_baseChange firstFiveLaws.1.polBaseChange (spMap (algebraMap M ℂ)) P₀
  obtain ⟨u, hu⟩ := exists_isThetaUnif thetaUnifAV_all PC
  have hL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (pull_isLB P₀.isLB ψ) (pull_isLB P.isLB _) hLC
      (LBIso.chartPull (Geo.Tor.chartPullPull P₀.L ψ ψ rfl) (Geo.Tor.chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀.symm)
  obtain ⟨c, hc, hΛ⟩ := hcm PC (ψ ≫ π)
    ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp fun _ => rfl) rfl, hL.symm⟩ u
  rw [hw] at hΛ
  exact ⟨M, inferInstance, P₀, ⟨PC, hgC.trans (hg₀.trans hg), u, hu, c, hc, hΛ⟩, ψ, hψ⟩

theorem exists_curveOver (H : Host E) {n : ℕ} (hn : 0 < n) :
    ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧ CurveOver H F n := by
  obtain ⟨M, _, P, C, ψ, hψ⟩ := exists_model H
  obtain ⟨s, hs, hfix⟩ := exists_finset_fixed firstFiveLaws.1.mulN M P hn
  have := IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := (s : Set ℂ)) hs
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (s : Set ℂ), inferInstance, fun τ hτ => ?_⟩
  have h₁ : ∀ x ∈ M, (τ : ℂ →+* ℂ) x = x := fun x hx => hτ x (le_sup_left (a := M) hx)
  have h₂ : ∀ z ∈ s, (τ : ℂ →+* ℂ) z = z := fun z hz =>
    hτ z (le_sup_right (a := M) (IntermediateField.subset_adjoin ℚ _ hz))
  have e : spMap (τ : ℂ →+* ℂ) ≫ spMap (algebraMap M ℂ) = spMap (algebraMap M ℂ) :=
    spMap_comp fun c => h₁ c c.2
  have w : ψ ≫ P.A.hom = (C.P.A.hom ≫ spMap (τ : ℂ →+* ℂ)) ≫ spMap (algebraMap M ℂ) := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨C, hψ.1.lift _ _ w, hψ.cancel (hψ.congr e.symm (hψ.1.lift_fst _ _ w).symm) (hψ.1.lift_snd _ _ w),
    fun a => ?_⟩
  have h1 : wC H (1, 0) = 1 := by simp [wC]
  rw [h1, _root_.one_mul]
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) (spMap (algebraMap M ℂ)) (Category.id_comp _).symm
  have hx := hfix τ h₁ h₂ (ε (C.u.ex fun _ => C.c * (wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (ex_pow_eq_one C hn a)).trans (map_one ε))
  rw [hε] at hx
  have ho : C.pt (wC H a / n) ≫ C.P.A.hom = 𝟙 _ := Over.w (C.u.ex fun _ => C.c * (wC H a / n))
  refine hψ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hψ.1.lift_fst, Category.assoc]
    exact hx.symm
  · rw [Category.assoc, hψ.1.lift_snd, Category.assoc, ho, reassoc_of% ho, Category.comp_id]

theorem exists_coeff_curveOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (n : ℕ), 0 < n → ∃ c' : Coeff l, c.F ≤ c'.F ∧ ∀ c'' : Coeff l, c'.F ≤ c''.F → CurveOver H c''.F n := by
  intro E _ _ _ H l c n hn
  obtain ⟨F, _, hF⟩ := exists_curveOver H hn
  have := c.fin
  exact ⟨⟨c.F ⊔ F, inferInstance, fun τ a => le_sup_left (b := F) (c.conj τ a), le_sup_left (b := F) c.zeta_mem,
    c.le.trans le_sup_left⟩, le_sup_left, fun c'' h τ hτ => hF τ fun x hx => hτ x (h (le_sup_right (a := c.F) hx))⟩

end GlobalTheory.CurveField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignatureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_scaled_isometry_same_signature : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H), D'.p = D.p → D'.q = D.q → ∀ b : ℕ, 0 < b → ∃ (k : ℕ) (f : D.La →ₗ[𝓞 E] D'.La), k.Coprime b ∧ ∀ x y, D'.EF (f x) (f y) = (k : ℤ) ^ 2 * D.EF x y := by
  first | exact @GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | exact GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry | (intros; apply GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry <;> assumption)
end

