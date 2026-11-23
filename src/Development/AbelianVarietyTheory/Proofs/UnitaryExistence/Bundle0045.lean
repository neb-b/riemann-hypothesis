module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TateIsoExistsLiftOfTwoData
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D D' : Datum H} {k : Type} [Field k]
  {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem tateIso_ev_eq_iff_add (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a b : D.La) :
    I.ev n a = I.ev n b ↔ ∃ c, a = b + n • c := by
  rw [tateIso_ev_eq_iff I hn]
  exact exists_congr fun c => sub_eq_iff_eq_add'

theorem tateIso_exists_lift_of_two_data (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) {n : ℕ} (hn : 0 < n) :
    ∃ f : D.La →ₗ[𝓞 E] D'.La, ∀ a, I.ev n a = I'.ev n (f a) := by
  let R : Submodule (𝓞 E) (D.La × D'.La) :=
    { carrier := {p | I.ev n p.1 = I'.ev n p.2}
      add_mem' := fun {p q} hp hq => by
        change I.ev n (p.1 + q.1) = I'.ev n (p.2 + q.2)
        rw [I.add, I'.add, show I.ev n p.1 = I'.ev n p.2 from hp, show I.ev n q.1 = I'.ev n q.2 from hq]
      zero_mem' := by
        change I.ev n 0 = I'.ev n 0
        rw [(I.ker n hn 0).2 ⟨0, by simp⟩, (I'.ker n hn 0).2 ⟨0, by simp⟩]
      smul_mem' := fun c p hp => by
        change I.ev n (c • p.1) = I'.ev n (c • p.2)
        rw [I.lin, I'.lin, show I.ev n p.1 = I'.ev n p.2 from hp] }
  have hs : Function.Surjective ((LinearMap.fst (𝓞 E) D.La D'.La).comp R.subtype) := fun a => by
    obtain ⟨b, hb⟩ := (I'.onto n hn _).1 (tateIso_ev_pow I hn a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  haveI := D.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hs
  refine ⟨((LinearMap.snd (𝓞 E) D.La D'.La).comp R.subtype).comp s, fun a => ?_⟩
  have h1 : (s a).1.1 = a := LinearMap.congr_fun hs a
  have h2 : I.ev n (s a).1.1 = I'.ev n (s a).1.2 := (s a).2
  rw [h1] at h2
  exact h2

theorem tateIso_similar_of_two_data
    (he : ∀ n x y c c', e n x y c → e n x y c' → c = c') (I : TateIso D k Q act e) (I' : TateIso D' k Q act e) :
    ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ),
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧
      (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧
      ∀ n : ℕ, 0 < n → ∀ a, I.ev n a = I'.ev n (f n a) := by
  have h1 : ∀ n : ℕ, ∃ f : D.La →ₗ[𝓞 E] D'.La, 0 < n → ∀ a, I.ev n a = I'.ev n (f a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · exact ⟨0, fun h' => absurd h h'.ne'⟩
    · obtain ⟨f, hf⟩ := tateIso_exists_lift_of_two_data I I' h
      exact ⟨f, fun _ => hf⟩
  have h2 : ∀ n : ℕ, ∃ ν : ℕ, 0 < n → I.ζ n = I'.ζ n ^ ν := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | hn
    · exact ⟨1, fun h' => absurd h h'.ne'⟩
    · haveI : NeZero n := ⟨hn.ne'⟩
      obtain ⟨i, -, hi⟩ := (I'.ζ_prim n hn).eq_pow_of_mem_rootsOfUnity
        ((mem_rootsOfUnity _ _).2 (I.ζ_prim n hn).pow_eq_one)
      exact ⟨i, fun _ => hi.symm⟩
  choose f hf using h1
  choose ν hν using h2
  refine ⟨f, fun n => ν n, ?_, ?_, ?_, ?_, ?_, hf⟩
  · intro n m hn hm a
    rw [← tateIso_ev_eq_iff_add I' hn, ← hf n hn, ← I'.tower n m hn hm, ← hf (n * m) (Nat.mul_pos hn hm),
      I.tower n m hn hm]
  · intro n hn
    refine ⟨fun a => ?_, fun a' => ?_⟩
    · rw [← I'.ker n hn, ← I.ker n hn, hf n hn]
    · obtain ⟨a, ha⟩ := (I.onto n hn _).1 (tateIso_ev_pow I' hn a')
      rw [hf n hn] at ha
      exact ⟨a, (tateIso_ev_eq_iff_add I' hn _ _).1 ha.symm⟩
  · intro n hn
    have h := I.ζ_prim n hn
    rw [hν n hn] at h
    exact Nat.isCoprime_iff_coprime.2 (((I'.ζ_prim n hn).pow_iff_coprime hn _).1 h)
  · intro n m hn hm
    have h : I'.ζ n ^ ν (n * m) = I'.ζ n ^ ν n := by
      rw [← hν n hn, ← I.ζ_pow n m hn hm, hν (n * m) (Nat.mul_pos hn hm), ← I'.ζ_pow n m hn hm, ← pow_mul,
        ← pow_mul, mul_comm m]
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, zpow_natCast, zpow_natCast, h, mul_inv_cancel]
  · intro n hn a b
    have e1 := I'.isom n hn (f n a) (f n b)
    have e2 := I.isom n hn a b
    rw [hf n hn a, hf n hn b] at e2
    have h := he n _ _ _ _ e1 e2
    rw [hν n hn, ← zpow_natCast, ← zpow_mul] at h
    rw [← (I'.ζ_prim n hn).zpow_eq_one_iff_dvd, zpow_sub, h, mul_inv_cancel]

end

noncomputable def expNegUnit (n : ℕ) : ℂˣ :=
  (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I / n)) (Complex.exp_ne_zero _))⁻¹

theorem expNegUnit_zpow_val (n : ℕ) (j : ℤ) :
    ((expNegUnit n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, expNegUnit, Units.val_inv_eq_inv_val, Units.val_mk0, ← Complex.exp_neg,
    ← Complex.exp_int_mul]
  congr 1
  ring

theorem expNegUnit_isPrimitiveRoot {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (expNegUnit n) n :=
  (IsPrimitiveRoot.coe_units_iff.1 (Complex.isPrimitiveRoot_exp n hn.ne')).inv

theorem expNegUnit_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : expNegUnit (n * m) ^ m = expNegUnit n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [← zpow_natCast, expNegUnit_zpow_val, ← zpow_one (expNegUnit n), expNegUnit_zpow_val]
  congr 1
  push_cast
  field_simp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (U : FamilyUnif Xo σ ty) {i : Fin U.n}
  {P : (U.Di i).La →+ (Fin g → ℂ)}

theorem familyUnif_ex_nsmul (hP : IsPeriod (U.Di i) ty P) (n : ℕ) (z : Fin g → ℂ) :
    U.ex i P ((n : ℂ) • z) = U.ex i P z ^ n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_smul, pow_zero]
    exact (U.ex_ker i P hP 0).2 (zero_mem _)
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, U.ex_add i P hP, ih, pow_succ]

noncomputable def familyUnifTateIso (hP : IsPeriod (U.Di i) ty P) :
    TateIso (U.Di i) ℂ (Over.mk (U.u i P) ⟶ Xo.univ.t.G) (fun a x => x ≫ Xo.univ.t.act.act a)
      (fun n x x' c => Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L n x x' (unitOn c)) where
  ζ := expNegUnit
  ζ_prim _ hn := expNegUnit_isPrimitiveRoot hn
  ζ_pow _ _ hn hm := expNegUnit_mul_pow hn hm
  ev n a := U.ex i P ((n : ℂ)⁻¹ • P a)
  add n a b := by rw [map_add (f := _), smul_add, U.ex_add i P hP]
  lin n c a := by
    rw [← U.ex_lin i P hP]
    congr 1
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, hP.1 c a k]
    exact mul_left_comm _ _ _
  ker n hn a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    rw [U.ex_ker i P hP]
    refine exists_congr fun b => ?_
    rw [eq_inv_smul_iff₀ hn', Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.2.1.eq_iff, eq_comm]
  onto n hn x := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    constructor
    · intro hx
      obtain ⟨z, rfl⟩ := U.ex_onto i P hP x
      rw [← familyUnif_ex_nsmul U hP, U.ex_ker i P hP] at hx
      obtain ⟨a, ha⟩ := hx
      exact ⟨a, by rw [ha, inv_smul_smul₀ hn']⟩
    · rintro ⟨a, rfl⟩
      rw [← familyUnif_ex_nsmul U hP, smul_inv_smul₀ hn', U.ex_ker i P hP]
      exact ⟨a, rfl⟩
  tower n m hn hm a := by
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [← familyUnif_ex_nsmul U hP, smul_smul]
    congr 2
    push_cast
    field_simp
  isom n hn a b := U.ex_weil i P hP n a b _ hn (expNegUnit_zpow_val n _)

end

theorem familyUnif_lattice_similar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), IsPeriod (U.Di i) ty P → ∃ (f : ℕ → D.La →ₗ[𝓞 E] (U.Di i).La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → IsCoprime (ν n) (n : ℤ)) ∧ (∀ n m : ℕ, 0 < n → 0 < m → (n : ℤ) ∣ ν (n * m) - ν n) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ (U.Di i).EF (f n a) (f n a') - ν n * D.EF a a') ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, f l.M a = U.t i a + l.M • e) ∧ ∀ a, ∃ e, f l.A a = U.t i a + l.A • e := by
  intro E _ _ _ H D l Xo σ g ty U i P hP
  obtain ⟨-, I, -, hA, hM⟩ := Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)
  obtain ⟨f, ν, h1, h2, h3, h4, h5, h6⟩ := tateIso_similar_of_two_data
    (fun n x y c c' => weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB ℂ _ n x y c c') I (familyUnifTateIso U hP)
  have hM0 : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  refine ⟨f, ν, h1, h2, h3, h4, h5, fun a ha => ?_, fun a => ?_⟩
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) hM0, ← h6 _ hM0, ← hM a ha]
    exact U.ex_eta i P hP a ha
  · rw [← tateIso_ev_eq_iff_add (familyUnifTateIso U hP) l.A_pos, ← h6 _ l.A_pos, ← hA a]
    exact U.ex_etaA i P hP a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitFrameRealUnitaryOrbitGramRigid
section
set_option autoImplicit false

open MeasureTheory Topology Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.PeterssonRigid

theorem conjT_isHermitian {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : M.IsHermitian)
    (x : Matrix (Fin r) (Fin r) ℂ) : (xᵀ * M * x.map (starRingEnd ℂ)).IsHermitian := by
  have h := Matrix.isHermitian_mul_mul_conjTranspose xᵀ hM
  have e : (xᵀ)ᴴ = x.map (starRingEnd ℂ) := by ext a b; rfl
  rwa [e] at h

theorem det_conjT {r : ℕ} {M x : Matrix (Fin r) (Fin r) ℂ} (hM : M.det ≠ 0) (hx : x.det ≠ 0) :
    (xᵀ * M * x.map (starRingEnd ℂ)).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    show x.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix x from rfl, ← RingHom.map_det]
  exact mul_ne_zero (mul_ne_zero hx hM) ((map_ne_zero _).2 hx)

theorem conjT_mul {r : ℕ} (M x y : Matrix (Fin r) (Fin r) ℂ) :
    (x * y)ᵀ * M * (x * y).map (starRingEnd ℂ) = yᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * y.map (starRingEnd ℂ) := by
  rw [Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

theorem conjT_one {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) :
    (1 : Matrix (Fin r) (Fin r) ℂ)ᵀ * M * (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = M := by
  simp

theorem conjT_cancel {r : ℕ} {x : Matrix (Fin r) (Fin r) ℂ} (hx : x.det ≠ 0) (M : Matrix (Fin r) (Fin r) ℂ) :
    (x⁻¹)ᵀ * (xᵀ * M * x.map (starRingEnd ℂ)) * (x⁻¹).map (starRingEnd ℂ) = M := by
  rw [← conjT_mul, Matrix.mul_nonsing_inv _ hx.isUnit, conjT_one]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_Gm_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) : (X.Gm.map τ).IsHermitian := by
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← X.Gm_herm b a]
  exact (IsCMField.complexEmbedding_complexConj E τ _).symm

theorem gram_isHermitian {r : ℕ} (X : Data E r) (τ : E →+* ℂ) (m : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ X.Gm m).IsHermitian := by
  rw [FrameDegreeData.gram_eq]
  exact conjT_isHermitian (map_Gm_isHermitian X τ) m

theorem gram_zero_zero {n : ℕ} (X : Data E (n + 1)) {x : Frame X.Ψ (n + 1)} (hx : x ∈ X.dom) (τ : X.Ψ)
    (h1 : ∀ i, ‖dmin X.Gm x τ i‖ = 1) : gram τ.1 X.Gm (mat x τ) 0 0 = (psgn X.p0 1 : ℂ) := by
  let i : Fin (n + 1 + 1) := ⟨1, by omega⟩
  have e : dmin X.Gm x τ i = gram τ.1 X.Gm (mat x τ) 0 0 := by
    unfold dmin lminor
    exact Matrix.det_fin_one _
  have hp := (hx τ).2 i
  have hn := h1 i
  rw [e] at hp hn
  have hr : (((gram τ.1 X.Gm (mat x τ) 0 0).re : ℝ) : ℂ) = gram τ.1 X.Gm (mat x τ) 0 0 :=
    (gram_isHermitian X τ.1 _).coe_re_apply_self 0
  rw [← hr, Complex.norm_real, Real.norm_eq_abs] at hn
  rw [← hr]
  congr 1
  have ha := GlobalTheory.PeterssonCompare.abs_psgn X.p0 1
  change 0 < psgn X.p0 1 * _ at hp
  rcases (abs_eq zero_le_one).1 ha with h | h <;> rcases (abs_eq zero_le_one).1 hn with h' | h' <;>
    rw [h, h'] at hp <;> first | exact h'.trans h.symm | norm_num at hp

theorem rigid : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Comp : Type) (X : Comp → Data E r) (G : Type) [Group G] (Gi : Subgroup G) (dict : G → Σ k, Frame (X k).Ψ r) (ar : ∀ k, G → (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (J : ∀ k, (X k).Ψ → Matrix (Fin r) (Fin r) ℂ) (x0 : ∀ k, Frame (X k).Ψ r), (∀ k τ, (J k τ).IsHermitian ∧ (J k τ).det ≠ 0) → (∀ k (u : (X k).Ψ → Matrix (Fin r) (Fin r) ℂ), (∀ τ, (u τ)ᵀ * J k τ * (u τ).map (starRingEnd ℂ) = J k τ) → ∃ h ∈ Gi, ∀ τ, ar k h τ = u τ) → (∀ k, x0 k ∈ (X k).dom ∧ ∃ g, dict g = ⟨k, x0 k⟩) → (∀ g, ∀ h ∈ Gi, ∃ γ ∈ (X (dict g).1).Γ, dict (g * h) = ⟨(dict g).1, lact γ (rmul (dict g).2 fun τ => ((mat (x0 (dict g).1) τ)⁻¹ * ar (dict g).1 h τ * mat (x0 (dict g).1) τ : Matrix (Fin r) (Fin r) ℂ))⟩) → (∀ g, (dict g).2 ∈ (X (dict g).1).dom) → (∀ g τ i, ‖dmin (X (dict g).1).Gm (dict g).2 τ i‖ = 1) → (∀ k (τ : (X k).Ψ), ∃ t : ℝ, t ≠ 0 ∧ (X k).Gm.map τ.1 = (t : ℂ) • J k τ) ∧ ∀ g τ, gram τ.1 (X (dict g).1).Gm (mat (dict g).2 τ) = gram τ.1 (X (dict g).1).Gm (mat (x0 (dict g).1) τ) := by
  intro E _ _ _ r Comp X G _ Gi dict ar J x0 hJ hsurj hx0 hmul hdom hunit
  classical
  cases r with
  | zero => exact ⟨fun k τ => ⟨1, one_ne_zero, Subsingleton.elim _ _⟩, fun g τ => Subsingleton.elim _ _⟩
  | succ n =>
  have he : ∀ p : ℕ, (psgn p 1 : ℂ) ≠ 0 := by
    intro p h
    have ha := GlobalTheory.PeterssonCompare.abs_psgn p 1
    rw [Complex.ofReal_eq_zero.1 h] at ha
    norm_num at ha
  have h00 : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ,
      gram τ.1 (X k).Gm (mat x τ) 0 0 = (psgn (X k).p0 1 : ℂ) := by
    intro g k x h τ
    have h1 := hdom g
    have h2 := hunit g
    rw [h] at h1 h2
    exact gram_zero_zero (X k) h1 τ (h2 τ)
  have key : ∀ g k x, dict g = ⟨k, x⟩ → ∀ τ : (X k).Ψ, ∃ t : ℝ, t ≠ 0 ∧
      gram τ.1 (X k).Gm (mat x τ) =
        (t : ℂ) • ((mat (x0 k) τ)ᵀ * J k τ * (mat (x0 k) τ).map (starRingEnd ℂ)) := by
    intro g k x h τ
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    refine GlobalTheory.hermitian_eq_smul_of_const_on_unitary_orbit _ _ _ 0 _ (he (X k).p0) (gram_isHermitian _ _ _) (conjT_isHermitian (hJ k τ).1 _)
      (det_conjT (hJ k τ).2 hd) fun u hu => ?_
    obtain ⟨a, ha, har⟩ := hsurj k (Function.update (fun _ => 1) τ (mat (x0 k) τ * u * (mat (x0 k) τ)⁻¹)) (by
      intro σ
      by_cases hσ : σ = τ
      · subst hσ
        rw [Function.update_self, conjT_mul, conjT_mul, hu, conjT_cancel hd]
      · rw [Function.update_of_ne hσ, conjT_one])
    have hm := hmul g a ha
    rw [h] at hm
    obtain ⟨γ, hγ, hm⟩ := hm
    have h1 := h00 _ _ _ hm τ
    rw [MajInv.gram_lact _ ((X k).Γ_stab γ hγ)] at h1
    have e : mat (rmul x fun τ => ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ :
        Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) τ = mat x τ * u := by
      show mat x τ * ((mat (x0 k) τ)⁻¹ * ar k a τ * mat (x0 k) τ) = _
      rw [har, Function.update_self, Matrix.mul_assoc (mat (x0 k) τ), Matrix.nonsing_inv_mul_cancel_left _ _ hd.isUnit,
        Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit]
    dsimp only at h1
    rw [e, FrameDegreeData.gram_mul] at h1
    exact h1
  refine ⟨fun k τ => ?_, fun g τ => ?_⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    obtain ⟨t, ht, h⟩ := key g k _ hg τ
    refine ⟨t, ht, ?_⟩
    have hd : (mat (x0 k) τ).det ≠ 0 := ((hx0 k).1 τ).1
    rw [← conjT_cancel hd ((X k).Gm.map τ.1), ← FrameDegreeData.gram_eq, h, Matrix.mul_smul, Matrix.smul_mul, conjT_cancel hd]
  · obtain ⟨g', hg'⟩ := (hx0 (dict g).1).2
    obtain ⟨t, -, h⟩ := key g _ _ rfl τ
    obtain ⟨t', -, h'⟩ := key g' _ _ hg' τ
    have a := h00 g _ _ rfl τ
    have a' := h00 g' _ _ hg' τ
    rw [h, Matrix.smul_apply, smul_eq_mul] at a
    rw [h', Matrix.smul_apply, smul_eq_mul] at a'
    have hb : ((mat (x0 (dict g).1) τ)ᵀ * J _ τ * (mat (x0 (dict g).1) τ).map (starRingEnd ℂ)) 0 0 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at a
      exact he _ a.symm
    rw [h, h', mul_right_cancel₀ hb (a.trans a'.symm)]

end GlobalTheory.PeterssonRigid
end

