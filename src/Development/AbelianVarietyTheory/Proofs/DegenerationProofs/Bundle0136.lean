module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMonHomOfPG
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNFrame
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch.Wp

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

theorem ex_nsmul (d : Dict N B) (i : ℕ) (z : Fin B.gB → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (d.ab.2.2.1 0).2 (zero_mem _)
  | succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]

theorem cubN_frame (d : Dict N B) (k : ℕ) (x' x : Fin B.gB → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ k ih =>
    have h := d.ab.2.2.2.2.2.1 (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

theorem tk_frame (d : Dict N B) {k : ℕ} (hk : 0 < k) {la la' : B.La} {p p' : N.QT k} (h : d.Rep k la p)
    (h' : d.Rep k la' p') :
    (N.tk p p' : ℂ) * (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) *
        ((d.fr ((k : ℂ)⁻¹ • B.P0 la').2 : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx
  set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'
  have e : k • x' = B.ct la'.y + la'.l := by
    rw [hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  have s := h.2.2 la'.y
  have f1 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)
  have f2 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y)
  rw [AnArc.ah_add, add_right_comm, ← e] at f1
  rw [← e] at f2
  rw [← hx, f1, f2, eTwoPi] at s
  rw [NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']
  have n1 := B.ah_ne_zero la'.l (B.ct la'.y)
  have n2 := (d.fr (k • x')).ne_zero
  have n3 := (d.fr x).ne_zero
  have n4 := (d.fr (k • x' + x)).ne_zero
  have n5 := Complex.exp_ne_zero (Real.pi * B.H x la'.l)
  rw [div_mul_eq_mul_div, eq_div_iff n5]
  apply mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))
  linear_combination (B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) *
    (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s

theorem wp_eq : WpSt := by
  intro O _ _ N B d k hk la la' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := tk_frame d hk h h'
  have b := tk_frame d hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  have E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ) := by
    rw [← B.Ef_eq_im]; simp
  have C := Complex.sub_conj (B.H la.l la'.l)
  rw [B.H_conj] at C
  have key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) *
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la').2 la.l) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd,
      AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]
    push_cast at C ⊢
    rw [E]
    have hI := Complex.I_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * C
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.Ex.Arch.Wp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationIsoCommInducedLabelMaps
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData

theorem eq_zero_of_forall_pow_smul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ} (hn : 1 < n) (v : X)
    (h : ∀ j : ℕ, ∃ z, v = n ^ j • z) : v = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨z, hz⟩ := h (b.repr v i).natAbs
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ((n ^ (b.repr v i).natAbs : ℕ) : ℤ)) ⟨b.repr z i, ?_⟩ ?_
  · have := congrArg (fun w => b.repr w i) hz
    simpa only [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] using this
  · rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hn

theorem exists_qt_image {O : Type} [CommRing O] {N N' : NumD O} (J : NumD.Iso N N') {k : ℕ} (p : N.QT k) :
    ∃ p' : N'.QT k, p'.1.1.toAdd = J.e p.1.1.toAdd ∧ J.Rel p.1.2 p'.1.2 := by
  have t := NumD.hom_transport O O (RingHom.id O) N N' (TateInh.homOfIso J)
  obtain ⟨g, r, hu⟩ := t.1 p.1.2
  have rp : ∀ m, (TateInh.homOfIso J).Rel (p.1.2 ^ m) (g ^ m) := by
    intro m
    induction m with
    | zero =>
      have h := t.2.2.1 0
      simpa [N.io_zero, N'.io_zero] using h
    | succ m ih => simpa [pow_succ] using t.2.1 _ _ _ _ ih r
  have r₂ := rp k
  rw [N.mem_QT.1 p.2] at r₂
  refine ⟨⟨(Multiplicative.ofAdd (J.e p.1.1.toAdd), g), ?_⟩, rfl, r⟩
  exact (t.1 _).unique r₂ (t.2.2.1 _)

theorem iso_comm_of_labels : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), 1 < n → Labels N EF ζ lab → Labels N' EF ζ' lab' → ∀ J : NumD.Iso N N', (∀ j (p : N.QT (n ^ j)) (p' : N'.QT (n ^ j)), p'.1.1.toAdd = J.e p.1.1.toAdd → J.Rel p.1.2 p'.1.2 → ∃ x, N.QEq (lab _ x) p ∧ N'.QEq (lab' _ x) p') → (∀ j (y : N.X), ∃ p : N.QT (n ^ j), p.1.1.toAdd = y) → ∀ (α : N.X →+ N.X) (α' : N'.X →+ N'.X) (gam : La → La), (∀ j x, ∃ z, (lab (n ^ j) (gam x)).1.1.toAdd = α (lab (n ^ j) x).1.1.toAdd + n ^ j • z) → (∀ j x, ∃ z, (lab' (n ^ j) (gam x)).1.1.toAdd = α' (lab' (n ^ j) x).1.1.toAdd + n ^ j • z) → ∀ y, J.e (α y) = α' (J.e y) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' J hJ hs α α' gam ha ha' y
  have hk : ∀ j, 0 < n ^ j := fun j => pow_pos (by omega) j
  have key : ∀ j x, ∃ z, J.e (lab (n ^ j) x).1.1.toAdd = (lab' (n ^ j) x).1.1.toAdd + n ^ j • z := by
    intro j x
    obtain ⟨p', e, r⟩ := exists_qt_image J (lab (n ^ j) x)
    obtain ⟨x₀, h, h'⟩ := hJ j _ p' e r
    have h₁ := (hL'.2.1 _ (hk j) x₀ x).2 ((hL.2.1 _ (hk j) x₀ x).1 h)
    obtain ⟨z, hz, _⟩ := h₁
    obtain ⟨w, hw, _⟩ := h'
    refine ⟨w - z, ?_⟩
    rw [← e, hw, hz, smul_sub]
    abel
  refine sub_eq_zero.1 (eq_zero_of_forall_pow_smul hn _ fun j => ?_)
  obtain ⟨p, rfl⟩ := hs j y
  obtain ⟨x, z₀, h₀, -⟩ := hL.2.2.1 _ (hk j) p
  obtain ⟨z₁, h₁⟩ := ha j x
  obtain ⟨z₂, h₂⟩ := ha' j x
  obtain ⟨z₃, h₃⟩ := key j x
  obtain ⟨z₄, h₄⟩ := key j (gam x)
  refine ⟨J.e (α z₀) - J.e z₁ + z₄ + z₂ - α' z₃ - α' (J.e z₀), ?_⟩
  rw [h₁, h₂, map_add (f := _), map_nsmul] at h₄
  rw [h₀]
  simp only [map_add (f := _), map_nsmul, h₃]
  linear_combination (norm := module) h₄

end GlobalTheory.ModelData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DifferentiableQuot
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibPrim
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.FrameValue

theorem differentiable_quot {A : Over (Sp ℂ)} [GrpObj A] {X : Scheme.{0}} {L : LB X} {L' : LB A.left} (hL' : L'.IsLB)
    {φ : A.left ⟶ X} {w : LB.Iso L' (L.pull φ)} (hw : w.IsGen) {g : ℕ} (u : HolUnif A L' g)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      fr z = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ φ), i)).val * u.fr i z)
    {K : Type} [Fintype K] {ψ : K → (X ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} (ht : t.IsGen)
    {z : (Fin g → ℂ) → K → Fin g → ℂ} (hd : ∀ k, Differentiable ℂ fun v => z v k)
    (hz : ∀ v k, ((u.ex v).left ≫ φ) ≫ ψ k = (u.ex (z v k)).left ≫ φ) :
    Differentiable ℂ fun v => vF t ((u.ex v).left ≫ φ) J / ∏ k, fr (z v k) ^ ε k := by
  intro v₀
  obtain ⟨j, hj⟩ : ∃ j, ⊤ ≤ ((u.ex v₀).left ≫ φ) ⁻¹ᵁ L.wchart ψ j :=
    ⟨_, (le_preimage_wchart _ L ψ _).2 fun _ => hJ _⟩
  obtain ⟨i, hi⟩ : ∃ i : K → L'.ι, ∀ k, ⊤ ≤ (u.ex (z v₀ k)).left ⁻¹ᵁ L'.U (i k) := ⟨_, fun _ => le_chartAt hL' _⟩
  have key : ∀ v, ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j → ∀ k,
      ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L.wchart (fun _ : PUnit => φ) (fun _ => j k) := fun v hv k =>
    (le_preimage_wchart _ L _ _).2 fun _ => hz v k ▸ (le_preimage_wchart _ L ψ _).1 hv k
  obtain ⟨ho, hh⟩ := u.hol (φ ⁻¹ᵁ L.wchart ψ j) ((φ.app _).hom (t.s j).val)
  have hn : {v | ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ j} ∈ nhds v₀ := ho.mem_nhds hj
  have d₁ : DifferentiableAt ℂ (fun v => valAt' ((u.ex v).left ≫ φ) (L.wchart ψ j) (t.s j).val) v₀ := by
    refine (hh.differentiableAt (ho.mem_nhds hj)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => ?_)
    exact ((valueRules _ (u.ex v).left).2.2.2.1 _ φ _ _).symm
  let G : K → (Fin g → ℂ) → ℂ := fun k x =>
    valAt' (u.ex x).left (L.wchart (fun _ : PUnit => φ) (fun _ => j k) ⊓ L'.U (i k)) (w.s (fun _ => j k, i k)).val *
      u.fr (i k) x
  have h₀ := fun k => (le_preimage_inf _ _ _).2 ⟨key v₀ hj k, hi k⟩
  have n₀ : ∀ k, G k (z v₀ k) ≠ 0 := fun k =>
    mul_ne_zero (val_unit_ne_zero _ valueRules (h₀ k) _) (u.fr_ne _ _ (hi k))
  have d₂ : DifferentiableAt ℂ (fun v => ∏ k, G k (z v k) ^ ε k) v₀ := by
    have a : ∀ k, DifferentiableAt ℂ (fun v => G k (z v k) ^ ε k) v₀ := fun k => by
      refine DifferentiableAt.zpow ?_ (Or.inl (n₀ k))
      refine DifferentiableAt.comp v₀ (g := G k) ?_ (hd k v₀)
      exact ((u.hol _ _).2.differentiableAt ((u.hol _ 0).1.mem_nhds (h₀ k))).fun_mul
        ((u.fr_hol (i k)).differentiableAt ((u.hol _ 0).1.mem_nhds (hi k)))
    classical
    exact (HasFDerivAt.finsetProd (u := Finset.univ) fun k _ => (a k).hasFDerivAt).differentiableAt
  refine (d₁.fun_mul (d₂.fun_inv (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (n₀ k)))).congr_of_eventuallyEq ?_
  have hn' : ∀ᶠ v in nhds v₀, ∀ k, ⊤ ≤ (u.ex (z v k)).left ⁻¹ᵁ L'.U (i k) :=
    Filter.eventually_all.2 fun k => (hd k v₀).continuousAt.preimage_mem_nhds ((u.hol _ 0).1.mem_nhds (hi k))
  filter_upwards [hn, hn'] with v hv hv'
  have hJv : ⊤ ≤ ((u.ex v).left ≫ φ) ⁻¹ᵁ L.wchart ψ fun k => J (((u.ex v).left ≫ φ) ≫ ψ k) :=
    (le_preimage_wchart _ L ψ _).2 fun _ => hJ _
  have e₁ := (val_gen _ valueRules t ht _ _ hJv hv).trans
    (congrArg (· * _) (val_linComb _ valueRules L ψ ε _ _ hJv hv))
  have e₂ : ∀ k, fr (z v k) = valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val * G k (z v k) := fun k => by
    rw [hfr _ _ (hv' k), hz v k, ← _root_.mul_assoc]
    refine congrArg (· * _) ((GlobalTheory.PowUnif.val_iso _ L L' (fun _ : PUnit => φ) w hw _ _ _ _
      ((le_preimage_wchart _ L _ _).2 fun _ => hJ _) (key v hv k) (hv' k) (hv' k)).trans ?_)
    rw [GlobalTheory.PowUnif.val_g_self hL' _ _ (hv' k), inv_one, _root_.mul_one, Fintype.prod_unique]
  have n : (∏ k, valAt' (((u.ex v).left ≫ φ) ≫ ψ k)
      (L.U (J (((u.ex v).left ≫ φ) ≫ ψ k)) ⊓ L.U (j k)) (L.g _ _).val ^ ε k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (val_unit_ne_zero _ valueRules
      ((le_preimage_inf _ _ _).2 ⟨hJ _, (le_preimage_wchart _ L ψ _).1 hv k⟩) _)
  simp only [e₂, mul_zpow, Finset.prod_mul_distrib]
  exact (congrArg (· / _) e₁).trans ((mul_div_mul_left _ _ n).trans (div_eq_mul_inv _ _))

theorem vF_eq_one {X Y Z : Scheme.{0}} {L : LB X} {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ))
    {K : Type} [Fintype K] {ψ : K → (Y ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L ψ ε)} {e : Z ⟶ Y}
    (h : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t e) (LB.oneGen L)) (y : Sp ℂ ⟶ Z) : vF t (y ≫ e) J = 1 := by
  have h₁ : ⊤ ≤ y ⁻¹ᵁ L.wchart (fun k => e ≫ ψ k) fun k => J (y ≫ e ≫ ψ k) :=
    (le_preimage_wchart _ L _ _).2 fun _ => hJ _
  have h₂ : ⊤ ≤ y ⁻¹ᵁ L.wchart (PEmpty.elim : PEmpty → (Z ⟶ X)) PEmpty.elim :=
    (le_preimage_wchart _ L _ _).2 fun k => k.elim
  have h₃ := (le_preimage_inf y _ _).2 ⟨h₁, h₂⟩
  have := congrArg (fun q : Γ(Z, _)ˣ => valAt' y _ q.val) (h (fun k => J (y ≫ e ≫ ψ k)) PEmpty.elim
    (fun a b q => congrArg (fun q => J (y ≫ q)) q) (fun a => a.elim) (fun _ b => b.elim))
  have e₁ := (val_res y valueRules inf_le_left h₃ _).symm.trans (this.trans (val_res y valueRules inf_le_right h₃ _))
  obtain ⟨r, hr⟩ := (valueRules Z y).2.1 _ h₂
  exact ((val_res y valueRules _ h₁ _).trans (val_pullU y valueRules e _ _)).symm.trans
    (e₁.trans ((hr _).trans (map_one r)))

theorem fibPrim : FibPrimSt := by
  rintro R _ _ _ D J g Λ Hm χ ex fr ⟨hJ, P', φ, w, u, rfl, hφ, hw, hAH, -, -, -, hex, hfr⟩ f hf F hF hFf hH Ef hEf t ⟨ht, h₀⟩
  change u.IsAH Hm χ at hAH
  have hL := P'.isLB
  have add : ∀ z z', ex (z + z') = ex z * ex z' := fun z z' => Over.OverMorphism.ext (by
    rw [hex, u.ex_add, ← hφ.2 _ _ _ (pushPt hφ.1.w (u.ex z)) (pushPt hφ.1.w (u.ex z')) rfl rfl]
    exact mul_left_congr (Category.id_comp _) _ _ _ _ (hex z).symm (hex z').symm)
  have zero : ex 0 = 1 := mul_eq_left.1 ((add 0 0).symm.trans (by rw [add_zero]))
  have per : ∀ (l : u.Λ) z, (ex (z + l)).left = (ex z).left := fun l z => by
    rw [hex, hex, ex_add_period u z l l.2]
  have fac : ∀ (l : u.Λ) z, (fr z : ℂ) = ahFactor Hm χ l z * fr (z + l) := fun l z => by
    have hi := le_chartAt hL (u.ex z).left
    have hi' : ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ P'.L.U (chartAt hL (u.ex z).left) := by
      rw [ex_add_period u z l l.2]; exact hi
    rw [hfr _ _ hi, hfr _ _ hi', hAH.2.2.2 l _ z hi, per, ex_add_period u z l l.2, mul_left_comm]
    rfl
  obtain ⟨V, hV⟩ : ∃ V : (Fin g → ℂ) → ℂ, ∀ v, V v = vF t (ex v).left J /
      (fr (v + F v) * ((fr v : ℂ) ^ 2)⁻¹ * (fr (F v) : ℂ)⁻¹ * fr 0 ^ 2) := ⟨_, fun _ => rfl⟩
  have dF : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have hd : Differentiable ℂ V := by
    have := differentiable_quot hL hw u hJ (fr := fun z => fr z) (fun z i hi => by rw [← hex]; exact hfr z i hi) ht
      (z := fun v => ![v + F v, v, F v, 0]) (fun k => by fin_cases k <;> simp <;> fun_prop) (fun v k => by
        rw [← hex, ← hex]
        fin_cases k
        · exact congrArg (fun m => m.left) (show ex v ≫ (𝟙 _ * f) = ex (v + F v) by
            rw [MonObj.comp_mul, Category.comp_id, ← hFf, add])
        · exact Category.comp_id _
        · exact congrArg (fun m => m.left) (hFf v).symm
        · exact congrArg (fun m => m.left) ((MonObj.comp_one (ex v)).trans zero.symm))
    convert this using 2 with v
    rw [hV, hex]
    simp [Fin.prod_univ_four]
  have hper : ∀ (l : u.Λ) v, V (v + l) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ / χ l * V v := fun l v => by
    have a₁ := fac (l + ⟨F l, hF l l.2⟩) (v + F v)
    have a₂ := fac l v
    have a₃ := fac ⟨F l, hF l l.2⟩ (F v)
    have c := chi_add hL hAH l ⟨F l, hF l l.2⟩
    have s : Complex.exp (Real.pi * Complex.I * (hermForm Hm l (F l)).im) = (-1) ^ Ef l ⟨F l, hF l l.2⟩ := by
      rw [← hEf l ⟨F l, hF l l.2⟩, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have x : Complex.exp (Real.pi * hermForm Hm (v + F v) (l + F l) + Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) =
        Complex.exp (Real.pi * hermForm Hm v l + Real.pi / 2 * hermForm Hm l l) ^ 2 *
        Complex.exp (Real.pi * hermForm Hm (F v) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      simp only [EigenNorm.hermForm_add_left, EigenNorm.hermForm_add_right]
      push_cast
      linear_combination (-Real.pi : ℂ) * hH v l - (Real.pi / 2 : ℂ) * hH l l
    rw [s] at c
    rw [hV, hV, per, a₁, a₂, a₃, map_add (f := _), add_add_add_comm v]
    simp only [ahFactor, c, Submodule.coe_add, x]
    have n := chi_ne_zero hAH l
    have n' := chi_ne_zero hAH ⟨F l, hF l l.2⟩
    have n'' : (-1 : ℂ) ^ Ef l ⟨F l, hF l l.2⟩ ≠ 0 := zpow_ne_zero _ (by simp)
    field_simp
  have hc := const_of_norm_periodic u hd (fun l v => by
    rw [hper, norm_mul, norm_div, hAH.2.2.1, norm_zpow, norm_neg, norm_one, one_zpow, div_one, _root_.one_mul])
  have h1 : V 0 = 1 := by
    have e : (ex 0).left = (TF (R := R) ℂ).hom ≫ eSec D.P.A := by rw [zero, Hom.one_def]; simp [eSec]
    rw [hV, e, vF_eq_one hJ h₀, map_zero, add_zero]
    have := (fr 0).ne_zero
    field_simp
  refine ⟨fun l => ?_, fun z => ?_⟩
  · have := hper l 0
    rw [hc _ 0, h1, _root_.mul_one] at this
    exact ((div_eq_one_iff_eq (chi_ne_zero hAH l)).1 this.symm).symm
  · have := (hV z).symm.trans ((hc z 0).trans h1)
    have a := (fr z).ne_zero
    have b := (fr (F z)).ne_zero
    have c := (fr (z + F z)).ne_zero
    have d := (fr 0).ne_zero
    field_simp at this
    exact this

theorem fibPrim_of_laws : Laws → FibPrimSt := fun _ => fibPrim

end GlobalTheory.Ex.Arch.FibPrim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianPartIsoThetaSectionScale
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.AbPartIso

noncomputable section
namespace GlobalTheory.Ex.AbPartIso
open ThetaInValues

theorem exists_th_scale : AllIso fun {_} _ _ {_} {_} {F} _ _ {N} {N'} ν ν' {_} w f =>
    ∃ lm : F, ∀ x, N'.th (f x) = lm * wVal ν ν' w f x * N.th x := by
  intro R _ _ D D' F _ _ N N' ν ν' φ w f hφ hw hc
  obtain ⟨y⟩ : Nonempty (TF (R := R) F).left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ := good ν y
  have hJ' := good ν' y
  obtain ⟨th, ρ, hth, vth⟩ := exists_th ν y
  obtain ⟨th', ρ', -, vth'⟩ := exists_th ν' y
  have e : φ.hom.left ≫ (snd (TF (R := R) F) D'.P.A).left = 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left :=
    (Category.id_comp _).symm
  let b := VVRank.pullTo (φ := fun _ : Fin 1 => (snd (TF (R := R) F) D'.P.A).left) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => 𝟙 _ ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left) th' φ.hom.left (fun _ => e)
  obtain ⟨a, ha, -⟩ := (FieldBaseChange.isoRelM_bijective (m := 𝟙 _) (k := 1) (h₁ := 𝟙 _)
    (g₁ := (snd (TF (R := R) F) D.P.A).left) D.P.isLB D'.P.isLB hw rfl (𝟙 _) (Category.id_comp _)
    (Category.id_comp _)).2 b
  obtain ⟨r, hr⟩ := hth a
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : F, r = fnOf r₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom r, (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of F)) r).symm⟩
  refine ⟨r₀ * ρ * ρ'⁻¹.val, fun x => ?_⟩
  have H := BoxExpansion.isoRel_val ha (ptSecT D.P.A (ν.eA x)).left y hJ hJ'
  simp only [Category.comp_id] at H
  have h₁ : sval b (ptSecT D.P.A (ν.eA x)).left y ν'.J = sR y (N'.th (f x) * ρ') := by
    refine (VVRank.sval_pullTo _ _ _ _ y hJ').trans (Eq.trans ?_ (vth' (f x)))
    rw [← Over.comp_left, ptSecT, hc x]
    rfl
  have hm := hJ.mem (fun _ : Fin 1 => (snd (TF (R := R) F) D.P.A).left) (ptSecT D.P.A (ν.eA x)).left
  have h₂ : sval a (ptSecT D.P.A (ν.eA x)).left y ν.J = sR y r₀ * sR y (N.th x * ρ) := by
    refine (congrArg (gs _ y _) (hr _)).trans ((gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ?_ (vth x)))
    refine (gs_res _ y _ hm _).trans ((gs_pull _ (fst (TF (R := R) F) D.P.A).left y ⊤ trivial _).trans ?_)
    rw [← Over.comp_left, ptSecT, lift_fst]
    exact gs_fnOf y r₀
  have p₁ : (ptSecT D.P.A (ν.eA x)).left ≫ (snd (TF (R := R) F) D.P.A).left = (ν.eA x).left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have p₂ : (ptSecT D.P.A (ν.eA x)).left ≫ (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left = (ν'.eA (f x)).left := by
    rw [← Over.comp_left, ptSecT, ← Category.assoc, hc x, lift_snd]
  have h₃ : sR y (wVal ν ν' w f x) = (BoxExpansion.pw w (ptSecT D.P.A (ν.eA x)).left y (ν.J (ν.eA x).left)
      (ν'.J (ν'.eA (f x)).left)).val := by
    have m₁ : (snd (TF (R := R) F) D.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D.P.A.left => q y ∈ D.P.L.U (ν.J (ν.eA x).left)) p₁).mpr (hJ _)
    have m₂ : (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left ((ptSecT D.P.A (ν.eA x)).left y) ∈
        D'.P.L.U (ν'.J (ν'.eA (f x)).left) :=
      (congrArg (fun q : (TF (R := R) F).left ⟶ D'.P.A.left => q y ∈ D'.P.L.U (ν'.J (ν'.eA (f x)).left)) p₂).mpr (hJ' _)
    exact toStk_valF (F := F) (ptSecT D.P.A (ν.eA x)).left
      ((D'.P.L.pull (φ.hom ≫ snd (TF (R := R) F) D'.P.A).left).U (fun _ => ν'.J (ν'.eA (f x)).left) ⊓
        (D.P.L.pull (snd (TF (R := R) F) D.P.A).left).U (fun _ => ν.J (ν.eA x).left)) y
      ⟨mem_pull.2 m₂, mem_pull.2 m₁⟩ _
  have H' : sR y (N'.th (f x) * ρ') = sR y (wVal ν ν' w f x) * (sR y r₀ * sR y (N.th x * ρ)) := by
    refine h₁.symm.trans (H.trans (congrArg₂ (· * ·) ?_ h₂))
    rw [h₃, pow_one, p₁, p₂]
  rw [← map_mul, ← map_mul] at H'
  haveI : Nontrivial ((TF (R := R) F).left.presheaf.stalk y) := inferInstance
  have := (sR (R := R) y).injective H'
  rw [← Units.eq_mul_inv_iff_mul_eq] at this
  rw [this]
  ring

end GlobalTheory.Ex.AbPartIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompareUniformisationDataPullback
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory.LN.PreCompare

theorem exists_cmp : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] [IsLocalRing V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I' ≠ ⊤ → ∀ φ : R →+* V, I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ C : Cmp φ U U' F, C.wL = wL := by
  intro hL _ _ R V _ _ _ _ _ _ I I' _ hV _ φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨D₁, U₁, C₁, hP, hC⟩ := PreBaseChange.exists_cmp_pull hL R V I I' φ hI D D' A A' G G' U U' F pb wL hw
  obtain ⟨semi, gen, gen_hom, P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ := U'
  obtain rfl : U₁.P = P := hP
  obtain rfl : C₁.wL = wL := eq_of_heq hC
  obtain ⟨C₂, h₂⟩ := PreUnique.exists_cmp_id hL V I' hV D₁ D' A' A' G' U₁
    ⟨semi, gen, gen_hom, U₁.P, wA, wA_gen, gt, gt_q, gt_t, w, w_gen, w_vals, w_compat⟩ (idIso U₁.P.L.L) (by simp)
    (IsCPMap.id U₁.P)
  refine _root_.GlobalTheory.LN.Cmp.exists_comp_id R V I I' φ D D₁ D' A A' A' G G' U U₁ _ F C₁ C₂ C₁.wL hw fun Z r z j i k hj hi hk => ?_
  rw [h₂]
  have a := (isGen_iff _).1 C₁.wL_map.gen Z r z j j i k hj hj hi hk
  rw [gm_self U.P.L.isLB (r ≫ F) z hj, _root_.one_mul] at a
  exact ((congrArg₂ (· * ·) a (gw_idIso U₁.P.L.L r z hi hk)).trans (by rw [mul_comm, mul_inv_cancel_left])).symm

end GlobalTheory.LN.PreCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumDHomDegenerationValuesFieldExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numDHom_degenerationValues_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F F' : Type) [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ (N : NumD F) (N' : NumD F') (ν : NumOf D F N) (ν' : NumOf D F' N'), ν'.th = ν.th → ∃ I : NumD.Hom f N N', I.lam = 1 ∧ (∀ y, ν'.eX (I.e y) = ν.eX y) ∧ ∀ (k : ℕ) (p : QkPt D F k) (p' : QkPt D F' k) (q : N.QT k) (q' : N'.QT k), QkExt f p p' → ν.QPt p q → ν'.QPt p' q' → q'.1.1.toAdd = I.e q.1.1.toAdd ∧ I.Rel q.1.2 q'.1.2 := by
  first | exact @GlobalTheory.GaugeHom.exists_hom | exact GlobalTheory.GaugeHom.exists_hom | (intros; apply GlobalTheory.GaugeHom.exists_hom <;> assumption)
end

