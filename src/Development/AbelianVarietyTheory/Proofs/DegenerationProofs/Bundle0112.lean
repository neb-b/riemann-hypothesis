module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal

theorem exists_nsmul_eq {κ : Type} {r N : ℕ} (h : 1 ≤ r * N) (a : κ → ZMod (r * N)) (ha : N • a = 0) :
    ∃ c : κ → ZMod (r * N), a = r • c := by
  haveI : NeZero (r * N) := ⟨by omega⟩
  have hN : 0 < N := Nat.pos_of_mul_pos_left h
  have key : ∀ i, r ∣ (a i).val := fun i => by
    have e : ((N * (a i).val : ℕ) : ZMod (r * N)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← nsmul_eq_mul]
      exact congrFun ha i
    rw [ZMod.natCast_eq_zero_iff, mul_comm N] at e
    exact Nat.dvd_of_mul_dvd_mul_right hN e
  choose c hc using key
  refine ⟨fun i => (c i : ZMod (r * N)), funext fun i => ?_⟩
  rw [Pi.smul_apply, nsmul_eq_mul, ← Nat.cast_mul, ← hc, ZMod.natCast_zmod_val]

theorem fn_hom {R : Type} [CommRing R] (v : Γ((baseOver (Sp R)).left, ⊤)) :
    fn ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom v) = v :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id_apply v

theorem fn_injective {R : Type} [CommRing R] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem isNoetherian_of_fg [ArithBase o Ω] {R : Subalgebra o Ω} (h : R.FG) : IsNoetherianRing R := by
  have := ArithBase.ded (o := o) (Ω := Ω)
  exact isNoetherianRing_of_fg h

theorem algebraMap_injective [ArithBase o Ω] (R : Subalgebra o Ω) : Function.Injective (algebraMap o R) :=
  fun _ _ h => ArithBase.inj (o := o) (Ω := Ω) (congrArg Subtype.val h)

theorem prim_iff [ArithBase o Ω] (R : Subalgebra o Ω) (ze : oˣ) (q : ℕ) :
    IsPrimitiveRoot (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) q ↔ IsPrimitiveRoot (ze : o) q := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact IsPrimitiveRoot.map_iff_of_injective
    (f := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R))
    (fn_injective.comp (algebraMap_injective R))

theorem exists_real_of_univBasis (hL : Laws) [ArithBase o Ω] (R : Subalgebra o Ω) (fg : R.FG)
    (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ) (hp : n.Prime)
    (ho : Odd n) (hk : 2 ≤ k) (hj : 1 ≤ j) (hu : IsUnit (n : o)) (hS : HypS P.A P.L)
    (lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)))
    (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))) (hth : UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th))
    (b : Fin (((n ^ k) ^ 2) ^ P.g) → SecM P.A P.L ((n ^ k) ^ 2 : ℕ) (baseOver (Sp R)))
    (hb : UnivBasis P ((n ^ k) ^ 2 : ℕ) b) {R₀ : Subalgebra o Ω} (h : R₀ ≤ R) (P₀ : PolAV (Sp R₀))
    (φ : P.A.left ⟶ P₀.A.left) (hg : P.g = P₀.g)
    (hφ : IsGrpPullback P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ) (hiso : LBIso P.L (P₀.L.pull φ))
    (x₀ : Fin (2 * P₀.g) → (baseOver (Sp R₀) ⟶ P₀.A))
    (hx₀ : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)), (i : ℕ) = i' →
      (lev.pt i').left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i).left) :
    ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R₀ ≤ S.R) (φ : ρ.P.A.left ⟶ P₀.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧
      S.r = n ^ j ∧ S.g = P₀.g ∧ IsGrpPullback ρ.P.A P₀.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧
      LBIso ρ.P.L (P₀.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P₀.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P₀.g →
      (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₁ ^ (S.r * S.N)).left ∧
      (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ =
        spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i₂ ^ (S.r * S.N)).left := by
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hn2 : 2 ≤ n := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  have hr1 : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn1
  have hN2 : 2 ≤ (n ^ k) ^ 2 := by
    have : n ^ 1 ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    nlinarith
  have hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k) := by ring
  have hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2 := hM ▸ Nat.one_le_pow _ _ hn1
  have hMo : Odd (n ^ j * (n ^ k) ^ 2) := hM ▸ ho.pow
  let f : o →+* Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)
  have hf : Function.Injective f := fn_injective.comp (algebraMap_injective R)
  haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial
  have un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤)) := fun q e hq => by
    have := (hu.pow e).map f
    rw [map_pow, map_natCast] at this
    rw [hq, Nat.cast_pow]
    exact this
  have prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2) := (prim_iff R ze _).1 lev.prim
  obtain ⟨pt, hadd, hbij, hweil, hdiv, hnorm⟩ := _root_.GlobalTheory.exists_torsionPoints_of_squareLevel hL _ P _ _ hM1 (un _ _ hM) lev
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  obtain ⟨rig, hrig⟩ := P.rigid
  have hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ := fun a => by
    obtain ⟨y, hy, e⟩ := hdiv a
    obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.exists_symLift_global hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy
    exact GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ
  choose fr hfr using hfr
  have tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1 := fun a => by
    rw [← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]
  choose U hU using fun a => _root_.GlobalTheory.exists_symLift_global hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _)
    (b := 1) P.isLB hα th
  obtain ⟨u, u₁, u₂, u₃, u₄, u₅⟩ := exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀
  have hspan := GlobalTheory.T.span_translates_multiplicationPullback_theta hL _ P (n ^ k) _ rfl hm1 (un _ _ rfl) th hth _ b hb α hα s₀ hs₀ _ U
    (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : (n ^ k) ^ 2 • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM1 a e
      exact ⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)
  obtain ⟨bb, -⟩ := hb.exists_basis
  obtain ⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩ := _root_.GlobalTheory.ThetaReal.exists_monomial_matrices o _ _ f hf P.g (n ^ k) (n ^ j) _ rfl hm1 hr1
    ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one bb u (SecM.ofSec P.A s₀) u₂
    (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan
  choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1
  choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists
  let ev : Γ((baseOver (Sp R)).left, ⊤) → R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0} := fun a => by
    let K := AlgebraicClosure Ω
    let x : Sp K ⟶ Sp R := spMap ((algebraMap Ω K).comp R.val.toRingHom)
    have := ArithBase.char (o := o) (Ω := Ω)
    obtain ⟨y, hy, H⟩ := GlobalTheory.T.exists_good_torsion_translate_geometricPoint hL _ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th hth
      ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)
    obtain ⟨c, hc, -⟩ := hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy,
      one_pow])
    obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
    refine ⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
      (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩
    refine H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_
    have e' : ev (v (a + c)) = 0 := Subtype.ext e
    exact (fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))
  obtain ⟨c₁, hc₁⟩ := hth.exists_basis
  let S : ThetaSys o Ω :=
    { g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim
      unit := by rw [hM, Nat.cast_pow]; exact hu.pow _
      J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃
      th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, frac := frac
      th_mem := fun a => (ev (v a)).2, ev_mem := fun a i => (ev (w a i)).2
      supp := _root_.GlobalTheory.ThetaReal.closure_eq_top_of_meets_torsion_cosets _ n (j + 2 * k) _ hn1 (by omega) hM _ good
      th_ne := by
        obtain ⟨y, -, hy⟩ := good 0
        exact ⟨_, hy⟩ }
  let ρ' : S.Real :=
    { P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl
      r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij
      weil := fun a b c hc => by
        have e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^
            (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val) := Units.ext
          ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))
        rw [e]
        exact hweil a b
      rig := rig, rig_gen := hrig, th₁ := th
      th₁_basis := fun σ => by
        have := existsUnique_of_basis c₁ σ
        simp only [hc₁] at this
        exact this
      fr := fr, fr_tors := hfr
      th_val := fun a => (fn_hom (v a)).symm ▸ hv a
      s := fun i => SecM.toSec P.A (s i)
      s_basis := existsUnique_of_basis s
      ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)
      i₀ := i₀, α := α, α_gen := hα, α_norm := hαn
      s_zero := by
        have e : SecM.toSec P.A (s i₀) = s₀ := by rw [hi₀]; rfl
        exact e ▸ hs₀
      U := U, U_sym := hU
      U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))
      orbit := ρ₅ }
  refine ⟨S, ρ', h, φ, rfl, rfl, rfl, hg, hφ, hiso, fun i i₁ i₂ e₁ e₂ => ?_⟩
  obtain ⟨q₁, q₂⟩ := hnorm i ⟨i₁, by have := i₁.2; omega⟩ ⟨i₂, by have := i₂.2; omega⟩ e₁
    (e₂.trans (congrArg (_ + ·) hg.symm))
  have key : ∀ (i : Fin (2 * P₀.g)) (i' : Fin (2 * P.g)) (q : ℕ), (i : ℕ) = i' →
      (lev.pt i' ^ q).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (x₀ i ^ q).left := fun i i' q e =>
    (ThetaPtMove.over_pow hφ (T := baseOver (Sp R)) (T₀ := baseOver (Sp R₀)) _
      ((Category.comp_id _).trans (Category.id_comp _).symm) (hx₀ i i' e).symm q).symm
  exact ⟨(congrArg (fun z => z.left ≫ φ) q₁).trans (key _ _ _ rfl),
    (congrArg (fun z => z.left ≫ φ) q₂).trans (key _ _ _ rfl)⟩

end GlobalTheory.ThetaReal


open GlobalTheory.ThetaReal in
theorem GlobalTheory.ThetaReal.exists_thetaSys_real : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) ∧ ∀ (i : Fin S.g) (i₁ i₂ : Fin (2 * P.g)), (i₁ : ℕ) = i → (i₂ : ℕ) = i + P.g → (ρ.pt (Pi.single (.inl i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₁ ^ (S.r * S.N)).left ∧ (ρ.pt (Pi.single (.inr i) 1)).left ≫ φ = spMap (Subalgebra.inclusion h).toRingHom ≫ (lev.pt i₂ ^ (S.r * S.N)).left := by
  intro hL hL₂ o Ω _ _ _ _ R fg frac P n k j ze hp ho hk hj hu hS lev
  haveI := isNoetherian_of_fg fg
  let p : Sp R := (⊥ : PrimeSpectrum R)
  obtain ⟨V₁, m₁, b₁, hb₁⟩ := exists_univBasis hL₂.secBaseChangeAny P 1 le_rfl p
  obtain ⟨V₂, m₂, b₂, hb₂⟩ := exists_univBasis hL₂.secBaseChangeAny P ((n ^ k) ^ 2)
    (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hp.pos)) p
  obtain ⟨R', h, fg', τ, hτ⟩ := GlobalTheory.T.exists_fg_subalgebra_spec_factor_through_open o Ω R fg (V₁ ⊓ V₂) ⟨p, m₁, m₂⟩
  haveI := isNoetherian_of_fg fg'
  obtain ⟨P', φ, hg, hφ, hiso⟩ := exists_isPolFibre hL.polBaseChange (Subalgebra.inclusion h).toRingHom P
  have hiso' := LBIso.symm hiso
  have w : ∀ (V : (Sp R).Opens) (hV : V₁ ⊓ V₂ ≤ V), (τ ≫ (Sp R).homOfLE hV) ≫ (overRes (T := baseOver (Sp R)) V).hom =
      spMap (Subalgebra.inclusion h).toRingHom := fun V hV => by
    change (τ ≫ (Sp R).homOfLE hV) ≫ V.ι ≫ 𝟙 _ = _
    rw [Category.comp_id, Category.assoc, Scheme.homOfLE_ι, hτ]
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₁ inf_le_left) b₁ hb₁
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.T.universalBasis_move_baseChange _ _ _ P P' φ hφ hiso' _ _ _ _ (w V₂ inf_le_right) b₂ hb₂
  obtain ⟨lev', hlev⟩ := _root_.GlobalTheory.exists_level_baseChange hL _ _ _ P P' φ hφ hiso' hg _ _
    (unitOn (Units.map (algebraMap o R').toMonoidHom ze))
    (congrArg (fun q => q.hom (algebraMap o R ze))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Subalgebra.inclusion h).toRingHom))).symm
    ((prim_iff R' ze _).2 ((prim_iff R ze _).1 lev.prim)) lev
  haveI hU : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let e := finCongr (congrArg (((n ^ k) ^ 2) ^ ·) hg)
  refine exists_real_of_univBasis hL R' fg' (fun x => ?_) P' n k j ze hp ho hk hj hu
    (SymBaseChange.hypS_baseChange _ _ _ _ _ φ _ _ P.isLB P'.isLB hφ hiso' hS) lev' (SecM.toSec P'.A (c₁ hU.default))
    hc₁.unique (fun i => c₂ (e i)) (fun T _ u => ?_) h P φ hg hφ hiso' lev.pt hlev
  · obtain ⟨a, ha, b, hb, e⟩ := frac x
    exact ⟨a, h ha, b, h hb, e⟩
  · obtain ⟨c, hc⟩ := hc₂ T u
    exact ⟨c.reindex e.symm, fun i => by rw [Module.Basis.reindex_apply, hc, Equiv.symm_symm]⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibrewiseNonzeroSectionProdAndBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.FibreNonzero

def pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => h) (fun _ => ((1 : ℕ) : ℤ))) :=
  LBGerm.secOfGerm (fun j => (Y.presheaf.map (homOfLE (LB.wchart_le L (fun _ : Fin 1 => h) j 0)).op).hom
      ((h.app (L.U (j 0))).hom (θ.f (j 0)))) fun y i j hi hj => by
    have hi' : (𝟙 Y ≫ h) y ∈ L.U (i 0) := Set.mem_iInter.1 hi 0
    have hj' : (𝟙 Y ≫ h) y ∈ L.U (j 0) := Set.mem_iInter.1 hj 0
    refine ((gs_res _ y _ hi _).trans (gs_pull (𝟙 Y) h y _ hi' _)).trans ((gs_compat θ _ y hi' hj').trans
      (congrArg₂ (· * ·) (congrArg Units.val ?_) ((gs_res _ y _ hj _).trans (gs_pull (𝟙 Y) h y _ hj' _)).symm))
    refine Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => h) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 Y) y i j hi hj).symm
    simp

theorem mem_nonzeroLocus_pullOne {X Y : Scheme.{0}} {L : LB X} (θ : L.Sec) (h : Y ⟶ X) (y : Y) (i : L.ι)
    (hy : h y ∈ X.basicOpen (θ.f i)) : y ∈ nonzeroLocus (pullOne θ h) := by
  have hi' : (𝟙 Y ≫ h) y ∈ L.U i := X.basicOpen_le _ hy
  have hi : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : Fin 1 => h) (fun _ => i) := Set.mem_iInter.2 fun _ => hi'
  refine (mem_nonzeroLocus_iff_isUnit (pullOne θ h) (k := fun _ => i) hi).2 ?_
  have e := (gs_res (𝟙 Y) y (LB.wchart_le L (fun _ : Fin 1 => h) (fun _ => i) 0) hi _).trans
    (gs_pull (𝟙 Y) h y _ hi' (θ.f i))
  exact e ▸ (LBGerm.isUnit_gs_iff _ y _ hi' _).2 hy

theorem isIso_snd_left {S : Scheme.{0}} (G : Over S) : IsIso (snd (𝟙_ (Over S)) G).left := by
  have : IsIso (snd (𝟙_ (Over S)) G) := by
    rw [← leftUnitor_hom]; infer_instance
  exact inferInstanceAs (IsIso ((Over.forget S).map (snd (𝟙_ (Over S)) G)))

end GlobalTheory.FibreNonzero


open GlobalTheory.FibreNonzero in
theorem GlobalTheory.fibNZ_prod_and_baseChange : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), (ThetaNZ G U.P.L.L → ∃ σ : U.SecGT (𝟙_ _) 1, FibNZ (𝟙_ _ ⊗ G).hom σ) ∧ ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k), (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') → FibNZ (𝟙_ _ ⊗ G).hom σ → FibNZ (𝟙_ _ ⊗ G').hom σ' := by
  intro R V _ _ _ _ I I' φ D D' A G _ _ A' G' _ _ U U' F C
  have := isIso_snd_left G
  have := isIso_snd_left G'
  refine ⟨fun ⟨θ, hθ⟩ => ⟨pullOne θ _, fun y => ?_⟩, fun k σ σ' h hσ y' => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hθ y
    obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
    refine ⟨z, ?_, mem_nonzeroLocus_pullOne θ _ z i hi⟩
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply, hg]
  · obtain ⟨z, hz, hzσ⟩ := hσ (spMap φ y')
    rw [← Over.w (snd (𝟙_ _) G), Scheme.Hom.comp_apply] at hz
    obtain ⟨g', hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback C.pb.1 _ y' hz
    obtain ⟨z', rfl⟩ := (snd (𝟙_ _) G').left.surjective g'
    refine ⟨z', by rw [← Over.w (snd (𝟙_ _) G'), Scheme.Hom.comp_apply, hg₂], ?_⟩
    let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
    have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
    have hrz : r z' = z := by
      apply (snd (𝟙_ _) G).left.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hr, Category.id_comp, Scheme.Hom.comp_apply, hg₁]
    obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
    obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
    have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 (hrz ▸ hzσ)
    rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
    exact (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory.LN.GenericPoint

theorem exists_extend {F K : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] [Field K] [CharZero K]
    (V : ValuationSubring F) (g : V →+* K) : ∃ g' : F →+* K, g'.comp V.subtype = g := by
  have hinj : Function.Injective g := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro a ha
    by_contra h0
    have hF : IsAlgebraic ℤ (a : F) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic _)
    have hV : IsAlgebraic ℤ a :=
      (isAlgebraic_algHom_iff (V.subtype.toIntAlgHom) Subtype.val_injective).1 hF
    refine Ideal.comap_ne_bot_of_algebraic_mem h0 ha hV (eq_bot_iff.2 fun n hn => ?_)
    have e : (n : K) = 0 := by simpa using hn
    exact_mod_cast e
  exact ⟨IsFractionRing.lift hinj, RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a⟩

theorem jK_mem {R : Type} [CommRing R] [IsDomain R] {U : Set (Sp R)} (hU : IsOpen U) (h : U.Nonempty)
    (q : Sp (FractionRing R)) : jK R q ∈ U := by
  obtain ⟨x, hx⟩ := h
  refine Specializes.mem_open (x := jK R q) (y := x) ?_ hU hx
  refine (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 fun a ha => ?_
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.isPrime.ne_top
  have h1 : algebraMap R (FractionRing R) a ∈ q.asIdeal := ha
  rw [hq, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))] at h1
  rw [h1]; exact Ideal.zero_mem _

theorem lbIso_pull {W X Y : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : W ⟶ Y)
    {a' : W ⟶ X} (ha : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (chartPullSame L _ _ _ j fun _ => ha) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_of_sabMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f) :
    LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, hw, -⟩ := m.lin
  exact ⟨w, hw⟩

theorem polAt_of_lift {X S Z : Scheme.{0}} {T : SAB H X} {t : SAB H S} {t' : SAB H Z} {ξ : S ⟶ X} {j : Z ⟶ X}
    (m : SABMap t T ξ) (m' : SABMap t' T j) (hp : IsProper t'.G.hom) (hA : RelAmple t'.G t'.PP.L)
    (hK : KTriv t'.G t'.PP.L) {K : Type} [Field K] (x : Sp K ⟶ S) (y : Sp K ⟶ Z) (h : y ≫ j = x ≫ ξ) : PolAt t x := by
  have g₁ : IsGrpPullback ((Over.pullback x).obj t.G) T.G (x ≫ ξ) (pullback.fst t.G.hom x ≫ m.φ) :=
    (isGrpPullback_pullback t.G x).comp m.cart
  have w : (pullback.fst t.G.hom x ≫ m.φ) ≫ T.G.hom = (pullback.snd t.G.hom x ≫ y) ≫ j :=
    g₁.1.w.trans (by rw [Category.assoc, h]; rfl)
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : pullback t.G.hom x ⟶ t'.G.left,
      ψ ≫ m'.φ = pullback.fst t.G.hom x ≫ m.φ ∧ ψ ≫ t'.G.hom = pullback.snd t.G.hom x ≫ y :=
    ⟨_, m'.cart.1.lift_fst _ _ w, m'.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback ((Over.pullback x).obj t.G) t'.G y ψ :=
    m'.cart.cancel (g₁.congr h.symm h₁.symm) h₂
  have e : LBIso (t.PP.L.pull (pullback.fst t.G.hom x)) (t'.PP.L.pull ψ) :=
    LBIso.trans (pull_isLB t.PP.isLB _) (pull_isLB T.PP.isLB _) (pull_isLB t'.PP.isLB _)
      (lbIso_pull (lbIso_of_sabMap m) _ rfl) (lbIso_pull (lbIso_of_sabMap m') _ h₁.symm).symm
  have hp' : IsProper (pullback.snd t.G.hom x) := MorphismProperty.of_isPullback (P := @IsProper) g₂.1 hp
  have hq := amplePt Z K y t'.G ((Over.pullback x).obj t.G) ψ g₂ t'.PP.L (t.PP.L.pull (pullback.fst t.G.hom x))
    t'.PP.isLB (pull_isLB t.PP.isLB (pullback.fst t.G.hom x)) e hA hK
  exact ⟨hp', hq.1, hq.2⟩

end GlobalTheory.LN.GenericPoint


open GlobalTheory.LN.GenericPoint in
theorem GlobalTheory.LN.generic_point_of_meets_abLocus : Laws → Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (ξ : Sp R ⟶ Y.X) (t : SAB H (Sp R)) (_ : SABMap t Y.t ξ), (ξ ⁻¹' abLocus Y.t.G).Nonempty → (∃ y : Sp (FractionRing R) ⟶ Xo.XF c, y ≫ Y.j = jK R ≫ ξ) ∧ PolAt t (jK R) ∧ ξ ⁻¹' abLocus Y.t.G = abLocus t.G := by
  intro _ _ E _ _ _ H D l Xo c W₀ Y p ⟨_, _, _, ⟨U, hU, _⟩, _⟩ R _ _ _ ξ t m hne
  have hop : IsOpen (ξ ⁻¹' abLocus Y.t.G) := by
    rw [← hU]; exact U.isOpen.preimage ξ.continuous
  have := c.fin
  obtain ⟨g, hg⟩ := exists_extend (K := FractionRing R) (c.V W₀) (Spec.preimage ((jK R ≫ ξ) ≫ Y.s)).hom
  have sq : (jK R ≫ ξ) ≫ Y.s = spMap g ≫ spMap (c.V W₀).subtype := by
    rw [← Geo.Tor.spMap_comp, hg]
    exact (Spec.map_preimage _).symm
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ sq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact jK_mem hop hne q
  have hy : IsOpenImmersion.lift Y.jQ _ hr ≫ Y.j = jK R ≫ ξ := by
    rw [Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  exact ⟨⟨_, hy⟩, polAt_of_lift m Y.m Y.oF.proper Y.oF.ample Y.oF.ktriv _ _ hy,
    Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi m.cart.1 x⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawOfHasTestsOfIndep
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := _root_.GlobalTheory.ZJ.Core.fib_of_indep C hI
  have hS := _root_.GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests C hT hF
  have hC : C.TestCart := _root_.GlobalTheory.ZJ.Core.testCart_of_fib C hF hS
  have hL : C.FibLaw := _root_.GlobalTheory.ZJ.Core.fibLaw_of_testCart C hC
  exact _root_.GlobalTheory.ZJ.Core.nonempty_law C hS hC (_root_.GlobalTheory.ZJ.Core.exists_add_extension C hT hS hC hL) (_root_.GlobalTheory.exists_inv_extension C hT hS hC hL)

end GlobalTheory.ZJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThmUOfAllSet
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ZH

theorem thmU_of_allSet : Laws → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → GlobalTheory.UU.AllSet (fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.gen = s.gen) → ThmUSt := by
  intro hL hext hall V _ _ _ _ hV A G _ _ hG hE hS gen hgen
  obtain ⟨s, hs⟩ := _root_.GlobalTheory.ZH.exists_setting_of_hypS hL hext V hV A G hG hE hS gen hgen
  obtain ⟨D, U, hU⟩ := hall V A G s
  exact ⟨D, U, hU.trans hs⟩
end GlobalTheory.ZH
end

