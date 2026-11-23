module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0116
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymAndLinearisationOdd
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0172
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HermAdjoint

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_nsmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact (u.ker 0).2 u.Λ.zero_mem
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem exists_period_of_pow_eq_one {n : ℕ} (hn : 0 < n) {x : 𝟙_ (Over (Sp ℂ)) ⟶ A} (hx : x ^ n = 1) :
    ∃ a : u.Λ, u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) = x := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 ((ex_nsmul u n z).trans hx)⟩, ?_⟩
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]

theorem ex_period_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_nsmul, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
  exact (u.ker _).2 a.2

theorem unitOn_injective {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) :=
  Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective

theorem int_eq_of_exp {p q : ℤ}
    (h : ∀ n : ℕ, 0 < n → Complex.exp (-(2 * Real.pi * Complex.I) * (p : ℂ) / n) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ) / n)) : p = q := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h ((q - p).natAbs + 1) (Nat.succ_pos _))
  have hn : (((q - p).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
  have h₁ : ((q - p : ℤ) : ℂ) = ((m * (((q - p).natAbs + 1 : ℕ) : ℤ) : ℤ) : ℂ) := by
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((q - p).natAbs + 1 : ℕ) : ℂ) = N at hm hn
    refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
    field_simp at hm ⊢
    linear_combination hm
  have h₂ : (((q - p).natAbs + 1 : ℕ) : ℤ) ∣ q - p := ⟨m, by rw [mul_comm]; exact Int.cast_injective h₁⟩
  have h₃ := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h₂ (by rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem adjoint_of_im (Hm : Matrix (Fin g) (Fin g) ℂ) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ a ∈ s, ∀ b ∈ s, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im)
    (z w : Fin g → ℂ) : hermForm Hm (F z) w = hermForm Hm z (F' w) := by
  have sl : ∀ (t : ℂ) a b, hermForm Hm (t • a) b = t * hermForm Hm a b := fun t a b => by
    simp [hermForm, smul_dotProduct]
  have sr : ∀ (t : ℝ) a b, hermForm Hm a ((t : ℂ) • b) = t * hermForm Hm a b := fun t a b => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  have al : ∀ a a' b, hermForm Hm (a + a') b = hermForm Hm a b + hermForm Hm a' b := fun a a' b => by
    simp [hermForm, add_dotProduct]
  have ar : ∀ a b b', hermForm Hm a (b + b') = hermForm Hm a b + hermForm Hm a b' := fun a b b' => by
    simp [hermForm, Matrix.mulVec_add, dotProduct_add]
  have all : ∀ a b, (hermForm Hm (F a) b).im = (hermForm Hm a (F' b)).im := fun a b => by
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    have hb : b ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha, hb using Submodule.span_induction₂ with
    | mem_mem a b ha hb => exact h a ha b hb
    | zero_left b _ => simp [hermForm]
    | zero_right a _ => simp [hermForm]
    | add_left a a' b _ _ _ h₁ h₂ => rw [map_add (f := _), al, al, Complex.add_im, Complex.add_im, h₁, h₂]
    | add_right a b b' _ _ _ h₁ h₂ => rw [map_add (f := _), ar, ar, Complex.add_im, Complex.add_im, h₁, h₂]
    | smul_left t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sl, sl, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
    | smul_right t a b _ _ h₁ =>
      rw [← Complex.coe_smul, map_smul, sr, sr, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h₁]
  refine Complex.ext ?_ (all z w)
  have := all (Complex.I • z) w
  rwa [map_smul, sl, sl, Complex.I_mul_im, Complex.I_mul_im] at this

theorem lbIso_cubeLB_iff_hermForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  intro hl hl₂ hc hU P u Hm χ f f' F F' hAH hf hf' e e'
  have := P.isAb.comm
  obtain ⟨Ef, hE, -, -, -, -, -, -, hW⟩ := GlobalTheory.AnyAppellHumbert.isAH_properties hl hl₂ hc hU P u Hm χ hAH
  have hF : ∀ a : u.Λ, F a ∈ u.Λ := fun a => by rw [← u.ker, e, (u.ker _).2 a.2, MonObj.one_comp]
  have hF' : ∀ a : u.Λ, F' a ∈ u.Λ := fun a => by rw [← u.ker, e', (u.ker _).2 a.2, MonObj.one_comp]
  let c : ℤ → ℕ → ℂˣ := fun p n => Units.mk0 _ (Complex.exp_ne_zero (-(2 * Real.pi * Complex.I) * (p : ℂ) / n))
  have w₁ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)) ≫ f)
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn (c (Ef ⟨_, hF a⟩ b) n)) := fun n a b hn => by
    rw [← e, map_smul]
    exact hW n ⟨_, hF a⟩ b _ hn rfl
  have w₂ : ∀ (n : ℕ) (a b : u.Λ), 0 < n → Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ)))
      (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ)) ≫ f') (unitOn (c (Ef a ⟨_, hF' b⟩) n)) := fun n a b hn => by
    rw [← e', map_smul]
    exact hW n a ⟨_, hF' b⟩ _ hn rfl
  have uq : ∀ (n : ℕ) (x y : 𝟙_ (Over (Sp ℂ)) ⟶ P.A) (d d' : Γ((𝟙_ (Over (Sp ℂ))).left, ⊤)ˣ), x ^ n = 1 → y ^ n = 1 →
      Out.WeilIs P.A P.L n (x ≫ f) y d → Out.WeilIs P.A P.L n (x ≫ f) y d' → d = d' := fun n x y d d' hx hy h h' =>
    ((hl.weil _ P n _).1 _ _ (by rw [← MonObj.pow_comp, hx, MonObj.one_comp]) hy).unique h h'
  constructor
  · intro hiso
    obtain ⟨t, ht⟩ := GlobalTheory.NormRos.exists_gen_rosati P.isLB _ _ hiso
    have hR : Out.RosatiAdj P.A P.L f f' := fun _ =>
      ⟨⊤, trivial, LB.pullGen _ _ _ t _, DVR.pullGen_isGen _ _ _ _ ht _⟩
    refine adjoint_of_im Hm F F' _ u.full fun a ha b hb => ?_
    have : Ef ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩ = Ef ⟨a, ha⟩ ⟨_, hF' ⟨b, hb⟩⟩ := int_eq_of_exp fun n hn => by
      have hx := ex_period_pow u hn ⟨a, ha⟩
      have hy := ex_period_pow u hn ⟨b, hb⟩
      exact congrArg Units.val (unitOn_injective (uq n _ _ _ _ hx hy (w₁ n ⟨a, ha⟩ ⟨b, hb⟩ hn)
        ((GlobalTheory.weilIs_rosati_iff hl.globalFns hl.cube P f f' hR n _ _ hx hy _).2 (w₂ n ⟨a, ha⟩ ⟨b, hb⟩ hn))))
    exact (hE ⟨_, hF ⟨a, ha⟩⟩ ⟨b, hb⟩).symm.trans ((congrArg Int.cast this).trans (hE _ _))
  · intro H
    refine GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hl ℂ P f f' hf hf' fun n x y d hn hx hy hd => ?_
    obtain ⟨a, rfl⟩ := exists_period_of_pow_eq_one u hn hx
    obtain ⟨b, rfl⟩ := exists_period_of_pow_eq_one u hn hy
    have hab : Ef ⟨_, hF a⟩ b = Ef a ⟨_, hF' b⟩ := by
      apply Int.cast_injective (α := ℝ)
      rw [hE, hE]
      exact congrArg Complex.im (H a b)
    rw [uq n _ _ _ _ hx hy hd (w₁ n a b hn), hab]
    exact w₂ n a b hn

end GlobalTheory.HermAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescended
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.OddDescent

theorem exists_descended : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (g m : ℕ) (M : LB A.left) (pt : Fin (2 * g) → (𝟙_ (Over (Sp R)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Odd m → IsUnit (m : R) → M.IsLB → Out.RelAmple A M → (∀ i, pt i ^ m = 1) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ A), y ^ m = 1 → ∃! c : Ix g m, Out.linComb (fun i => toUnit (Over.mk x) ≫ pt i) (fun i => (c i).val) = y) → DenseP {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), RingHom.ker x = q ∧ IsGrpPullback Pl.A A (spMap x) φ ∧ LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ)} → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ Out.Sym A L ∧ Out.RelAmple A L ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (Pl : Out.PolAV (Sp K)) (φ : Pl.A.left ⟶ A.left), IsGrpPullback Pl.A A (spMap x) φ → LBIso (lbPow Pl.L (m ^ 2)) (M.pull φ) → LBIso Pl.L (L.pull φ) :=
  exists_descended_of GlobalTheory.seesaw_rigidified_of_dense GlobalTheory.sym_and_linearisation_odd
    GlobalTheory.pol_iso_symmetrised_root GlobalTheory.AbLaw.CubeAssembly.cube_gen

end GlobalTheory.OddDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleDeeperLevelCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevCover

theorem levelCover_closed : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (B : Type) [Field B] (b : Base l B) (b₂ : Base l₂ B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), 1 ≤ D.p + D.q → l.Dvd l₂ → b.ρ = b₂.ρ → b.ζ = b₂.ζ ^ (l₂.A / l.A) → ∃ (S₂ : Scheme.{0}) (π : S₂ ⟶ S) (o₂ : Obj D l₂ b₂ (π ≫ s)) (m : SABMap o₂.t o.t π), IsFinite π ∧ Etale π ∧ Surjective π ∧ ((∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left) ∧ (∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)) ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f), (∀ a, (o'.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = f ≫ (o.eta a).left) ∧ (∀ a, (o'.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = f ≫ (o.etaA a).left) → ∃! h : T ⟶ S₂, h ≫ π = f ∧ ∃ u : ObjMap o' o₂ h, u.toSABMap.φ ≫ m.φ = m'.φ :=
  fun hL => GlobalTheory.LevCover.levelCover_field hL GlobalTheory.LiePull.lieMult_pull GlobalTheory.pol_pull
    GlobalTheory.obj_isAbelianScheme_dim_rigidified_sym GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift
    GlobalTheory.tateIso_differ_by_similitude GlobalTheory.exists_finiteEtale_latticeTorsionHom
    (GlobalTheory.exists_clopen_weilIs_iff hL)
    (GlobalTheory.SimMult.exists_sim_trivial_of_mult GlobalTheory.SimAlg.sim_group GlobalTheory.exists_sim_lift)

end GlobalTheory.LevCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientPrincipalTriple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem exists_heckeQuotient_triple_of_laws : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  intro laws E _ _ _ H k _ _ _ t g p C hp hprop hsm hamp hK hst hpow
    hweil hcard
  have glob : Out.GlobalFnsSt := laws.globalFns
  have cube := GlobalTheory.Moduli.cube_of_isLB
  have cubeDesc := GlobalTheory.cube_descends_along_etale_isogeny glob
  have quot := GlobalTheory.exists_quotient_by_finite_group_of_points laws
  have split := GlobalTheory.lbPow_descends_of_isotropic_of_laws laws
  have princ := GlobalTheory.kTriv_of_descent laws
  have amp := GlobalTheory.relAmple_finite_pow_iso
  have prim := GlobalTheory.PrimNorm.exists_primitive_normalisation glob
  have seesaw := _root_.GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian glob
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp k) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  obtain ⟨B, gB, ψ, hB, hψ, hf, he, hs, hker, huniv⟩ :
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : t.G ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧
        Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧
        ∀ (Y : Over (Sp k)) (f : t.G ⟶ Y), (∀ x ∈ C, ((toUnit t.G ≫ x) * 𝟙 t.G) ≫ f = f) →
          ∃! f' : B ⟶ Y, ψ ≫ f' = f := quot k P C hfin
  have := hB.comm
  obtain ⟨M, hM, hiso⟩ : ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) :=
    split k P (p ^ 2) C B ψ hn (Nat.cast_ne_zero.2 hn.ne') hpow hweil hψ hf he hs hker
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen :=
    cubeDesc k t.G B ψ M hA hB hM hψ hf he hs (cube _ P (M.pull ψ.left) (pull_isLB hM _))
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hid : IsFinite (𝟙 t.G : t.G ⟶ t.G).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple t.G (lbPow t.PP.L (p ^ 2)) :=
    (amp _ t.G t.G (𝟙 _) t.PP.L (p ^ 2) hn hA hA hL hid).2.1.2 hamp

  have hMamp : Out.RelAmple B M :=
    (amp _ t.G B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs
      ((amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁)

  have fac : ∀ (Y : Over (Sp k)) [GrpObj Y] (f : t.G ⟶ Y) [IsMonHom f], (∀ x ∈ C, x ≫ f = 1) →
      ∃ f' : B ⟶ Y, ψ ≫ f' = f := fun Y _ f _ h =>
    (huniv Y f fun x hx => by
      rw [MonObj.mul_comp, Category.assoc, h x hx, MonObj.comp_one, _root_.one_mul, Category.id_comp]).exists
  have canc : ∀ (Y : Over (Sp k)) (f f' : B ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    (huniv Y (ψ ≫ f) fun x hx => by
      rw [← Category.assoc, MonObj.mul_comp, Category.assoc, (hker x).2 hx, MonObj.comp_one, _root_.one_mul,
        Category.id_comp]).unique rfl h.symm
  have hact : ∀ a, ∃ f' : B ⟶ B, ψ ≫ f' = t.act.act a ≫ ψ := fun a => by
    have := t.act.hom a
    exact fac B _ fun x hx => by rw [← Category.assoc]; exact (hker _).2 (hst x hx a)
  choose α hα using hact
  let act : OAct (𝓞 E) B :=
    { act := α
      hom := fun a => laws.rigidity _ B B hB hB _ (by
        have := t.act.hom a
        rw [← IsMonHom.one_hom ψ, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom])
      one := canc _ _ _ (by rw [hα, t.act.one, Category.id_comp, Category.comp_id])
      mul := fun a b => canc _ _ _ (by
        rw [hα, t.act.mul, ← Category.assoc ψ, hα, Category.assoc, Category.assoc, hα])
      add := fun a b => canc _ _ _ (by rw [hα, t.act.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) }
  have hαhom : ∀ a, IsMonHom (α a) := act.hom

  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]

  have hpowhom : IsMonHom (𝟙 t.G ^ p ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[t.G] : 𝟙_ _ ⟶ t.G) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  obtain ⟨π, hπ⟩ := fac t.G (𝟙 t.G ^ p ^ 2) fun x hx => by rw [MonObj.comp_pow, Category.comp_id, hpow x hx]
  have hπψ : π ≫ ψ = 𝟙 B ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := hαhom a
    have := hαhom (H.bar a)
    have adjA : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G),
        lam m (u ≫ ψ ≫ α a) (v ≫ ψ) = lam m (u ≫ ψ) (v ≫ ψ ≫ α (H.bar a)) := by
      intro T u v
      rw [hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ α a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp k)} (x y : T ⟶ B), lam m (x ≫ α a) y = lam m x (y ≫ α (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M)
          (cubeLB B ![fst B B ≫ α a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine seesaw k B B _ M hB hB hM hMamp hN (val _ _ ?_) ?_ (val _ _ ?_)
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · have hs' : Surjective (𝟙 t.G ^ p ^ 2).left := (laws.mulN _ P (p ^ 2) hn).2.2.1
      have hs'' : Surjective ((𝟙 t.G ^ p ^ 2) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
      refine dense_image_points ((𝟙 t.G ^ p ^ 2) ≫ ψ) _ fun u => val _ _ ?_
      have h := adjψ (toUnit B ≫ u) π
      rw [← Category.assoc π, hπψ, MonObj.pow_comp, lam_pow_right hM hΘ, lam_pow_right hM hΘ] at h
      rw [MonObj.pow_comp, MonObj.comp_pow, MonObj.comp_pow, MonObj.pow_comp, lam_pow_left hM hΘ,
        lam_pow_left hM hΘ]
      simpa only [Category.assoc, Category.id_comp] using h
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ := prim E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (α H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  have a₂ : Out.RelAmple t.G (PP.L.pull ψ.left) :=
    (amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hP' _) hfinal a₁
  have a₃ : Out.RelAmple B PP.L :=
    (amp _ t.G B ψ PP.L 1 one_pos hA hB hP' hf).2.2.1 inferInstance hs a₂
  have hc : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ t.G // x ≫ ψ = 1} = (p ^ 2) ^ g := by
    rw [← pow_mul, ← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hlam : LBIso (abelian₂ t.G (lbPow t.PP.L (p ^ 2))) (abelian₂ t.G (PP.L.pull ψ.left)) := by
    refine (cls_eq_iff (LB.isLB_linComb hn' _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two hn' _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [(cls_eq_iff hn' (pull_isLB hP' _)).2 hfinal]
  have a₄ : Out.KTriv B PP.L := princ k P (p ^ 2) B ψ PP.L hn hB hP' hψ hf he hs hc hlam
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, hψ, hf, he, hs, hker, fun a => (hα a).symm, hfinal⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtensStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_polarisedAbelianSchemes_dvr_of_fieldExtension : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (P P' : PolAV (Sp V)) (C : Type) [Field C] [Algebra (FractionRing V) C] (φ : TF (R := V) C ⊗ P.A ≅ TF (R := V) C ⊗ P'.A), φ.hom ≫ fst _ _ = fst _ _ → lift (𝟙 (TF (R := V) C)) (1 : TF (R := V) C ⟶ P.A) ≫ φ.hom ≫ snd _ _ = 1 → LBIso (P.L.pull (snd (TF (R := V) C) P.A).left) (P'.L.pull (φ.hom ≫ snd (TF (R := V) C) P'.A).left) → ∀ (κ : TF (R := V) C ⟶ TK V) (g : TK V ⊗ P.A ⟶ P'.A), κ ▷ P.A ≫ g = φ.hom ≫ snd _ _ → ∃ Ψ : P.A ≅ P'.A, IsMonHom Ψ.hom ∧ φ.hom ≫ snd _ _ = snd _ _ ≫ Ψ.hom ∧ LBIso P.L (P'.L.pull Ψ.hom.left) := by
  first | exact @GlobalTheory.IsoOverField.exists_iso_over_dvr | exact GlobalTheory.IsoOverField.exists_iso_over_dvr | (intros; apply GlobalTheory.IsoOverField.exists_iso_over_dvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocalMultiplicationPullbackThetaEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.EmbedLocal

theorem exists_emb_projRep :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh x v → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (σ : _), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ t.Emb m (Over.mk (spMap φ ≫ x)) σ ∧ ProjRep (idealOf (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ (𝟙 _)) (fst (Over.mk (spMap φ ≫ x)) t.A).left _ σ :=
  of_parts GlobalTheory.exists_emb_locally _root_.GlobalTheory.emb_baseChange _root_.GlobalTheory.EmbSpan.emb_span_eq_top _root_.GlobalTheory.FibreEmbed.projRep_fibre GlobalTheory.FibreEmbed.projRep_of_fibres

end GlobalTheory.ZM.EmbedLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem exists_point_of_isPeriod : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT hL
  have hG : Out.GlobalFnsSt := hL.globalFns
  exact GlobalTheory.exists_point_of_period hT hL GlobalTheory.Moduli.cube_of_isLB GlobalTheory.principalTorus_algebraic
    (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (_root_.GlobalTheory.lbIso_cubeLB_of_pairing_adjoint hL)
    (GlobalTheory.PrimNorm.exists_primitive_normalisation hG) (GlobalTheory.kTriv_of_descent hL)
    GlobalTheory.relAmple_finite_pow_iso (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.Moduli
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTorsionSemiAbelian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem finite_torsion_semiAbelian :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} :=
  TorsionFinite.finite_torsion_semiAbelian_of_abelian AbTorsionFinite.finite_torsion

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAdjointPrimitiveOfDenseEighthPowersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers : Out.GlobalFnsSt → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Dense (fromSet em (SharpClass (b := b) W a bas em) t) → (∀ j j', (a j).transpose * (W + W.transpose) = (W + W.transpose) * a j' → LBIso (cubeLB t.A ![fst t.A t.A ≫ t.act j, snd t.A t.A] t.L) (cubeLB t.A ![fst t.A t.A, snd t.A t.A ≫ t.act j'] t.L)) ∧ ∀ j, (W + W.transpose) * a j = W → LBIso t.L (cubeLB t.A ![𝟙 t.A, t.act j] t.L) := by
  first | exact @GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | exact GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense | (intros; apply GlobalTheory.SharpAdjoint.adjoint_primitive_of_dense <;> assumption)
end

