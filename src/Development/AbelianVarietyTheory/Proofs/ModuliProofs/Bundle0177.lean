module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnTheta
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NatCastMemConj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaClassical

theorem constFn_mul {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) (a b : ℂ) :
    constFn f U (a * b) = constFn f U a * constFn f U b := by
  unfold constFn
  rw [map_mul, map_mul]

theorem constFn_one {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : constFn f U 1 = 1 := by
  unfold constFn
  rw [map_one, map_one]

theorem constFn_top (a : ℂ) :
    (⊤ : (Sp ℂ).Opens).ι.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) =
      constFn ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _) ⊤ a := by
  rw [Category.comp_id]
  exact congrArg (fun f : Γ(Sp ℂ, ⊤) ⟶ Γ((⊤ : (Sp ℂ).Opens).toScheme, (⊤ : (Sp ℂ).Opens).ι ⁻¹ᵁ ⊤) =>
    f.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a))
    (Scheme.Hom.appLE_eq_app (⊤ : (Sp ℂ).Opens).ι (U := ⊤)).symm

theorem isThetaPtOver (hL : Out.Laws) (hL2 : Out.Laws2) (hT : ThetaUnifAV) (P : Out.PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ)
    (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
    {I : Type} (x : I → (T ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0)
    (hx : ∀ i, p ≫ x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)))
    (hU : ∀ i, ∃ U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T,
      Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) (x i) U) :
    Out.IsThetaPtOver P N x (fun i => constFn T.hom ⊤
      (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
        θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ)))) := by
  have hC := GlobalTheory.Moduli.cube_of_isLB
  obtain ⟨th, hgen, hth⟩ := GlobalTheory.exists_isGenSec_of_isThetaFn hL hL2 hC hT P u Hm χ θ T p hAH hθ h0
  obtain ⟨s1, α, c, hc, hα, htw, hs1⟩ := GlobalTheory.exists_twistPull_mul_fn hL hL2 hC hT P u Hm χ N θ T p th hAH hN hth
  obtain ⟨τ, hτ, hval⟩ := GlobalTheory.OriginValue.exists_gen_isValueAt_origin P u ((N : ℤ) ^ 2) T p
  choose U hU using hU
  choose s2 hs2 using fun i => GlobalTheory.ThetaPtExist.exists_isTwistPull P.isLB (Out.translT P.A (U i).pt)
    (Out.translPt P.A (U i).pt) (lift_snd _ _) ((N : ℤ) ^ 2) ((N : ℤ) ^ 2) (U i).φ (U i).isGen s1
  have hact := fun i => _root_.GlobalTheory.symLift_act_in_frame hL hL2 hC hT P u Hm χ N (l i) (fun z => c * θ ((N : ℂ) • z)) T p
    (x i) (U i) s1 (s2 i) hAH hN (hx i) (hU i) (hs2 i) hs1
  have hv := fun i => hval (s2 i) (fun z => χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) *
    hermForm Hm (l i) (l i) - Real.pi * hermForm Hm z (l i)) *
      (c * θ ((N : ℂ) • (z + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))))) (hact i)
  have hcu : IsUnit (constFn T.hom ⊤ c⁻¹) :=
    IsUnit.of_mul_eq_one (constFn T.hom ⊤ c) (by rw [← constFn_mul, inv_mul_cancel₀ hc, constFn_one])
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨th, s1, α, τ, U, s2, _, hcu.unit, hgen, hα, hτ, htw, hU, hs2, hv, fun i => ?_⟩
  refine Eq.trans (congrArg (constFn T.hom ⊤) ?_) (constFn_mul T.hom ⊤ c⁻¹ _)
  have e1 : hermForm Hm 0 (l i) = 0 := by simp [hermForm]
  have e2 : (N : ℂ) • (0 + ((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ)) = (N : ℂ)⁻¹ • (l i : Fin P.g → ℂ) := by
    rw [zero_add, smul_smul]
    congr 1
    field_simp
  simp only [e1, e2, mul_zero, sub_zero]
  field_simp

theorem exists_symLift (hL : Out.Laws) (P : Out.PolAV (Sp ℂ)) (n : ℕ) (k : ℤ) (hk : k = n) (hn : Odd n)
    (x : Out.baseOver (Sp ℂ) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ U : Out.ThetaGrp P.A P.L k (Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤),
      Out.SymLift P.A P.L k n (Out.overResι ⊤ ≫ x) U := by
  subst hk
  have hu : IsUnit (n : Γ(Sp ℂ, ⊤)) := by
    have h : IsUnit (n : ℂ) := IsUnit.mk0 _ (by exact_mod_cast hn.pos.ne')
    simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  obtain ⟨V, hV, U, hU⟩ := (hL.symLift (Sp ℂ) P n hn hu _ x hx).1 (default : PrimeSpectrum ℂ)
  obtain rfl : V = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hV
  exact ⟨U, hU⟩

theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) :
    u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_nsmul {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex (n • z) = u.ex z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_sum {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {r : ℕ} (z : Fin r → Fin g → ℂ) (a : Fin r → ℕ) :
    u.ex (∑ i, a i • z i) = Out.linComb (fun i => u.ex (z i)) a := by
  induction r with
  | zero => simp [Out.linComb, ex_zero]
  | succ r ih =>
    rw [Fin.sum_univ_succ, u.ex_add, ih, ex_nsmul]
    simp [Out.linComb, List.ofFn_succ]

theorem hasTh_classical : Out.Laws → Out.Laws2 → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (t : TObj g (N' ^ 2) J b (spMap em)) (u : HolUnif t.A t.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (lam : Fin (2 * g) → u.Λ), Odd N' → u.IsAH Hm χ → u.IsThetaFn Hm χ 1 θ → θ ≠ 0 → (∀ i, (t.pt i).left = (u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ))).left) → t.HasTh (𝟙 _) (fun a => χ (∑ i, ((a i).val : ℤ) • lam i) * Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ)) (∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) * θ ((N' : ℂ)⁻¹ • ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ))) := by
  intro hL hL2 hT o _ g N' J b em t u Hm χ θ lam hN hAH hθ h0 hpt
  have hN0 : (N' : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  haveI := t.ab.comm
  refine ⟨hN, ?_, fun q => ⟨⊤, trivial, ?_⟩⟩
  · have h : IsUnit (N' : ℂ) := IsUnit.mk0 _ hN0
    have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rw [map_natCast] at h'
    exact h'
  let T : Over (Sp ℂ) := Out.overRes (T := Out.baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ Out.overResι (T := Out.baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have hpt' : t.pt = fun i => u.ex (((N' : ℂ) ^ 2)⁻¹ • (lam i : Fin g → ℂ)) :=
    funext fun i => Over.OverMorphism.ext (hpt i)
  have hcoe : ∀ a : Ix g (N' ^ 2), ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ) =
      ∑ i, ((a i).val : ℂ) • (lam i : Fin g → ℂ) := fun a => by
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hlab : ∀ a : Ix g (N' ^ 2), t.lab a =
      u.ex (((N' : ℂ) ^ 2)⁻¹ • ((∑ i, ((a i).val : ℤ) • lam i : u.Λ) : Fin g → ℂ)) := fun a => by
    rw [hcoe, Finset.smul_sum, TObj.lab, hpt']
    refine (ex_sum u _ _).symm.trans (congrArg u.ex (Finset.sum_congr rfl fun i _ => ?_))
    rw [smul_comm, Nat.cast_smul_eq_nsmul]
  have htor : ∀ a : Ix g (N' ^ 2), t.lab a ^ (N' ^ 2) = 1 := fun a => by
    rw [TObj.lab, Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, t.torsion, one_pow]
  have key := isThetaPtOver hL hL2 hT t.pol u Hm χ θ N' T p
    (fun a : Ix g (N' ^ 2) => Out.overResι ⊤ ≫ t.lab a) (fun a => ∑ i, ((a i).val : ℤ) • lam i)
    hN hAH hθ h0 (fun a => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ t.lab a) hp).trans
      ((Category.id_comp _).trans (hlab a))))
    (fun a => exists_symLift hL t.pol (N' ^ 2) _ (by push_cast; rfl) hN.pow (t.lab a) (htor a))
  convert key using 2 with a a
  · congr 1
  · refine (constFn_top _).trans ?_
    refine congrArg (constFn T.hom ⊤) ?_
    exact congrArg (fun w : Fin g → ℂ => χ (∑ i, ((a i).val : ℤ) • lam i) *
      Complex.exp (-(Real.pi / 2 / (N' : ℂ) ^ 2) * hermForm Hm w w) * θ ((N' : ℂ)⁻¹ • w)) (hcoe a).symm

end GlobalTheory.ThetaClassical
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteSurjectiveOfPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckeCompare

open GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckePoint GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem splitPrime_iff (l : Level H) (p : ℕ) (P : Ideal (𝓞 E)) : IsSplitPrimeOff l p P ↔
    P.IsMaximal ∧ P ⊔ P.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧ p.Prime ∧ (p : 𝓞 E) ∈ P ∧ ¬ p ∣ l.M' := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨h₂, h₂.coprime_of_ne (conj_isMaximal H P) (Ne.symm h₄), h₁, h₃, h₅⟩
  · rintro ⟨h₂, h₄, h₁, h₃, h₅⟩
    refine ⟨h₁, h₂, h₃, fun h => h₂.ne_top ?_, h₅⟩
    rw [← h₄, show P.map (H.bar : 𝓞 E →+* 𝓞 E) = P from h, sup_idem]

section Fibre

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) (a : 𝓞 E) : (T ⟶ t.G) →* (T ⟶ t.G) :=
  haveI := t.act.hom a
  MonoidHom.mk' (fun x => x ≫ t.act.act a) fun x y => MonObj.mul_comp x y _

theorem isAct_ptAct {S : Scheme.{0}} (t : SAB H S) (T : Over S) : IsAct (ptAct t T) :=
  ⟨fun x => by show x ≫ _ = x; rw [t.act.one, Category.comp_id],
    fun a c x => by show x ≫ _ = (x ≫ _) ≫ _; rw [t.act.mul, Category.assoc],
    fun a c x => by show x ≫ _ = (x ≫ _) * (x ≫ _); rw [t.act.add, MonObj.comp_mul]⟩

abbrev ptWeil (t : SAB H (Sp k)) : ℕ → Pts t → Pts t → kˣ → Prop :=
  fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c)

theorem ptWeil_one (t : SAB H (Sp k)) (n : ℕ) (x y : Pts t) : ptWeil t n x y 1 ↔ Out.WeilIs t.G t.PP.L n x y 1 :=
  iff_of_eq (congrArg (Out.WeilIs t.G t.PP.L n x y) unitOn_one)

theorem kerSet_eq (t : SAB H (Sp k)) (p : ℕ) (P : Ideal (𝓞 E)) (C₀ : Subgroup (Pts t)) :
    kerSet (ptAct t _) (ptWeil t) p P (P.map (H.bar : 𝓞 E →+* 𝓞 E)) C₀ = heckeKernel t p P C₀ := by
  ext x
  constructor
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).1 (h₅ c hc)⟩
  · rintro ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨x₁, x₂, x₃, h, h₁, h₂, h₃, h₄, fun c hc => (ptWeil_one t p _ _).2 (h₅ c hc)⟩

abbrev objPol (o : Obj D l b s) : Out.PolAV (Sp k) :=
  polOf o.t o.proper o.ample o.ktriv (obj_isAbelianScheme_dim_rigidified_sym E H D l B b _ s o).2.1

theorem tate_facts [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) :
    Nonempty (TateIso D k (Pts o.t) (fun a x => ptAct o.t _ a x) (ptWeil o.t)) ∧ Uniq (ptWeil o.t) ∧
      ∀ p : ℕ, 0 < p → Nat.card {x : Pts o.t // x ^ p = 1} = p ^ (2 * (Module.finrank ℚ E / 2 * (D.p + D.q))) := by
  obtain ⟨-, I, -⟩ := o.geom k (𝟙 _) (Spec.preimage s).hom (by simp [spMap])
  exact ⟨⟨I⟩, fun n z w c c' _ hz hw h h' =>
    (unitOn_bijective k).1 (((hL.weil _ (objPol o) n _).1 z w hz hw).unique h h'),
    fun p hp => (hL.mulN _ (objPol o) p hp).2.2.2.2 k (𝟙 _) (Nat.cast_ne_zero.2 hp.ne')⟩

theorem weil_sq (t : SAB H (Sp k)) (p : ℕ) (x y : Pts t) :
    ptWeil t (p * p) x y 1 ↔ Out.WeilIs t.G t.PP.L ((p : ℤ) ^ 2) x y 1 := by
  rw [ptWeil_one, Nat.cast_mul, pow_two]

theorem card_tors (t : SAB H (Sp k)) (p : ℕ) :
    Nat.card (t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)})) = Nat.card {x : Pts t // x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => (isAct_ptAct t _).kill_span_iff p x)

theorem card_inter_tors (t : SAB H (Sp k)) (p : ℕ) (C : Subgroup (Pts t)) :
    Nat.card ((C : Set (Pts t)) ∩ t.tors (𝟙_ _) (Ideal.span {(p : 𝓞 E)}) : Set (Pts t)) =
      Nat.card {x : Pts t // x ∈ C ∧ x ^ p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun x => and_congr_right' ((isAct_ptAct t _).kill_span_iff p x))

variable [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}
include hL

theorem exists_heckeKer_of_datum (h : IsSplitPrimeOff l p P) {i : ℕ} {C₀ : Subgroup (Pts o.t)}
    (h₀ : IsHeckeDatum o.t P i C₀) :
    ∃ C : Subgroup (Pts o.t), (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ ∧ o.t.HeckeKer (𝟙_ _) D P p i C := by
  obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
  have hf : Finite {x : Pts o.t // x ^ p = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact (pow_pos hp.pos _).ne')
  obtain ⟨C, e, c₁, c₂, c₃, c₄, c₅, c₆⟩ := exists_subgroup I hu (isAct_ptAct _ _) hco hp.pos hpP h₀.1 h₀.2.1 hf
  exact ⟨C, e.trans (kerSet_eq _ _ _ _), c₁, c₂, c₃, fun x hx y hy => (weil_sq _ _ _ _).1 (c₄ x hx y hy),
    c₅.trans (hc p hp.pos), by rw [card_tors, card_inter_tors, c₆, h₀.2.2.2]⟩

theorem heckeKer_iff (h : IsSplitPrimeOff l p P) (i : ℕ) (C : Subgroup (Pts o.t)) :
    o.t.HeckeKer (𝟙_ _) D P p i C ↔
      ∃ C₀, IsHeckeDatum o.t P i C₀ ∧ (C : Set (Pts o.t)) = heckeKernel o.t p P C₀ := by
  constructor
  · rintro ⟨c₁, -, c₃, c₄, c₅, c₆⟩
    obtain ⟨hP, hco, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨⟨I⟩, hu, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hf : Finite {x : Pts o.t // x ^ p = 1} := Nat.finite_of_card_ne_zero (by rw [hc p hp.pos]; exact hpos.ne')
    obtain ⟨d₁, d₂, e⟩ := eq_kerSet I hu (isAct_ptAct _ _) hco hp.pos hpP hf C c₁ c₃
      (fun x hx y hy => (weil_sq _ _ _ _).2 (c₄ x hx y hy)) (c₅.trans (hc p hp.pos).symm)
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₀ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact ⟨_, ⟨d₁, d₂, Nat.finite_of_card_ne_zero h₀.2, mul_left_cancel₀ h₀.1 (hm.symm.trans c₆)⟩,
      e.trans (kerSet_eq _ _ _ _)⟩
  · rintro ⟨C₀, h₀, e⟩
    obtain ⟨C', e', h'⟩ := exists_heckeKer_of_datum hL o h h₀
    rwa [SetLike.coe_injective (e.trans e'.symm)]

end Fibre

section Isogeny

variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}

def IsIsogenyOnPoints (o o' : Obj D l b s) (p : ℕ) (C : Set (Pts o.t)) (ψ : o.t.G ⟶ o'.t.G) : Prop :=
  IsMonHom ψ ∧ (∀ a, o.t.act.act a ≫ ψ = ψ ≫ o'.t.act.act a) ∧
  (∀ y : Pts o'.t, ∃ x, x ≫ ψ = y) ∧ (∀ x, x ≫ ψ = 1 ↔ x ∈ C) ∧
  (∀ (n : ℕ) (x x' : Pts o.t) (c : kˣ), n.Coprime p → Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) →
    Out.WeilIs o'.t.G o'.t.PP.L n (x ≫ ψ) (x' ≫ ψ) (unitOn (c ^ (p ^ 2)))) ∧
  ∀ p' : ℕ, p * p' ≡ 1 [MOD l.M'] → ∀ a, o.eta (p' • a) ≫ ψ = o'.eta a ∧ o.etaA (p' • a) ≫ ψ = o'.etaA a

end Isogeny

section Transfer

variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem exists_fibre_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) :
    ∃ (ρ : Pts o.t ≃* (Over.mk y ⟶ u.t.G)) (e : o.t.G.left ≅ pullback u.t.G.hom y),
      (∀ x, (ρ x).left = x.left ≫ m.cm.F) ∧
      e.hom ≫ pullback.snd _ _ = o.t.G.hom ∧ (∀ x, fibPt _ (ρ x) = x.left ≫ e.hom) ∧
      (∀ a x, ρ (x ≫ o.t.act.act a) = ρ x ≫ u.t.act.act a) ∧
      (∀ (n : ℤ) x x' (c : kˣ), Out.WeilIs o.t.G o.t.PP.L n x x' (unitOn c) ↔
        Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') (unitOn c)) ∧
      (∀ a, ρ (o.eta a) = toUnit _ ≫ u.eta a) ∧ ∀ a, ρ (o.etaA a) = toUnit _ ≫ u.etaA a := by
  obtain ⟨ρ, hρ⟩ := exists_ptsEquiv m.cart (𝟙_ (Over (Sp k))) y (Category.id_comp _)
  have key : ∀ (T : Over (Sp k)) (y' : T.left ⟶ X) (_ : T.hom ≫ y = y') (n : ℤ) (x x' : T ⟶ o.t.G)
      (x₀ x₀' : Over.mk y' ⟶ u.t.G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ m.cm.F → x₀'.left = x'.left ≫ m.cm.F →
      (Out.WeilIs o.t.G o.t.PP.L n x x' c ↔ Out.WeilIs u.t.G u.t.PP.L n x₀ x₀' c) := by
    intro T y' e
    subst e
    obtain ⟨w, hw, -⟩ := m.lin
    exact fun n x x' x₀ x₀' c =>
      weilIs_grpPullback_of_comm _ _ _ _ y m.cm.F _ _ u.t.PP.isLB o.t.PP.isLB m.cart ⟨w, hw⟩ T n x x' x₀ x₀' c
  have tu : (toUnit (Over.mk y)).left = y := by simp
  refine ⟨ρ, m.cart.1.isoPullback, hρ, m.cart.1.isoPullback_hom_snd, fun x => ?_,
    fun a x => Over.OverMorphism.ext ?_, fun n x x' c => key _ y (Category.id_comp _) n x x' _ _ _ (hρ x) (hρ x'),
    fun a => Over.OverMorphism.ext ?_, fun a => Over.OverMorphism.ext ?_⟩
  · apply pullback.hom_ext
    · rw [fibPt, pullback.lift_fst, hρ, Category.assoc, m.cart.1.isoPullback_hom_fst]
    · rw [fibPt, pullback.lift_snd, Category.assoc, m.cart.1.isoPullback_hom_snd]
      exact (Over.w x).symm
  · rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, m.act, Category.assoc]
  · rw [hρ, Over.comp_left, tu]; exact m.eta a
  · rw [hρ, Over.comp_left, tu]; exact m.etaA a

def SamePoints {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y) (C' : Set (Pts o.t))
    (C : Set (Over.mk y ⟶ u.t.G)) : Prop :=
  ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → (x ∈ C' ↔ x₀ ∈ C)

theorem heckeKer_transfer {u : Obj D l b sX} {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    {C' : Subgroup (Pts o.t)} {C : Subgroup (Over.mk y ⟶ u.t.G)} (h : SamePoints m C' C) (P : Ideal (𝓞 E))
    (p i : ℕ) : u.t.HeckeKer (Over.mk y) D P p i C ↔ o.t.HeckeKer (𝟙_ _) D P p i C' := by
  obtain ⟨ρ, -, e₀, -, -, e₃, e₄, -⟩ := exists_fibre_equiv u m
  have mem : ∀ x, x ∈ C' ↔ ρ x ∈ C := fun x => h x _ (e₀ x)
  have tor : ∀ J x, x ∈ o.t.tors (𝟙_ _) J ↔ ρ x ∈ u.t.tors (Over.mk y) J := fun J x =>
    forall₂_congr fun a _ => by rw [← e₃, map_eq_one_iff _ ρ.injective]
  have wl : ∀ (n : ℤ) x x', Out.WeilIs o.t.G o.t.PP.L n x x' 1 ↔ Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x') 1 :=
    fun n x x' => (iff_of_eq (congrArg (Out.WeilIs o.t.G o.t.PP.L n x x') unitOn_one)).symm.trans ((e₄ n x x' 1).trans
      (iff_of_eq (congrArg (Out.WeilIs u.t.G u.t.PP.L n (ρ x) (ρ x')) unitOn_one)))
  have c₁ : Nat.card C' = Nat.card C := Nat.card_congr (ρ.toEquiv.subtypeEquiv mem)
  have c₂ : ∀ J, Nat.card (o.t.tors (𝟙_ _) J) = Nat.card (u.t.tors (Over.mk y) J) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv (tor J))
  have c₃ : ∀ J, Nat.card ((C' : Set (Pts o.t)) ∩ o.t.tors (𝟙_ _) J : Set (Pts o.t)) =
      Nat.card ((C : Set (Over.mk y ⟶ u.t.G)) ∩ u.t.tors (Over.mk y) J : Set (Over.mk y ⟶ u.t.G)) := fun J =>
    Nat.card_congr (ρ.toEquiv.subtypeEquiv fun x => and_congr (mem x) (tor J x))
  unfold SAB.HeckeKer
  rw [c₁, c₂, c₃]
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ Iff.rfl)))
  · rw [ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (forall_congr' fun a => by rw [← e₃, mem])
  · refine forall₂_congr fun J _ => ?_
    rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (tor J x).symm (mem x).symm
  · rw [Set.subset_def, Set.subset_def, ρ.surjective.forall]
    exact forall_congr' fun x => imp_congr (mem x).symm (tor _ x).symm
  · rw [ρ.surjective.forall]
    refine forall_congr' fun x => imp_congr (mem x).symm ?_
    rw [ρ.surjective.forall]
    exact forall_congr' fun x' => imp_congr (mem x').symm (wl _ x x').symm

end Transfer

section Statements

variable {k : Type} [Field k]

theorem exists_fibre_obj (Xo : Moduli D l) (y y' : Sp k ⟶ Xo.X) (h : y' ≫ Xo.s = y ≫ Xo.s) :
    ∃ o : Obj D l (baseKA l) (y ≫ Xo.s), Nonempty (ObjMap o Xo.univ y') :=
  obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (y ≫ Xo.s) y' rfl rfl
    (by rw [h, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ

end Statements

end GlobalTheory.HeckeCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivAwayOfKTrivFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private theorem isGrpPullback_pullback_obj {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback _ _, ?_⟩
  intro T x y x₀ y₀ hx hy
  have e : (lift x₀ y₀).left =
      (lift x y).left ≫ (Functor.LaxMonoidal.μ (Over.pullback f) G G).left ≫
        pullback.fst (G ⊗ G).hom f := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_fst]
      simp only [Over.lift_left, pullback.lift_fst, pullback.lift_fst_assoc, hx]
    · simp only [Category.assoc]
      rw [Over.μ_pullback_left_fst_snd]
      simp only [Over.lift_left, pullback.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst_assoc, hy]
  rw [Hom.mul_def, Hom.mul_def, Over.comp_left, Over.comp_left, e, Functor.obj.μ_def, Over.comp_left]
  simp only [Category.assoc]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  first
    | exact (pullback.lift_fst _ _ _).symm
    | (erw [Over.pullback_map_left]; simp)

theorem kTriv_away_of_kTriv_fibre : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (K : Type) [Field K] (x : R →+* K), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Out.KTriv ((Over.pullback (spMap x)).obj A) (L.pull (pullback.fst A.hom (spMap x))) → ∃ f : R, x f ≠ 0 ∧ Out.KTriv ((Over.pullback (spMap (algebraMap R (Localization.Away f)))).obj A) (L.pull (pullback.fst A.hom (spMap (algebraMap R (Localization.Away f))))) := by
  intro _ R _ _ A _ L K _ x hA hL hR hK
  obtain ⟨f, hf, H⟩ := _root_.GlobalTheory.KTrivSpread.exists_kTriv_of_isUnit R A L K x ((Over.pullback (spMap x)).obj A)
    (pullback.fst A.hom (spMap x)) hA hL hR (isGrpPullback_pullback_obj A (spMap x)) hK
  exact ⟨f, hf, H (Localization.Away f) (algebraMap R (Localization.Away f)) _ _
    (IsLocalization.Away.algebraMap_isUnit f) (isGrpPullback_pullback_obj A _)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlong
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem tangent_eq_constPt_of_tMap : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  intro hL hL2 o _ g n N' J b I Y u hN hu K _ x t hs h1 h2
  have hsub : Subsingleton (PrimeSpectrum (DualNumber K)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber K),
        p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom := by
      intro p
      have hp := p.isPrime
      have hle : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom ≤ p.asIdeal := by
        intro a ha
        have ha' : a.fst = 0 := ha
        apply hp.mem_of_pow_mem 2
        have : a ^ 2 = 0 := by
          rw [sq]; ext <;> simp [ha']
        rw [this]; exact p.asIdeal.zero_mem
      have hmax : (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨TrivSqZeroExt.inl c, rfl⟩)
      exact (hmax.eq_of_le hp.ne_top hle).symm
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have hsub' : Subsingleton (Sp (DualNumber K)) := hsub
  obtain ⟨p⟩ : Nonempty (Sp (DualNumber K)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber K)))
  obtain ⟨R, _, j, v, hj, ⟨q, _⟩, hv⟩ := _root_.GlobalTheory.ThetaLocal.exists_hasTh hL hL2 o g N' J b _ _ t hN p
  have hsurj : Function.Surjective j := fun y => ⟨q, Subsingleton.elim _ _⟩
  have hiso : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext y
    simpa using hsurj y
  have c1 := (hu R _ v).1 ((_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ u _ _ t x R j v h1).1 hv)
  have c2 := (hu R _ v).1 ((_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ u _ _ t (constPt x) R j v h2).1 hv)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (R := CommRingCat.of o) (S := CommRingCat.of R) (j ≫ x ≫ Y.s)
  have e1 : (j ≫ x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc]; exact hβ.symm
  have e2 : (j ≫ constPt x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc, ← hs]; exact hβ.symm
  have h := (Y.pts R β.hom v (Y.loc R β.hom _ v e1 c1)).unique ⟨e1, c1⟩ ⟨e2, c2⟩
  exact (cancel_epi j).1 h

end GlobalTheory.ZM
end

