module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SimilitudeDefiniteFormIsAlgebraicOnVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolyNormSqRoots
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS
open Polynomial

theorem exists_surj_of_torsion {N : Type} [AddCommGroup N] [Finite N] (l n c : ℕ) (hn : ∀ x : N, l ^ n • x = 0)
    (hc : Nat.card {x : N // l • x = 0} ≤ c) :
    ∃ π : (Fin c → ℤ) →ₗ[ℤ] N, Function.Surjective π := by
  classical
  let m : N →+ N := nsmulAddMonoidHom l
  have h1 : Nat.card (N ⧸ m.range) = Nat.card m.ker := by
    have a := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.range
    have b := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup m.ker
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange m).toEquiv, _root_.mul_comm] at b
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (a.symm.trans b)
  have h2 : Nat.card (N ⧸ m.range) ≤ Nat.card (Fin c) := by
    rw [h1, Nat.card_fin]; exact hc
  obtain ⟨e⟩ : Nonempty ((N ⧸ m.range) ↪ Fin c) := by
    have := Fintype.ofFinite (N ⧸ m.range)
    apply Function.Embedding.nonempty_of_card_le
    simpa using h2
  let v : Fin c → N := fun i => (Function.invFun e i).out
  let π : (Fin c → ℤ) →ₗ[ℤ] N := Fintype.linearCombination ℤ v
  have hv : ∀ i, v i ∈ LinearMap.range π := fun i => ⟨Pi.single i 1, by simp [π]⟩
  have key : ∀ j : ℕ, ∀ x : N, ∃ y : N, x - l ^ j • y ∈ LinearMap.range π := by
    intro j
    induction j with
    | zero => exact fun x => ⟨x, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      have h3 : (QuotientAddGroup.mk (v (e y)) : N ⧸ m.range) = QuotientAddGroup.mk y := by
        simp only [v, QuotientAddGroup.out_eq']
        exact Function.leftInverse_invFun e.injective _
      obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 h3
      have hz' : l • z = - v (e y) + y := hz
      refine ⟨z, ?_⟩
      have : x - l ^ (j + 1) • z = (x - l ^ j • y) + l ^ j • v (e y) := by
        rw [pow_succ, mul_smul, hz', smul_add, smul_neg]; abel
      rw [this]
      exact add_mem hy (nsmul_mem (hv _) _)
  refine ⟨π, fun x => ?_⟩
  obtain ⟨y, hy⟩ := key n x
  rwa [hn, sub_zero] at hy

theorem aeval_intertwine {M N : Type} [AddCommGroup M] [AddCommGroup N] (π : M →ₗ[ℤ] N) (S : Module.End ℤ M)
    (T : Module.End ℤ N) (h : ∀ x, T (π x) = π (S x)) (p : ℤ[X]) : ∀ x, aeval T p (π x) = π (aeval S p x) := by
  induction p using Polynomial.induction_on with
  | C a => intro x; rw [aeval_C, aeval_C, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]
  | add p q hp hq => intro x; simp [hp, hq]
  | monomial n a ih =>
    intro x
    rw [pow_succ, ← _root_.mul_assoc, map_mul, map_mul (aeval _) _ X, aeval_X, aeval_X, Module.End.mul_apply,
      Module.End.mul_apply, h, ih]

theorem exists_monic_of_surj {N : Type} [AddCommGroup N] (c : ℕ) (π : (Fin c → ℤ) →ₗ[ℤ] N)
    (hπ : Function.Surjective π) (T : Module.End ℤ N) :
    ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = c ∧ aeval T χ = 0 := by
  obtain ⟨S, hS⟩ := Module.projective_lifting_property π (T ∘ₗ π) hπ
  have h := aeval_intertwine π S T fun x => (LinearMap.congr_fun hS x).symm
  refine ⟨S.charpoly, S.charpoly_monic, by simp [LinearMap.charpoly_natDegree], ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hπ x
  rw [h, LinearMap.aeval_self_charpoly]
  simp

theorem exists_monic_torsion {M : Type} [AddCommGroup M] (l : ℕ) (hf : ∀ n : ℕ, Finite {x : M // l ^ n • x = 0})
    (T : Module.End ℤ M) : ∃ r : ℕ, ∀ n : ℕ, ∃ χ : ℤ[X], χ.Monic ∧ χ.natDegree = r ∧
      ∀ x : M, l ^ n • x = 0 → aeval T χ x = 0 := by
  refine ⟨Nat.card {x : M // l ^ 1 • x = 0}, fun n => ?_⟩
  let N : Submodule ℤ M := LinearMap.ker (l ^ n • LinearMap.id)
  have hN : ∀ x : M, x ∈ N ↔ l ^ n • x = 0 := fun x => Iff.rfl
  have : Finite N := by
    have := hf n
    exact Finite.of_equiv _ (Equiv.subtypeEquivRight fun x => (hN x).symm)
  have hT : ∀ x ∈ N, T x ∈ N := fun x hx => by
    rw [hN] at hx ⊢
    rw [← map_nsmul, hx, map_zero]
  have := hf 1
  obtain ⟨π, hπ⟩ := exists_surj_of_torsion (N := N) l n (Nat.card {x : M // l ^ 1 • x = 0})
    (fun x => Subtype.ext ((hN _).1 x.2))
    (Nat.card_le_card_of_injective (fun x => (⟨x.1.1, by rw [pow_one]; exact congrArg Subtype.val x.2⟩ :
      {x : M // l ^ 1 • x = 0})) fun x y h => Subtype.ext (Subtype.ext (by simpa using h)))
  obtain ⟨χ, h1, h2, h3⟩ := exists_monic_of_surj _ π hπ (T.restrict hT)
  refine ⟨χ, h1, h2, fun x hx => ?_⟩
  have h := aeval_intertwine N.subtype (T.restrict hT) T (fun _ => rfl) χ ⟨x, (hN x).2 hx⟩
  rw [h3] at h
  exact h

section
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

noncomputable def ptEnd (F : End B) (hF : IsMonHom F.asHom) (Z : Over S) :
    Module.End ℤ (Additive (Z ⟶ B)) :=
  (MonoidHom.toAdditive (IsMonHom.monoidHom F.asHom Z)).toIntLinearMap

theorem ptEnd_pow (F : End B) (hF : IsMonHom F.asHom) {Z : Over S} (x : Z ⟶ B) (n : ℕ) :
    (ptEnd F hF Z ^ n) (Additive.ofMul x) = Additive.ofMul (x ≫ (F ^ n).asHom) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, End.one_asHom, Category.comp_id]
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, End.mul_asHom]
    exact congrArg Additive.ofMul (Category.assoc x (F ^ n).asHom F.asHom)

theorem aeval_ptEnd (F : End B) (hF : IsMonHom F.asHom) {Z : Over S} (x : Z ⟶ B) (P : ℤ[X]) :
    aeval (ptEnd F hF Z) P (Additive.ofMul x) = Additive.ofMul (polyPt F P x) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, polyPt, ← List.prod_toFinset _ List.nodup_range,
    List.toFinset_range, ofMul_prod]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, ptEnd_pow, ofMul_zpow]

noncomputable def evalPt {Z : Over S} (x : Z ⟶ B) : Additive (B ⟶ B) →ₗ[ℤ] Additive (Z ⟶ B) :=
  (AddMonoidHom.mk' (fun f => Additive.ofMul (x ≫ Additive.toMul f))
    fun f g => by rw [toMul_add, MonObj.comp_mul, ofMul_mul]).toIntLinearMap

noncomputable def homSub (B : Over S) [GrpObj B] [IsCommMonObj B] : Submodule ℤ (Additive (B ⟶ B)) :=
  AddSubgroup.toIntSubmodule
    { carrier := {f | IsMonHom (Additive.toMul f)}
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul g) at hg
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        rw [Hom.mul_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f) at hf
        change IsMonHom (Additive.toMul f)⁻¹
        infer_instance }

end

theorem exists_poly_normSq_roots : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom F.asHom → PullPow F.asHom.left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by
  intro k _ _ B _ hB L hL F q hF hq
  have := hB.comm
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ (l : k) ≠ 0 := by
    by_cases h : ((2 : ℕ) : k) = 0
    · refine ⟨2 + 1, by norm_num, ?_⟩
      rw [Nat.cast_add, h]; simp
    · exact ⟨2, le_rfl, h⟩
  have hD := fun n : ℕ => _root_.GlobalTheory.TorsionDivisible.finite_torsion_and_divisible k B hB (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl)
  obtain ⟨Q, Q1, Q2, Q3, Q4⟩ := _root_.GlobalTheory.SS.exists_quadraticForm_end k B hB L hL
  obtain ⟨r, hr⟩ := exists_monic_torsion (M := Additive (𝟙_ (Over (Sp k)) ⟶ B)) l (fun n => (hD n).1) (ptEnd F hF _)
  have hT : ∀ f ∈ homSub B, ptEnd F hF B f ∈ homSub B := fun f hf => by
    change IsMonHom (Additive.toMul f) at hf
    change IsMonHom (Additive.toMul f ≫ F.asHom)
    infer_instance
  let e : homSub B := ⟨Additive.ofMul (𝟙 B), inferInstanceAs (IsMonHom (𝟙 B))⟩
  let φ : Module.End ℤ (homSub B) := (ptEnd F hF B).restrict hT
  have hev : ∀ (x : 𝟙_ (Over (Sp k)) ⟶ B) (p : ℤ[X]), aeval (ptEnd F hF _) p (Additive.ofMul x) =
      Additive.ofMul (x ≫ Additive.toMul (aeval φ p e).1) := fun x p => by
    have h := aeval_intertwine (evalPt x ∘ₗ (homSub B).subtype) φ (ptEnd F hF _)
      (fun f => congrArg Additive.ofMul (Category.assoc x (Additive.toMul f.1) F.asHom)) p e
    have h' : (evalPt x ∘ₗ (homSub B).subtype) e = Additive.ofMul x := congrArg Additive.ofMul (Category.comp_id x)
    rw [h'] at h
    exact h
  obtain ⟨P, hP, h0, hβ⟩ := _root_.GlobalTheory.SimAlg.similitude_algebraic (homSub B) (fun f => Q (Additive.toMul f.1)) φ e q l r hl2
    (fun x y => by
      have := Q1 (Additive.toMul x.1) (Additive.toMul y.1)
      rw [sub_eq_add_neg]
      exact this)
    (fun x => Q2 _) (fun x hx => Subtype.ext (Q3 _ x.2 hx)) (fun x => Q4 _ q hq _)
    (fun n => by
      obtain ⟨χ, h1, h2, h3⟩ := hr n
      obtain ⟨g, hg, hg'⟩ := (hD n).2 (Additive.toMul (aeval φ χ e).1) (aeval φ χ e).2 fun x hx =>
        (hev x χ).symm.trans (h3 (Additive.ofMul x) hx)
      exact ⟨χ, ⟨Additive.ofMul g, hg⟩, h1, h2, Subtype.ext hg'⟩)
  refine ⟨P, hP, hβ, fun x => ?_⟩
  have h := (aeval_ptEnd F hF x P).symm.trans (hev x P)
  rw [h0] at h
  exact h.trans (MonObj.comp_one x)

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusPointEqOneOfAxes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem splitTorus_point_eq_one_of_axes (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K))
    (G : Over (Sp K)) [GrpObj G] (h : E.IsGt G) (X : Type) [AddCommGroup X]
    (t : G ⊗ G ⟶ splitTorus (Sp K) X)
    (h₁ : lift (𝟙 G) (1 : G ⟶ G) ≫ t = 1) (h₂ : lift (1 : G ⟶ G) (𝟙 G) ≫ t = 1) : t = 1 := by
  have key : ∀ (a : G ⟶ G ⊗ G), a ≫ t = 1 → ∀ χ : X, a.left.appTop.hom
      (splitTorusPointsEquiv (Sp K) X (G ⊗ G) t (Multiplicative.ofAdd χ)).val = 1 := by
    intro a ha χ
    have := splitTorusPointsEquiv_val (Sp K) X G (a ≫ t) χ
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_one] at this
    rw [splitTorusPointsEquiv_val]
    exact this.symm
  apply (splitTorusPointsEquiv (Sp K) X (G ⊗ G)).injective
  rw [map_one]
  ext χ
  exact unit_eq_one_of_axes_of_isGt K E G h _ (Units.isUnit _) (key _ h₁ χ) (key _ h₂ χ)

theorem isMonHom_of_isGt_of_one :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E E' : SplitExt (Sp K)) (G G' : Over (Sp K)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'], E.IsGt G → E'.IsGt G' → ∀ f : G ⟶ G', η[G] ≫ f = η[G'] → IsMonHom f := by
  intro K _ _ E E' G G' _ _ _ _ h ⟨D⟩ f hf
  have := D.q_hom
  have := D.i_hom
  have hk := D.isKernel
  have hq : IsMonHom (f ≫ D.q) := _root_.GlobalTheory.ExtensionRigidity.isMonHom_of_pointed K E G h E'.B E'.isAbelian (f ≫ D.q) (by
    rw [reassoc_of% hf]; exact IsMonHom.one_hom D.q)
  have hf1 : ∀ {W : Over (Sp K)}, (1 : W ⟶ G) ≫ f = 1 := by
    intro W
    rw [Hom.one_def, Hom.one_def, Category.assoc, hf]
  let d : G ⊗ G ⟶ G' := ((fst G G * snd G G) ≫ f) / ((fst G G ≫ f) * (snd G G ≫ f))
  have hd : d ≫ D.q = 1 := by
    simp only [d]
    rw [GrpObj.div_comp, Category.assoc, MonObj.mul_comp, MonObj.mul_comp, Category.assoc,
      Category.assoc, div_self']
  let t : G ⊗ G ⟶ splitTorus (Sp K) E'.X := hk.lift d (toUnit _) (by rw [hd, Hom.one_def])
  have ht : t ≫ D.i = d := hk.lift_fst _ _ _
  have inj : ∀ a : G ⟶ G ⊗ G, a ≫ d = 1 → a ≫ t = 1 := fun a ha =>
    hk.hom_ext (by rw [Category.assoc, ht, ha, MonObj.one_comp]) (toUnit_unique _ _)
  have t1 : t = 1 := by
    refine splitTorus_point_eq_one_of_axes K E G h E'.X t (inj _ ?_) (inj _ ?_)
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.mul_one, _root_.mul_one, div_self']
    · simp only [d]
      rw [GrpObj.comp_div, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd,
        lift_fst_assoc, lift_snd_assoc, hf1, _root_.one_mul, _root_.one_mul, div_self']
  rw [t1, MonObj.one_comp] at ht
  have hm : (fst G G * snd G G) ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := div_eq_one.mp ht.symm
  refine ⟨hf, ?_⟩
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at hm
  rw [hm]
  congr 1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology

namespace GlobalTheory.MatchTerm

theorem txT_tendsto {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ} (hq : N.Int q) {m : ℕ}
    (hm : Odd m) (p : N.QT (m ^ 2)) (hp : p.1.1 = 1) : Tendsto (N.txT m p) cofinite (𝓝 0) := by
  have h0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.pos.ne'
  refine squeeze_zero_norm (a := fun χ => Real.exp (-q χ)) (fun χ => ?_)
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hq.pos))
  rw [(_root_.GlobalTheory.Ex.norm_QT_s_and_norm_txT C N q hq).2 m hm p χ, hp, toAdd_one, zero_add, ← natCast_zsmul, QuadraticMap.map_smul]
  have : (((m : ℤ) * (m : ℤ)) • q χ) / (m : ℝ) ^ 2 = q χ := by
    rw [zsmul_eq_mul]; push_cast; field_simp
  rw [this]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hq.th _)

theorem exists_txT_ne {C : Type} [NormedField C] [IsAlgClosed C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
    (hq : N.Int q) {n g : ℕ} (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (x : N.X) :
    ∃ p : N.QT ((n ^ 1) ^ 2), p.1.1 = 1 ∧ N.txT (n ^ 1) p x ≠ 0 := by
  obtain ⟨t, ht, hx⟩ := hT.good (N.c x)
  obtain ⟨b, rfl⟩ := hT.div t
  obtain ⟨γ, rfl⟩ := (_root_.GlobalTheory.Ex.QStr.qStructure C N n g hC hT 0).1 b
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ ^ (n ^ 1) ^ 2)).2 (by rw [NumD.Gt.pow_b, pow_one, sq, pow_mul, ht])
  obtain ⟨s, rfl⟩ := exists_char_pow (k := (n ^ 1) ^ 2) (pow_ne_zero _ (pow_ne_zero _ hn.pos.ne')) s
  refine ⟨⟨(1, γ * (N.tor s)⁻¹), ?_⟩, rfl, ?_⟩
  · rw [NumD.mem_QT, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
    exact N.io_zero.symm
  · rw [← norm_ne_zero_iff, (_root_.GlobalTheory.Ex.norm_QT_s_and_norm_txT C N q hq).2 _ hn.pow]
    refine mul_ne_zero (Real.exp_pos _).ne' ?_
    simp [hx]

theorem tx_twist {C : Type} [NormedField C] {N : NumD C} {M m : ℕ} (hM : Odd M) (hm : Odd m)
    (p : N.QT (m ^ 2)) (P : N.QT ((M * m) ^ 2)) (hp : p.1.1 = 1) (hP : P.1.1 = 1) (h : p.1.2 = P.1.2 ^ M)
    (s : Multiplicative N.X →* Cˣ) (hs : s ^ (M * m) ^ 2 = 1) :
    N.tx (M * m) (P * N.qTor s hs) = ∑' β, N.txT m p β * ((s ^ (M * m)) (Multiplicative.ofAdd β) : C) := by
  refine tsum_congr fun β => ?_
  rw [(_root_.GlobalTheory.Ex.txT_shift C N (M * m) (hM.mul hm) P (P * N.qTor s hs) β).2 s (mul_one _) rfl,
    _root_.GlobalTheory.Ex.Nest.txT_nest C N M m hM hm P p (by rw [hP, hp, one_pow]) h, hP, map_one, one_pow, one_mul, toAdd_one, zero_add,
    ofAdd_nsmul, map_pow, mul_comm]
  rfl

section
variable {C : Type} [NormedField C] [IsAlgClosed C] {N N' : NumD C} {n g : ℕ} (μ : Match N N' n)

theorem tx_eq {m : ℕ} (hm : ∃ j, m = n ^ j) {p : N.QT (m ^ 2)} {p' : N'.QT (m ^ 2)} (h : μ.r _ p p') :
    N'.tx m p' = μ.c₀ * N.tx m p := by
  obtain ⟨j, rfl⟩ := hm
  exact μ.tx j p p' h

theorem twisted_eq (hn : Odd n) (hC : (n : C) ≠ 0) (hT : N.Tors n g) (hA : μ.A) (i j : ℕ)
    {p : N.QT ((n ^ j) ^ 2)} {p' : N'.QT ((n ^ j) ^ 2)} (h : μ.r _ p p') (hp : p.1.1 = 1) (hp' : p'.1.1 = 1)
    {t : Multiplicative N.X →* Cˣ} {ht : t ^ n ^ i = 1} {t' : Multiplicative N'.X →* Cˣ} {ht' : t' ^ n ^ i = 1}
    (e : μ.r _ (N.qTor t ht) (N'.qTor t' ht')) :
    ∑' β, N'.txT (n ^ j) p' β * (t' (Multiplicative.ofAdd β) : C) =
      μ.c₀ * ∑' β, N.txT (n ^ j) p β * (t (Multiplicative.ofAdd β) : C) := by
  have h0 : ∀ a, n ^ a ≠ 0 := fun a => pow_ne_zero _ hn.pos.ne'
  have hL0 : n ^ i * n ^ j ≠ 0 := mul_ne_zero (h0 _) (h0 _)
  have hL : ∃ a, (n ^ i * n ^ j) ^ 2 = n ^ a := ⟨(i + j) * 2, by ring⟩
  obtain ⟨γ, hγ⟩ := (_root_.GlobalTheory.Ex.QStr.qStructure C N n g hC hT i).2.1 p.1.2
  have hp1 : p.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N.mem_QT.1 p.2, hp]; exact N.io_zero
  have hp1' : p'.1.2 ^ (n ^ j) ^ 2 = 1 := by rw [N'.mem_QT.1 p'.2, hp']; exact N'.io_zero
  let P : N.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, γ), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = n ^ i * ((n ^ j) ^ 2 * n ^ i) by ring, pow_mul, hγ, pow_mul, hp1, one_pow]
    exact N.io_zero.symm⟩
  obtain ⟨P', hPP, hP'⟩ := tot_G μ hA hL P rfl
  let Q' : N'.QT ((n ^ i * n ^ j) ^ 2) := ⟨(1, p'.1.2), by
    rw [NumD.mem_QT, show (n ^ i * n ^ j) ^ 2 = (n ^ j) ^ 2 * (n ^ i) ^ 2 by ring, pow_mul, hp1', one_pow]
    exact N'.io_zero.symm⟩
  have h1 : μ.r _ (P ^ n ^ i) Q' :=
    (r_incl μ (p := p) (p' := p') (q := P ^ n ^ i) (q' := Q') ((n ^ i) ^ 2) (by ring) (pow_ne_zero _ (h0 i)) (by rw [hp, one_pow]; exact one_pow _) hγ
      (by rw [hp', one_pow]) rfl).1 h
  have h2 : Q' = P' ^ n ^ i := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h1 (r_pow μ hL hPP _))
    (by change 1 = P'.1.1 ^ n ^ i; rw [hP', one_pow])
  have h3 : p'.1.2 = P'.1.2 ^ n ^ i := congrArg (fun q : N'.QT _ => q.1.2) h2
  obtain ⟨s, rfl⟩ := exists_char_pow hL0 t
  have hs : s ^ (n ^ i * n ^ j) ^ 2 = 1 := by rw [sq, pow_mul, pow_mul _ (n ^ i), ht, one_pow]
  obtain ⟨s', hs', hss⟩ := thetaMatching_exists_right_torus_torsion μ hA hL s hs
  have ht'' : t' ^ (n ^ i * n ^ j) ^ 2 = 1 := by
    rw [show (n ^ i * n ^ j) ^ 2 = n ^ i * (n ^ i * (n ^ j) ^ 2) by ring, pow_mul, ht', one_pow]
  have h4 : μ.r _ (N.qTor s hs ^ (n ^ i * n ^ j)) (N'.qTor t' ht'') :=
    (r_incl μ (p := N.qTor _ ht) (p' := N'.qTor t' ht') (q := N.qTor s hs ^ (n ^ i * n ^ j))
      (q' := N'.qTor t' ht'') (n ^ i * (n ^ j) ^ 2) (by ring) (mul_ne_zero (h0 i) (pow_ne_zero _ (h0 j)))
      ((one_pow _).trans (one_pow _).symm) (N.tor_pow _ _).symm (one_pow _).symm rfl).1 e
  have h5 := eq_of_qeq (pow_ne_zero _ hL0) (qeq_right μ h4 (r_pow μ hL hss _)) (one_pow _).symm
  have h6 : t' = s' ^ (n ^ i * n ^ j) :=
    N'.tor_injective ((congrArg (fun q : N'.QT _ => q.1.2) h5).trans (N'.tor_pow _ _).symm)
  rw [h6, ← tx_twist hn.pow hn.pow p P hp rfl hγ.symm s hs, ← tx_twist hn.pow hn.pow p' P' hp' hP' h3 s' hs']
  exact tx_eq μ ⟨i + j, (pow_add _ _ _).symm⟩ (μ.mul _ _ _ _ _ hPP hss)
end

theorem main : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  intro C _ _ _ _ N N' q q' n g g' hpr hn hn1 hq hq' hT hT' μ hA
  have hC : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  have hn0 := hpr.ne_zero
  have key : ∀ i j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)), μ.r _ p p' → p.1.1 = 1 → p'.1.1 = 1 →
      ∀ α α', Cl μ i α α' →
      ∑' z, N'.txT (n ^ j) p' (α' + n ^ i • z) = μ.c₀ * ∑' z, N.txT (n ^ j) p (α + n ^ i • z) := by
    intro i j p p' h hp hp' α α' hα
    obtain ⟨E, hE, hr⟩ := exists_torus_bij μ hn0 hA ⟨i, rfl⟩
    exact class_sum_eq (by rw [Nat.cast_pow, norm_pow, hn1, one_pow]) _ _ (txT_tendsto hq hn.pow p hp)
      (txT_tendsto hq' hn.pow p' hp') _ α α' E hE (fun t => hα.tor μ (hr t))
      fun t => twisted_eq μ hn hC hT hA i j h hp hp' (hr t)
  have tot : ∀ j x, ∃ x', Cl μ j x x' := fun j x => by
    obtain ⟨p, hp⟩ := (_root_.GlobalTheory.Ex.QStr.qStructure C N n g hC hT j).2.2.1 x
    obtain ⟨p', h⟩ := μ.tot j p
    exact ⟨_, p, p', h, hp, rfl⟩
  have cotot : ∀ j x', ∃ x, Cl μ j x x' := fun j x' => by
    obtain ⟨p', hp⟩ := (_root_.GlobalTheory.Ex.QStr.qStructure C N' n g' hC hT' j).2.2.1 x'
    obtain ⟨p, h⟩ := μ.cotot j p'
    exact ⟨_, p, p', h, rfl, hp⟩
  have hL : ∃ a, (n ^ 1) ^ 2 = n ^ a := ⟨2, by ring⟩
  have hf : ∀ x, ∃ x', ∀ j, Cl μ j x x' := fun x => by
    choose α hα using fun j => tot j x
    obtain ⟨p, hp, hx⟩ := exists_txT_ne hq hn hC hT x
    obtain ⟨p', h, hp'⟩ := tot_G μ hA hL p hp
    obtain ⟨x', hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
      μ.c₀ x α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).1 ⟨0, by simp⟩)
      fun i => key i 1 p p' h hp hp' _ _ (hα i)).2 (mul_ne_zero μ.c₀_ne hx)
    refine ⟨x', fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ 0 z
  have hg : ∀ x', ∃ x, ∀ j, Cl μ j x x' := fun x' => by
    choose α hα using fun j => cotot j x'
    obtain ⟨p', hp', hx⟩ := exists_txT_ne hq' hn hC hT' x'
    obtain ⟨p, h, hp⟩ := cotot_G μ hA hL p' hp'
    obtain ⟨x, hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq' hn.pow p' hp') (txT_tendsto hq hn.pow p hp)
      μ.c₀⁻¹ x' α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).2 ⟨0, by simp⟩)
      fun i => by rw [key i 1 p p' h hp hp' _ _ (hα i), inv_mul_cancel_left₀ μ.c₀_ne]).2
      (mul_ne_zero (inv_ne_zero μ.c₀_ne) hx)
    refine ⟨x, fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ z 0
  obtain ⟨e, he, -⟩ := existsUnique_addEquiv_of_compatible_congr N.X N'.X n hpr.two_le (Cl μ) tot cotot
    (fun _ _ _ _ _ h h' => h.add μ h') (fun _ _ _ _ _ h h' => h.cong μ hA h') (fun _ _ _ _ _ h => h.shift μ _ _) hf hg
  refine ⟨e, fun j p p' h => ((he j _).cong μ hA ⟨p, p', h, rfl, rfl⟩).1 ⟨0, by simp⟩, fun j p p' h hp hp' χ => ?_⟩
  exact (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
    μ.c₀ χ (fun _ => e χ) (fun j => ⟨0, by simp⟩) fun i => key i j p p' h hp hp' _ _ (he i χ)).1 _
    fun j => ⟨0, by simp⟩

end GlobalTheory.MatchTerm
end

