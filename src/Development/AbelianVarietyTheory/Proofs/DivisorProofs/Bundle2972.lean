module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitUniq

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {w : W} (hw : Irreducible w) {a b : ℕ}
    (h : Associated (w ^ a) (w ^ b)) : a = b := by
  have key : ∀ {a b : ℕ}, Associated (w ^ a) (w ^ b) → a ≤ b → a = b := by
    intro a b h hab
    by_contra hne
    have hlt : 0 < b - a := by omega
    have h1 : Associated (w ^ a * 1) (w ^ a * w ^ (b - a)) := by
      rw [mul_one, ← pow_add, Nat.add_sub_cancel' hab]; exact h
    have h2 : Associated 1 (w ^ (b - a)) :=
      Associated.of_mul_left h1 (Associated.refl _) (pow_ne_zero _ hw.ne_zero)
    have h3 : IsUnit (w ^ (b - a)) := associated_one_iff_isUnit.1 h2.symm
    exact hw.not_isUnit ((isUnit_pow_iff hlt.ne').1 h3)
  rcases le_total a b with hab | hab
  · exact key h hab
  · exact (key h.symm hab).symm

theorem sq_associated {V W : Type} [CommRing V] [CommRing W] [IsDomain W] (f : V →+* W) (ϖ : V) (w : W) (m n : ℕ)
    (hm : Associated (f ϖ) (w ^ m)) (v : Wˣ) (u : Vˣ) :
    Associated ((v * f (u * ϖ ^ n)) ^ 2) (w ^ (2 * (m * n))) := by
  have hu : IsUnit (f (u : V)) := (Units.isUnit u).map f
  have e : (v * f (u * ϖ ^ n)) ^ 2 = (((v : W) * f u) ^ 2) * (f ϖ ^ n) ^ 2 := by
    rw [map_mul, map_pow]; ring
  rw [e]
  refine (associated_unit_mul_left _ _ ((v.isUnit.mul hu).pow 2)).trans ?_
  have eq : w ^ (2 * (m * n)) = ((w ^ m) ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
  rw [eq]
  exact (hm.pow_pow (n := n)).pow_pow (n := 2)

end GlobalTheory.UPoinc.TraitUniq


open GlobalTheory.UPoinc.TraitUniq in
theorem GlobalTheory.UPoinc.uTraitUniqSt_holds : UTraitUniqSt := by
  intro E _ _ _ H Dw l Xo c T T' W _ _ _ f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy w m m' hw hm hm'
  obtain ⟨tW, ⟨φ⟩, ⟨φ'⟩⟩ := _root_.GlobalTheory.UPoinc.TraitUniq.exists_common_pull E H Dw l Xo c T T' W f f' fK fK' hB hW hf hf' hfl hfl' hK hK' hy
  obtain ⟨PW, e1, he1⟩ := _root_.GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T.V T.cdvr T.t T.P W hB hW f hf hfl tW ⟨φ⟩
  obtain ⟨PW', e1', he1'⟩ := _root_.GlobalTheory.UnifDvrBaseChange.exists_pelUnif E H T'.V T'.cdvr T'.t T'.P W hB hW f' hf' hfl' tW ⟨φ'⟩
  obtain ⟨e2, he2⟩ := _root_.GlobalTheory.PelUnifUniqCoord.main E H W hB tW PW PW'
  let e : T.P.D.toPre.X ≃ₗ[𝓞 E] T'.P.D.toPre.X := e1.symm.trans (e2.trans e1')

  have diag : ∀ y, (m : ℤ) * T.be y y = m' * T'.be (e y) (e y) := by
    intro y
    obtain ⟨u, n, hn, hc⟩ := T.mono y
    obtain ⟨u', n', hn', hc'⟩ := T'.mono (e y)
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one] at hn hc hn' hc'
    have hc1 : PsiCoord T.P.D.toPre (e1 (e1.symm y)) (u * T.ϖ ^ n 0) := by
      rw [LinearEquiv.apply_symm_apply]; exact hc
    obtain ⟨v, hv⟩ := he1 _ _ hc1
    obtain ⟨v', hv'⟩ := he1' (e2 (e1.symm y)) _ hc'
    have ha := he2 _ _ _ hv hv'
    have h1 := sq_associated f T.ϖ w m (n 0) hm v u
    have h2 := sq_associated f' T'.ϖ w m' (n' 0) hm' v' u'
    have := pow_eq_of_associated hw (h1.symm.trans (ha.trans h2))
    rw [hn 0, hn' 0]
    have : ((2 * (m * n 0) : ℕ) : ℤ) = ((2 * (m' * n' 0) : ℕ) : ℤ) := by rw [this]
    push_cast at this
    linarith
  have hs : ∀ a b, T.be a b = T.be b a := fun a b => (mem_levelForms.1 T.lev).1 a b
  have hs' : ∀ a b, T'.be a b = T'.be b a := fun a b => (mem_levelForms.1 T'.lev).1 a b
  refine ⟨e, fun a b => ?_⟩
  have h := diag (a + b)
  simp only [map_add (f := _), LinearMap.add_apply] at h
  have ha := diag a
  have hb := diag b
  rw [hs b a, hs' (e b) (e a)] at h
  linarith
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPullbackIdentificationDerivationCommutesTrans
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section

open GlobalTheory.KS.DlogPol (gs_pbT gs_sub)

namespace GlobalTheory.HeatConn.Comm

theorem gs_stalkMap' {X X' Z : Scheme.{0}} (r : Z ⟶ X') (β : X' ⟶ X) (z : Z) (U : X.Opens) (h : β (r z) ∈ U)
    (a : Γ(X, U)) : (r.stalkMap z).hom (gs β (r z) U a) = gs (r ≫ β) z U a := by
  rw [← gs_pull r β z U h, gs_eq β _ U h, gs_eq r z _ h]
  exact Scheme.Hom.germ_stalkMap_apply r (β ⁻¹ᵁ U) z h _

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem cst_spMap {V V' : Type} [CommRing V] [CommRing V'] {Z : Scheme.{0}} (q : Z ⟶ Sp V) (ψ : V' →+* V) (z : Z)
    (a : V') : cst (q ≫ spMap ψ) z a = cst q z (ψ a) := by
  rw [cst, cst, ← gs_pull _ (spMap ψ) z ⊤ trivial]
  exact congrArg (gs q z ⊤) (congrArg (fun ψ' => ψ'.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm

theorem stalkMap_eq_zero {k : Type} [Field k] {A₀ B' : Scheme.{0}} (q : B' ⟶ Sp (DualNumber k)) [Flat q]
    (sc : A₀ ⟶ B') (q₀ : A₀ ⟶ Sp k) (hsc : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (y : A₀)
    {t : B'.presheaf.stalk (sc y)} (ht : cst q (sc y) DualNumber.eps * t = 0) : (sc.stalkMap y).hom t = 0 := by
  obtain ⟨u, rfl⟩ := GlobalTheory.cst_dvd_of_cst_mul_eq_zero q (sc y) (a := DualNumber.eps) (b := DualNumber.eps)
    (fun c hc => by
      have h1 : c.fst = 0 := by simpa using congrArg TrivSqZeroExt.snd hc
      exact ⟨TrivSqZeroExt.inl c.snd, by ext <;> simp [h1]⟩) ht
  rw [map_mul, cst, gs_stalkMap' sc q y ⊤ trivial, ← cst, hsc, cst_spMap]
  have e0 : (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 := by simp
  rw [e0, cst, map_zero, gs_eq _ y ⊤ trivial, map_zero, map_zero, zero_mul]

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem spMap_fst_alg (k : Type) [Field k] :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
    ext; simp
  rw [this, spMap]
  exact Spec.map_id _

theorem exists_sec {k : Type} [Field k] {S A A₀ B' : Scheme.{0}} (p : A ⟶ S) (s : Sp k ⟶ S) (q₀ : A₀ ⟶ Sp k)
    (q : B' ⟶ Sp (DualNumber k)) (m₀ : A₀ ⟶ A) (π₁ π₂ : B' ⟶ A) (pr : B' ⟶ A₀)
    (h₀ : IsPullback m₀ q₀ p s) (h₂ : IsPullback π₂ q p (spMap (algebraMap k (DualNumber k)) ≫ s))
    (h₃ : ∀ (Z : Scheme.{0}) (x : Z ⟶ B') (y : Z ⟶ Sp k),
      x ≫ q = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂)
    (hpr₁ : pr ≫ m₀ = π₂) (hpr₂ : pr ≫ q₀ = q ≫ spMap (algebraMap k (DualNumber k))) :
    ∃ sc : A₀ ⟶ B', sc ≫ pr = 𝟙 _ ∧ sc ≫ π₂ = m₀ ∧
      sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ∧ ∀ x : B', π₁ x = π₂ x := by
  have e1 := spMap_fst_alg k
  have w : m₀ ≫ p = (q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap (algebraMap k (DualNumber k)) ≫ s := by
    rw [Category.assoc, reassoc_of% e1, h₀.w]
  let sc := h₂.lift m₀ _ w
  have hs₂ : sc ≫ π₂ = m₀ := h₂.lift_fst _ _ _
  have hsq : sc ≫ q = q₀ ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := h₂.lift_snd _ _ _
  have hspr : sc ≫ pr = 𝟙 _ := h₀.hom_ext (by rw [Category.assoc, hpr₁, hs₂, Category.id_comp])
    (by rw [Category.assoc, hpr₂, reassoc_of% hsq, e1, Category.comp_id, Category.id_comp])
  have hR : IsPullback pr q q₀ (spMap (algebraMap k (DualNumber k))) :=
    IsPullback.of_right (h₁₂ := m₀) (v₁₃ := p) (h₂₂ := s) (by rw [hpr₁]; exact h₂) hpr₂ h₀
  have hL : IsPullback sc q₀ q (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) :=
    IsPullback.of_right (h₁₂ := pr) (v₁₃ := q₀) (h₂₂ := spMap (algebraMap k (DualNumber k)))
      (by rw [hspr, e1]; exact IsPullback.id_horiz q₀) hsq hR
  have surj := (GlobalTheory.EpsIso.isHomeomorph_of_isPullback hL).2.surjective
  refine ⟨sc, hspr, hs₂, hsq, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := surj x
  have := congrArg (fun g : A₀ ⟶ A => g y) (h₃ _ sc q₀ hsq)
  simpa using this

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

open ReciprocityTheory.ChartRestriction.G.Out.PullGtPf in
theorem const_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) : (toUnit B ≫ c').left ≫ π = π ≫ (toUnit A ≫ c).left := by
  rw [Over.comp_left, Over.comp_left, toUnit_left', toUnit_left', Category.assoc, hc, ← Category.assoc,
    ← h.1.w, Category.assoc]

theorem trans_comm {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B]
    {π : B.left ⟶ A.left} (h : IsGrpPullback B A f π) (c : 𝟙_ (Over S) ⟶ A) (c' : 𝟙_ (Over S') ⟶ B)
    (hc : c'.left ≫ π = f ≫ c.left) :
    (padd B (𝟙 B) (toUnit B ≫ c')).left ≫ π = π ≫ (padd A (𝟙 A) (toUnit A ≫ c)).left := by
  let x₀ : Over.mk (B.hom ≫ f) ⟶ A := Over.homMk π h.1.w
  have e := h.2 B (𝟙 B) (toUnit B ≫ c') x₀ (toUnit _ ≫ c) (by simp [x₀]) (by
    rw [Over.comp_left, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left',
      ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left', Category.assoc, hc]
    rfl)
  have e2 : x₀ * (toUnit _ ≫ c) = x₀ ≫ (𝟙 A * (toUnit A ≫ c)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  change (𝟙 B * (toUnit B ≫ c')).left ≫ π = π ≫ (𝟙 A * (toUnit A ≫ c)).left
  rw [← e, e2]
  rfl

theorem exists_lift {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k]
    (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left)
    (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)) (h₁ : IsGrpPullback B' Q.P.A (spMap ρ) π₁)
    (h₂ : IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂)
    (hc : ∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧
      c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) (α : Q.X) (j : Fin 4) :
    ∃ φ' : B'.left ⟶ B'.left, φ' ≫ B'.hom = B'.hom ∧ φ' ≫ π₁ = π₁ ≫ Q.famφB α j ∧ φ' ≫ π₂ = π₂ ≫ Q.famφB α j := by
  have hcB : ∀ y, c' y ≫ B'.hom = (𝟙_ (Over (Sp (DualNumber k)))).hom := fun y => (hc y).1
  let cB : Q.X → (𝟙_ (Over (Sp (DualNumber k))) ⟶ B') := fun y => Over.homMk (c' y) (hcB y)
  have h1 : ∀ y, (cB y).left ≫ π₁ = spMap ρ ≫ (Q.c y).left := fun y => (hc y).2.1
  have h2 : ∀ y, (cB y).left ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left := fun y => (hc y).2.2
  fin_cases j
  · exact ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans (Category.comp_id _).symm,
      (Category.id_comp _).trans (Category.comp_id _).symm⟩
  · exact ⟨(padd B' (𝟙 B') (toUnit B' ≫ cB α)).left, Over.w _, trans_comm h₁ _ _ (h1 α),
      trans_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ cB α).left, Over.w _, const_comm h₁ _ _ (h1 α), const_comm h₂ _ _ (h2 α)⟩
  · exact ⟨(toUnit B' ≫ η[B']).left, Over.w _,
      const_comm h₁ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₁),
      const_comm h₂ _ _ (ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h₂)⟩

end GlobalTheory.HeatConn.Comm

namespace GlobalTheory.HeatConn.Comm

theorem commutes : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {k : Type} [Field k] (ρ : R →+* DualNumber k) (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsGrpPullback A₀ Q.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left) (c' : Q.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (Q.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (Q.c y).left) → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → (∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → Commutes Q m₀ ed := by
  intro R _ _ Q k _ ρ A₀ _ m₀ hA₀ ed B' _ π₁ π₂ c' h₁ h₂ h₃ hc pr hpr₁ hpr₂ hD α j T hT₁ hT₂ W f Z b z hz
  have hfA : Flat Q.P.A.hom := by
    have := Q.P.smoothDim
    have : Smooth Q.P.A.hom := SmoothOfRelativeDimension.smooth Q.P.g _
    infer_instance
  have hfB : Flat B'.hom := MorphismProperty.of_isPullback h₁.1 hfA
  obtain ⟨φ', hφ'0, hφ'1, hφ'2⟩ := exists_lift Q ρ B' π₁ π₂ c' h₁ h₂ hc α j
  have e2 : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := spMap_comp _ _
  obtain ⟨sc, hspr, hs₂, hsq, hpts⟩ := exists_sec Q.P.A.hom _ A₀.hom B'.hom m₀ π₁ π₂ pr hA₀.1
    (e2 ▸ h₂.1) h₃ hpr₁ hpr₂
  have hpre : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ π₁ ⁻¹ᵁ U := fun U x hx => by
    change π₁ x ∈ U
    rw [hpts x]
    exact hx
  have hprle : ∀ U : Q.P.A.left.Opens, π₂ ⁻¹ᵁ U ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U x hx => by
    change m₀ (pr x) ∈ U
    have : (pr ≫ m₀) x ∈ U := by rw [hpr₁]; exact hx
    simpa using this
  have hφpr : φ' ≫ pr = pr ≫ T := hA₀.1.hom_ext
    (by rw [Category.assoc, Category.assoc, hpr₁, hφ'2, hT₁, ← Category.assoc, hpr₁])
    (by rw [Category.assoc, Category.assoc, hpr₂, ← Category.assoc, hφ'0, hT₂, hpr₂])
  set φ := Q.famφB α j with hφdef
  have key : ∀ y : A₀.left, (T ≫ m₀) y ∈ W →
      gs (𝟙 _) y (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) = gs T y (m₀ ⁻¹ᵁ W) (ed W f) := by
    intro y hy
    have hy' : φ (m₀ y) ∈ W := by
      have h := hy
      rw [hT₁] at h
      all_goals simpa using h
    have m₂ : sc y ∈ π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (π₂ (sc y)) ∈ W
      have : (sc ≫ π₂) y = m₀ y := by rw [hs₂]
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact hy'
    have m₃ : φ' (sc y) ∈ π₂ ⁻¹ᵁ W := by
      change π₂ (φ' (sc y)) ∈ W
      have : (φ' ≫ π₂) (sc y) = φ (π₂ (sc y)) := by rw [hφ'2]; simp
      simp only [Scheme.Hom.comp_apply] at this
      rw [this]; exact m₂
    have eA := congrArg (gs (𝟙 B'.left) (sc y) (π₂ ⁻¹ᵁ (φ ⁻¹ᵁ W))) (hD (φ ⁻¹ᵁ W) ((φ.app W).hom f))
    rw [gs_add (𝟙 _) (sc y) _ m₂, gs_mul (𝟙 _) (sc y) _ m₂, gs_pbT (𝟙 _) π₁ (sc y) (hpre _) m₂,
      gs_pbT (𝟙 _) π₂ (sc y) le_rfl m₂, gs_pbT (𝟙 _) pr (sc y) (hprle _) m₂, gs_constFn B'.hom _ (𝟙 _) (sc y) m₂] at eA
    have eB := congrArg (gs φ' (sc y) (π₂ ⁻¹ᵁ W)) (hD W f)
    rw [gs_add φ' (sc y) _ m₃, gs_mul φ' (sc y) _ m₃, gs_pbT φ' π₁ (sc y) (hpre _) m₃,
      gs_pbT φ' π₂ (sc y) le_rfl m₃, gs_pbT φ' pr (sc y) (hprle _) m₃, gs_constFn B'.hom _ φ' (sc y) m₃, hφ'1, hφ'2, hφ'0, hφpr] at eB
    simp only [Category.id_comp] at eA
    have m₁' : φ (π₁ (sc y)) ∈ W := by rw [hpts]; exact m₂
    rw [← gs_pull π₁ φ (sc y) W m₁', ← gs_pull π₂ φ (sc y) W m₂] at eB
    have hk : cst B'.hom (sc y) DualNumber.eps * (gs pr (sc y) (m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W)) (ed _ ((φ.app W).hom f)) -
        gs (pr ≫ T) (sc y) (m₀ ⁻¹ᵁ W) (ed W f)) = 0 := by
      linear_combination eB - eA
    have h0 := stalkMap_eq_zero B'.hom sc A₀.hom hsq y hk
    have hy0 : pr (sc y) = y := by
      have := congrArg (fun g : A₀.left ⟶ A₀.left => g y) hspr
      simpa using this
    have ma : pr (sc y) ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
      change φ (m₀ (pr (sc y))) ∈ W
      rw [hy0]; exact hy'
    have mb : (pr ≫ T) (sc y) ∈ m₀ ⁻¹ᵁ W := by
      change m₀ ((pr ≫ T) (sc y)) ∈ W
      simp only [Scheme.Hom.comp_apply]
      rw [hy0]; simpa using hy
    rw [map_sub, gs_stalkMap' sc pr y _ ma, gs_stalkMap' sc (pr ≫ T) y _ mb, hspr, reassoc_of% hspr] at h0
    exact sub_eq_zero.1 h0
  have hyz : (T ≫ m₀) (b z) ∈ W := by simpa using hz
  have mz1 : b z ∈ m₀ ⁻¹ᵁ (φ ⁻¹ᵁ W) := by
    change φ (m₀ (b z)) ∈ W
    have h := hyz
    rw [hT₁] at h
    all_goals simpa using h
  have mz2 : T (b z) ∈ m₀ ⁻¹ᵁ W := by
    change m₀ (T (b z)) ∈ W
    simpa using hyz
  rw [gs_stalkMap b z _ mz1, key (b z) hyz, gs_stalkMap' b T z _ mz2]

end GlobalTheory.HeatConn.Comm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupsAdjointHomPairClosedForm
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

namespace GlobalTheory.MumAdj

section

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D₁ D₂ : DegData R (maximalIdeal R)}
  {A A₁ A₂ : PolAV (Sp (FractionRing R))} {G G₁ G₂ : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G₁] [IsCommMonObj G₁]
  [GrpObj G₂] [IsCommMonObj G₂]

theorem exists_linHom_end (hR : Base R) (hG : IsSemiAbelian G) (U : Unif (maximalIdeal R) D A G) {a a' h h'}
    (H : Adj (pol D) (pol D) a a' h h') : ∃ g, LinHom U.toUnifPre U.toUnifPre a h' g := by
  have hE := GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D a a' h h' H
  obtain ⟨b, hb⟩ := GlobalTheory.Mum.EndThick.formalEnd_exists R hR.1 D A G hG U a a' h h' hE
  obtain ⟨g, hg, e⟩ := _root_.GlobalTheory.Mum.formalEnd_algebraic R hR D A G hG U a a' h h' hE b hb
  exact ⟨g, linHom_iff_linEnd.2 ⟨hg, (funext e : _ = b).symm ▸ hb⟩⟩

theorem exists_linHom (hR : Base R) (hG₁ : IsSemiAbelian G₁) (hG₂ : IsSemiAbelian G₂) (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁)
    (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) {a : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A}
    {h : D₁.toPre.X →+ D₂.toPre.X} {h' : D₂.toPre.X →+ D₁.toPre.X} (H : Adj (pol D₁) (pol D₂) a a' h h') :
    ∃ u u', LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧
      GAdj U₁.LG.L U₂.LG.L u u' := by
  obtain ⟨D, A, U, i₁, p₁, i₂, p₂, j₁, q₁, j₂, q₂, hG, ip₁, ip₂, jq₁, jq₂, ad₁, ad₂, l₁, r₁, l₂, r₂, g₁, g₂⟩ :=
    _root_.GlobalTheory.MumProd.prod_main R hR D₁ A₁ G₁ hG₁ U₁ D₂ A₂ G₂ hG₂ U₂
  have H' := GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.Adj.comp R _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ ad₁) H) ad₂
  obtain ⟨g, hg⟩ := exists_linHom_end hR hG U H'
  obtain ⟨g', hg'⟩ := exists_linHom_end hR hG U (GlobalTheory.MumFam.adj_symm R _ _ _ _ _ _ H')
  have ros : GAdj U.LG.L U.LG.L g g' := GlobalTheory.Mum.linEnd_adjoint_lbIso R hR D A _ hG U _ _ _ _ (GlobalTheory.MumFam.AdjEnd.endData_of_adj R hR D _ _ _ _ H') g g'
    (linHom_iff_linEnd.1 hg) (linHom_iff_linEnd.1 hg')
  refine ⟨_, _, ?_, ?_, GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U₂.LG.isLB _ _ _ _
    (GlobalTheory.MumFam.gAdj_swap_comp.2 _ _ _ _ _ _ _ U₁.LG.isLB U.LG.isLB U.LG.isLB _ _ _ _ g₁ ros)
    (GlobalTheory.MumFam.gAdj_swap_comp.1 _ _ _ _ _ U₂.LG.isLB U.LG.isLB _ _ g₂)⟩
  · have := (l₁.comp hg).comp r₂
    convert this using 1
    · change a = (i₁ ≫ (p₁ ≫ a) ≫ i₂) ≫ p₂
      simp only [Category.assoc, ip₂, Category.comp_id, reassoc_of% ip₁]
    · ext y
      change h' y = q₁ (j₁ (h' (q₂ (j₂ y))))
      rw [jq₁, jq₂]
  · have := l₂.comp (hg'.comp r₁)
    convert this using 1
    · change a' = i₂ ≫ (p₂ ≫ a' ≫ i₁) ≫ p₁
      simp only [Category.assoc, ip₁, Category.comp_id, reassoc_of% ip₂]
    · ext y
      change h y = q₂ (j₂ (h (q₁ (j₁ y))))
      rw [jq₁, jq₂]

end

theorem adj_groups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (a : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (a' : D₂.toPre.P.A ⟶ D₁.toPre.P.A) (h : D₁.toPre.X →+ D₂.toPre.X) (h' : D₂.toPre.X →+ D₁.toPre.X), Adj (pol D₁) (pol D₂) a a' h h' → ∃ (u : G₁ ⟶ G₂) (u' : G₂ ⟶ G₁), LinHom U₁.toUnifPre U₂.toUnifPre a h' u ∧ LinHom U₂.toUnifPre U₁.toUnifPre a' h u' ∧ GAdj U₁.LG.L U₂.LG.L u u' := fun R _ _ _ hR D₁ A₁ G₁ _ _ hG₁ U₁ D₂ A₂ G₂ _ _ hG₂ U₂ _ _ _ _ H =>
  exists_linHom hR hG₁ hG₂ U₁ U₂ H

end GlobalTheory.MumAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryApproxPoincareSeriesAtMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem uApproxAt_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (φ : InvFun (𝓞 E)) (d m : ℕ), 1 ≤ m → UApproxAt X₁ φ d → UApproxAt X₁ φ (d * m) := by
  intro E _ _ _ H Dw l Xo c C X₁ φ d m hm hd p _ z₁ t₀ e
  obtain ⟨f, hf0, hf⟩ := hd p z₁ t₀ e
  have hpow : ∀ t : UCTrait X₁ p z₁, ‖t.val (f ^ m)‖ = ‖t.val f‖ ^ m := fun t => by
    rw [UModel.val_eq_valInt, UModel.val_eq_valInt, map_pow]
    push_cast
    exact norm_pow _ _
  have hexp : ∀ t : UCTrait X₁ p z₁, Real.exp (-(t.sc * (((d * m : ℕ) : ℝ) * φ.evalZ t.T.be))) =
      Real.exp (-(t.sc * (d * φ.evalZ t.T.be))) ^ m := fun t => by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  refine ⟨f ^ m, ?_, fun t => ?_⟩
  · rw [hpow, hf0, hexp]
  · rcases hf t with h1 | ⟨h, hh, h2⟩
    · left
      rw [hpow, hexp]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 m
    · right
      refine ⟨h, hh, ?_⟩
      rw [hpow]
      exact (pow_le_of_le_one (norm_nonneg _) (UModel.norm_val_le t f) (by omega)).trans h2

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinFamilyInclusionPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

open GlobalTheory.CechPic GlobalTheory.AbDual

noncomputable section

namespace GlobalTheory.ZarhinFam

section
variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem incZ_pa (i : Fin 4) : incZ A B ≫ pa A B i = if i = 0 then 𝟙 A else 1 := by
  unfold incZ pa mkZ
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk A _) ⟨i⟩

theorem incZ_pb (j : Fin 4) : incZ A B ≫ pb A B j = 1 := by
  unfold incZ pb mkZ
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk A _) ⟨j⟩
end

theorem zarhinBundle_pullback_inclusion : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → LBIso c.P ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (GlobalTheory.ZarhinFam.incZ c.A B ⊗ₘ GlobalTheory.ZarhinFam.incZ c.A B).left) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ _ _ _ _
  have hQ : Q.IsLB := hZ.2.1.isLB
  have hq0 : ∀ {Y : Over S} (a : Y ⟶ c.A), CechPic.pull (lift a (1 : Y ⟶ B)).left (cls Q hZ.2.1.isLB) = 0 :=
    fun a => evc_one_right hZ.2.1.isLB hZ.2.1.zero a
  have hp0 : ∀ {Y : Over S}, CechPic.pull (lift (1 : Y ⟶ c.A) (1 : Y ⟶ c.A)).left (cls c.P c.isLB) = 0 :=
    evc_one_left c.isLB c.rig₁ 1
  have hp1 : CechPic.pull (lift (fst c.A c.A) (snd c.A c.A)).left (cls c.P c.isLB) = cls c.P c.isLB := by
    rw [lift_fst_snd, Over.id_left, pull_id]
  refine (cls_eq_iff c.isLB (pull_isLB (zarhinBundle_isLineBundle _ _ _ _ _ _) _)).1 ?_
  rw [cls_pull (zarhinBundle_isLineBundle _ _ _ _ _ _), cls_zP]
  unfold zCls
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, tensorHom_fst_assoc,
    tensorHom_snd_assoc, incZ_pa, incZ_pb, Fin.sum_univ_four]
  simp only [MonObj.comp_one, Category.comp_id, ↓reduceIte, Fin.isValue, Fin.reduceEq, one_ne_zero, hq0, hp0, hp1, smul_zero, add_zero, zero_add, Finset.sum_const_zero]

end GlobalTheory.ZarhinFam
end
end

