module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppLESpMapJetPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnValJetGlob


set_option backward.isDefEq.respectTransparency false in
theorem appLE_spMap_jetPt {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by
  have hU : q 0 cpt ∈ U := by
    have : (spMap χ ≫ jetPt q hq m) (IsLocalRing.closedPoint _) ∈ U :=
      h (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [Scheme.Hom.comp_apply, spMap, Spec_closedPoint, jetPt_closedPoint] at this
  refine ⟨hU, fun f => ?_⟩
  have hp : ⊤ ≤ jetPt q hq m ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (jetPt q hq m) (by rw [jetPt_closedPoint]; exact hU)).ge
  have k := specMap_comp_appLE (CommRingCat.ofHom χ) (jetPt q hq m) U h hp
  rw [jetPt_appLE q hq m U hU hp, Category.assoc, Iso.inv_hom_id_assoc, ← Iso.eq_comp_inv] at k
  have k' := ConcreteCategory.congr_hom k f
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, jetψ_apply] at k'
  exact k'


set_option backward.isDefEq.respectTransparency false in
theorem jetRd_pullGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (Z : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (q : (Fin (n * g) → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q), (∀ v, Φ.GenRd φ ε t (q v) (fun k => Λ k (colsOf n g v)) 1) → Φ.JetRd m (fun k => (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m) ≫ φ k) ε (LB.pullGen L.L φ ε t (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt q hq m)) Λ := by
  intro S A _ _ L x0 g Φ n m Z K _ φ ε t Λ q hq H
  refine ⟨fun k => ?_, fun j h => ?_⟩
  · have he : ∀ v, q v ≫ φ k = (Φ.e (Λ k (colsOf n g v))).left := fun v => (H v).1 k
    have hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ k (colsOf n g v))).left) := by
      have h := isHolFam_comp q hq (φ k)
      rwa [show (fun v => q v ≫ φ k) = fun v => (Φ.e (Λ k (colsOf n g v))).left from funext he] at h
    refine ⟨hol, ?_⟩
    beta_reduce
    rw [Category.assoc, jetPt_comp q hq (φ k) _ hol he]
  · have : IsLocalHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) :=
      isLocalHom_jetMap (K := ℂ) (m := m) _ _
    have h' : ⊤ ≤ (spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt q hq m) ⁻¹ᵁ LB.wchart L.L φ j := by
      intro x hx
      have hx' := h hx
      simp only [LB.wchart] at hx' ⊢
      exact Set.mem_iInter.2 fun k => by
        have := Set.mem_iInter.1 hx' k
        simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using this
    obtain ⟨hU, hf⟩ := appLE_spMap_jetPt q hq _ _ h'
    have hj : jetOf m (fun v => valAt' (q v) (LB.wchart L.L φ j) (t.s j).val) =
        jetOf m (fun v => ∏ k, Φ.fr (j k) (Λ k (colsOf n g v)) ^ ε k) := by
      refine jetOf_congr m ((eventually_mem q hq hU).mono fun v hv => ?_)
      have := (H v).2 j hv
      rw [_root_.one_mul] at this
      exact this
    have hf' := hf (t.s j).val
    rw [hj] at hf'
    refine Eq.trans ?_ hf'
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    show ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom
      (((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE _).op).hom _) = _
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

end GlobalTheory.AnValJetGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AppellHumbertFrameSemicharacter
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem semichar_herm_zero_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) : hermForm Hm 0 w = 0 := by
  simp [hermForm]

theorem semichar_herm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem semichar_herm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem semichar_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hH.apply]
  ring

section

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.exists_chart_lat : ∃ j, ∀ a ∈ Φ.lat, ⊤ ≤ (Φ.e a).left ⁻¹ᵁ L.L.U j := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ : ∃ j, (Φ.e 0).left pt ∈ L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hj0 : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := fun z _ => by
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) z pt
    rw [hz]
    exact hj
  refine ⟨j, fun a ha => ?_⟩
  rw [(Φ.e_ker a).2 ha, ← (Φ.e_ker 0).2 Φ.lat.zero_mem]
  exact hj0

theorem AnFr.χ_add {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
  obtain ⟨j, hj⟩ := Φ.exists_chart_lat
  have hab := Φ.lat.add_mem ha hb
  have h1 := Φ.fr_per a ha j 0 (hj 0 Φ.lat.zero_mem)
  have h2 := Φ.fr_per b hb j a (hj a ha)
  have h3 := Φ.fr_per (a + b) hab j 0 (hj 0 Φ.lat.zero_mem)
  have hne : Φ.fr j (a + b) ≠ 0 := Φ.fr_ne j _ (hj _ hab)
  rw [zero_add, h2] at h1
  rw [zero_add] at h3
  simp only [semichar_herm_zero_left, mul_zero, zero_add] at h1 h3
  have key : Φ.χ (a + b) * Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) =
      Φ.χ a * Φ.χ b * (Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
        Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b)) := by
    have := h3.symm.trans h1
    apply mul_right_cancel₀ hne
    linear_combination this
  have hexp : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm a a) *
      Complex.exp (↑Real.pi * hermForm Φ.Hm a b + ↑Real.pi / 2 * hermForm Φ.Hm b b) =
      Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) *
        Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [semichar_herm_add_left, semichar_herm_add_right, semichar_herm_add_right, semichar_herm_swap Φ.herm a b]
    have hsc : hermForm Φ.Hm a b - star (hermForm Φ.Hm a b) =
        2 * ((hermForm Φ.Hm a b).im : ℂ) * Complex.I := by
      rw [show star (hermForm Φ.Hm a b) = (starRingEnd ℂ) (hermForm Φ.Hm a b) from rfl, Complex.sub_conj]
      push_cast; ring
    linear_combination (↑Real.pi / 2 : ℂ) * hsc
  rw [hexp] at key
  have hE : Complex.exp (↑Real.pi / 2 * hermForm Φ.Hm (a + b) (a + b)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hE
  linear_combination key

theorem AnFr.χ_ne_zero {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ a ≠ 0 := fun h => by
  have := Φ.χ_norm a ha
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem AnFr.herm_im_swap (a b : Fin g → ℂ) : (hermForm Φ.Hm b a).im = -(hermForm Φ.Hm a b).im := by
  rw [semichar_herm_swap Φ.herm a b]
  simp

theorem AnFr.herm_im_int {a b : Fin g → ℂ} (ha : a ∈ Φ.lat) (hb : b ∈ Φ.lat) :
    ∃ k : ℤ, (hermForm Φ.Hm a b).im = k := by
  have h1 := Φ.χ_add ha hb
  have h2 := Φ.χ_add hb ha
  rw [add_comm b a, h1, Φ.herm_im_swap a b, mul_comm (Φ.χ b)] at h2
  have h3 := mul_left_cancel₀ (mul_ne_zero (Φ.χ_ne_zero ha) (Φ.χ_ne_zero hb)) h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h3
  refine ⟨n, ?_⟩
  have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (((hermForm Φ.Hm a b).im : ℝ) : ℂ) = (n : ℂ) := by
    apply mul_left_cancel₀ hπ
    push_cast at hn
    linear_combination hn
  exact_mod_cast this

theorem AnFr.herm_im_self (a : Fin g → ℂ) : (hermForm Φ.Hm a a).im = 0 := by
  have := Φ.herm_im_swap a a
  linarith

theorem AnFr.χ_add_self {a : Fin g → ℂ} (ha : a ∈ Φ.lat) : Φ.χ (a + a) = Φ.χ a ^ 2 := by
  rw [Φ.χ_add ha ha, Φ.herm_im_self]
  simp [sq]

theorem AnFr.χ_zero : Φ.χ 0 = 1 := by
  have h := Φ.χ_add_self Φ.lat.zero_mem
  rw [add_zero] at h
  apply mul_left_cancel₀ (Φ.χ_ne_zero Φ.lat.zero_mem)
  linear_combination -h

end

theorem anFr_semichar : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, ∀ b ∈ Φ.lat, (∃ k : ℤ, (hermForm Φ.Hm a b).im = k) ∧ Φ.χ (a + b) = Φ.χ a * Φ.χ b * Complex.exp (Real.pi * Complex.I * ((hermForm Φ.Hm a b).im : ℂ))) ∧ Φ.χ 0 = 1 ∧ ((∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ a ∈ Φ.lat, Φ.χ ((2 : ℂ) • a) = 1) := by
  intro S A _ _ L x0 g Φ
  refine ⟨fun a ha b hb => ⟨Φ.herm_im_int ha hb, Φ.χ_add ha hb⟩, Φ.χ_zero, fun h a ha => ?_⟩
  rw [two_smul, Φ.χ_add_self ha, h a ha]

end GlobalTheory.AnVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorJetReading
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnValJetEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

theorem jet_point_eq {K : Type} [Field K] {I : Type} {m : ℕ} (p : PrimeSpectrum (Jet K I m)) :
    p = IsLocalRing.closedPoint (Jet K I m) := by
  apply PrimeSpectrum.ext
  refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun a ha => ?_
  have hn : IsNilpotent a := by
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff q = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_jetAug _ (by rwa [jetAug_mk]))
    have := jet_nilpotent_of_orig K I m (sub_const_mem_orig (R := K) q)
    rwa [h0, map_zero, sub_zero] at this
  obtain ⟨n, hn⟩ := hn
  exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)

theorem res_res' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_id' {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  apply Units.ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have : (homOfLE h).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

theorem res_pullU {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ U)
    (h' : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)ˣ) (b : Γ(Y, ⊤)ˣ) (hb : (f.appLE U ⊤ h').hom a.val = b.val) :
    res h (pullU f U a) = res (le_top : W ≤ ⊤) b := by
  have : b = res h' (pullU f U a) := Units.ext hb.symm
  rw [this, res_res']

theorem exists_gen_of_units {X Y : Scheme.{0}} (L : LB X) (hY : ∀ p q : Y, p = q) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : K → L.ι → Γ(Y, ⊤)ˣ)
    (hu : ∀ k j j' (h : ⊤ ≤ φ k ⁻¹ᵁ (L.U j ⊓ L.U j')),
      (u k j).val = ((φ k).appLE _ ⊤ h).hom (L.g j j').val * (u k j').val) :
    ∃ τ : LB.Gen (LB.LinComb L φ ε), τ.IsGen ∧ ∀ (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j),
      (Y.presheaf.map (homOfLE h).op).hom (τ.s j).val = (∏ k, u k (j k) ^ ε k).val := by
  refine ⟨⟨fun j => res le_top (∏ k, u k (j k) ^ ε k)⟩, fun (i : K → L.ι) (j : K → L.ι) => ?_, fun j h => ?_⟩
  · by_cases hne : ∃ p, p ∈ LB.wchart L φ i ⊓ LB.wchart L φ j
    · obtain ⟨p, hp⟩ := hne
      have hk : ∀ k, ⊤ ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k q _ => by
        rw [hY q p]
        exact ⟨LB.wchart_le L φ i k hp.1, LB.wchart_le L φ j k hp.2⟩
      have hle : ∀ k, LB.wchart L φ i ⊓ LB.wchart L φ j ≤ φ k ⁻¹ᵁ (L.U (i k) ⊓ L.U (j k)) := fun k =>
        le_top.trans (hk k)
      show res (inf_le_left : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ i) (res le_top (∏ k, u k (i k) ^ ε k)) =
        (∏ k, (res (hle k) (pullU (φ k) _ (L.g (i k) (j k)))) ^ (ε k)) *
          res (inf_le_right : LB.wchart L φ i ⊓ LB.wchart L φ j ≤ LB.wchart L φ j) (res le_top (∏ k, u k (j k) ^ ε k))
      rw [res_res', res_res', map_prod, map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [res_pullU (φ k) _ _ (hk k) (L.g (i k) (j k)) (u k (i k) * (u k (j k))⁻¹)
        (by rw [Units.val_mul, hu k _ _ (hk k), Units.mul_inv_cancel_right]), map_zpow, map_zpow, ← mul_zpow,
        ← map_mul, inv_mul_cancel_right]
    · have hb : LB.wchart L φ i ⊓ LB.wchart L φ j = ⊥ :=
        le_bot_iff.1 fun p hp => (hne ⟨p, hp⟩).elim
      have : Subsingleton Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j) := by
        rw [hb]; infer_instance
      exact Units.ext (this.elim _ _)
  · exact congrArg Units.val ((res_res' le_top h _).trans (res_id' _ _))

theorem jetOf_one {d : ℕ} (m : ℕ) : jetOf m (fun _ : Fin d → ℂ => (1 : ℂ)) = 1 := by
  rw [jetOf_const, map_one]

theorem jetOf_pow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (k : ℕ) :
    jetOf m (fun z => f z ^ k) = jetOf m f ^ k := by
  induction k with
  | zero => simpa using jetOf_one m
  | succ k ih =>
    rw [pow_succ, ← ih, ← jetOf_mul m (hf.pow k) hf]
    congr 1

theorem contDiffAt_zpow' {d : ℕ} {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0) (k : ℤ) :
    ContDiffAt ℂ ω (fun z => f z ^ k) 0 := by
  cases k with
  | ofNat k => simpa using hf.pow k
  | negSucc k =>
    simp only [zpow_negSucc]
    exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)

theorem jetOf_zpow {d : ℕ} (m : ℕ) {f : (Fin d → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (h0 : f 0 ≠ 0)
    (u : (Jet ℂ (Fin 1 × Fin d) m)ˣ) (hu : u.val = jetOf m f) (k : ℤ) :
    jetOf m (fun z => f z ^ k) = (u ^ k).val := by
  cases k with
  | ofNat k => simpa [hu] using jetOf_pow m hf k
  | negSucc k =>
    rw [zpow_negSucc]
    refine Units.eq_inv_of_mul_eq_one_left ?_
    rw [Units.val_pow_eq_pow_val, hu, ← jetOf_pow m hf,
      ← jetOf_mul m (hf.pow (k + 1)) (contDiffAt_zpow' hf h0 _), ← jetOf_one m]
    refine jetOf_congr m ((hf.continuousAt.eventually_ne h0).mono fun z hz => ?_)
    show f z ^ (k + 1) * f z ^ (Int.negSucc k) = 1
    rw [zpow_negSucc, mul_inv_cancel₀ (pow_ne_zero _ hz)]

theorem jetOf_prod {d : ℕ} (m : ℕ) {K : Type} (s : Finset K) {f : K → (Fin d → ℂ) → ℂ}
    (hf : ∀ k, ContDiffAt ℂ ω (f k) 0) :
    jetOf m (fun z => ∏ k ∈ s, f k z) = ∏ k ∈ s, jetOf m (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetOf_one m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ← ih, ← jetOf_mul m (hf a) (contDiffAt_prod fun k _ => hf k)]
    congr 1
    funext z
    simp [Finset.prod_insert ha]

theorem appLE_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by
  have h1 : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U := fun p _ => by
    rw [jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) p]
    show jetPt e hol m (IsLocalRing.closedPoint _) ∈ U
    rwa [jetPt_closedPoint]
  have e1 : (spMap r ≫ jetPt e hol m).appLE U ⊤ h = (jetPt e hol m).appLE U ⊤ h1 ≫ (spMap r).appTop :=
    (Scheme.Hom.appLE_comp_appLE (spMap r) (jetPt e hol m) U ⊤ ⊤ h1 le_rfl).symm
  rw [e1, jetPt_appLE e hol m U hU h1, Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem mem_of_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {I : Type} (r : Jet ℂ (Fin 1 × Fin d) m →+* Jet ℂ I m) (U : Y.Opens)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) : e 0 cpt ∈ U := by
  let p : Sp (Jet ℂ I m) := IsLocalRing.closedPoint (Jet ℂ I m)
  have h2 : (spMap r ≫ jetPt e hol m) p ∈ U := h (show p ∈ (⊤ : (Sp (Jet ℂ I m)).Opens) from trivial)
  rw [Scheme.Hom.comp_apply] at h2
  rw [← jetPt_closedPoint e hol m, ← jet_point_eq (K := ℂ) (I := Fin 1 × Fin d) (m := m) (spMap r p)]
  exact h2

theorem contDiffAt_fr {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) {n : ℕ} (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (j : L.L.ι)
    (h : (Φ.e (Λ (colsOf n g 0))).left cpt ∈ L.L.U j) :
    ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0 := by
  have h1 : ContDiffAt ℂ ω (Φ.fr j) (Λ (colsOf n g 0)) :=
    (ReciprocityTheory.AnForm.Osgood.osgood g {z | ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j} (Φ.fr j) (Φ.hol (L.L.U j) 0).1 (Φ.fr_hol j) _
      (top_le_of_mem h)).contDiffAt
  have h2 : ContDiff ℂ ω (colsOf n g) :=
    contDiff_pi.2 fun i => contDiff_pi.2 fun j => contDiff_apply ℂ (fun _ => ℂ) (finProdFinEquiv (i, j))
  have h3 : ContDiff ℂ ω (fun v => Λ (colsOf n g v)) :=
    (LinearMap.toContinuousLinearMap Λ).contDiff.comp h2
  exact h1.comp 0 h3.contDiffAt

theorem exists_gen_jetRd : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), ∀ (n m : ℕ) (K : Type) [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ k, Φ.JetMap m (φ k) (Λ k)) → ∃ τ : LB.Gen (LB.LinComb L.L φ ε), τ.IsGen ∧ Φ.JetRd m φ ε τ Λ := by
  intro S A _ _ L x0 g Φ n m K _ φ ε Λ hφ
  classical
  have hφ' := hφ
  choose hol hφe using hφ'
  let r : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m := renN n g m
  let F : K → L.L.ι → (Fin (n * g) → ℂ) → ℂ := fun k j v => Φ.fr j (Λ k (colsOf n g v))
  let u0 : K → L.L.ι → (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ := fun k j =>
    if h : IsUnit (jetOf m (F k j)) then h.unit else 1
  have hmem : ∀ k (U : A.left.Opens), ⊤ ≤ φ k ⁻¹ᵁ U → (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ U := fun k U h =>
    mem_of_spMap_jetPt _ (hol k) m r U (by rw [hφe k] at h; exact h)
  have hF0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → F k j 0 ≠ 0 := fun k j h =>
    Φ.fr_ne j _ (top_le_of_mem h)
  have hu0 : ∀ k j, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U j → (u0 k j).val = jetOf m (F k j) := fun k j h => by
    have hu : IsUnit (jetOf m (F k j)) := isUnit_of_jetAug _ (by rw [jetAug_jetOf]; exact hF0 k j h)
    simp only [u0, dif_pos hu, IsUnit.unit_spec]
  let ρ : (Jet ℂ (Fin 1 × Fin (n * g)) m)ˣ →* Γ(Sp (Jet ℂ (Fin n × Fin g) m), ⊤)ˣ :=
    Units.map ((toΓ (Jet ℂ (Fin n × Fin g) m)).comp r).toMonoidHom
  have hρ : ∀ a, (ρ a).val = toΓ _ (r a.val) := fun _ => rfl
  obtain ⟨τ, h1, h2⟩ := exists_gen_of_units L.L (Y := Sp (Jet ℂ (Fin n × Fin g) m))
    (fun p q => (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) p).trans
      (jet_point_eq (K := ℂ) (I := Fin n × Fin g) (m := m) q).symm) φ ε (fun k j => ρ (u0 k j)) (fun k j j' h => by
      have hm := hmem k _ h
      have key : ∀ (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left) (h : ⊤ ≤ ψ ⁻¹ᵁ (L.L.U j ⊓ L.L.U j')),
          ψ = spMap r ≫ jetPt _ (hol k) m → (ψ.appLE _ ⊤ h).hom (L.L.g j j').val = toΓ _ (r (jetOf m fun z =>
            valAt' (Φ.e (Λ k (colsOf n g z))).left (L.L.U j ⊓ L.L.U j') (L.L.g j j').val)) := by
        rintro _ h rfl
        exact appLE_spMap_jetPt _ (hol k) m r _ hm h _
      rw [key _ h (hφe k), hρ, hρ, ← map_mul, ← map_mul, hu0 k j hm.1, hu0 k j' hm.2,
        ← jetOf_mul m (contDiffAt_val _ (hol k) hm _) (contDiffAt_fr Φ (Λ k) j' hm.2)]
      exact congrArg (fun x => toΓ _ (r x))
        (jetOf_congr m ((eventually_mem _ (hol k) hm).mono fun z hz => Φ.fr_g j j' _ hz)))
  refine ⟨τ, h1, hφ, fun j h => ?_⟩
  have hm : ∀ k, (Φ.e (Λ k (colsOf n g 0))).left cpt ∈ L.L.U (j k) := fun k =>
    hmem k _ (h.trans (LB.wchart_le L.L φ j k))
  rw [h2 j h]
  have e1 : (∏ k, ρ (u0 k (j k)) ^ ε k) = ρ (∏ k, u0 k (j k) ^ ε k) := by
    simp only [map_prod, map_zpow]
  rw [e1, hρ]
  show toΓ _ (r _) = toΓ _ (r (jetOf m fun v => ∏ k, F k (j k) v ^ ε k))
  refine congrArg (fun x => toΓ _ (r x)) ?_
  rw [jetOf_prod m Finset.univ (f := fun k v => F k (j k) v ^ ε k)
    (fun k => contDiffAt_zpow' (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _), Units.coe_prod]
  exact Finset.prod_congr rfl fun k _ =>
    (jetOf_zpow m (contDiffAt_fr Φ (Λ k) _ (hm k)) (hF0 k _ (hm k)) _ (hu0 k _ (hm k)) _).symm

end GlobalTheory.AnValJetEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

theorem isHolFam_pullback_lift : ∀ (X Y₁ Y₂ : Scheme.{0}) (p₁ : Y₁ ⟶ X) (p₂ : Y₂ ⟶ X) (N : ℕ) (e₁ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₁)) (e₂ : (Fin N → ℂ) → (Sp ℂ ⟶ Y₂)) (u : Sp ℂ ⟶ X) (h₁ : ∀ z, e₁ z ≫ p₁ = u) (h₂ : ∀ z, e₂ z ≫ p₂ = u), IsHolFam e₁ → IsHolFam e₂ → IsHolFam (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm)) := by
  intro X Y₁ Y₂ p₁ p₂ N e₁ e₂ u h₁ h₂ hol₁ hol₂
  have ea : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) = e₁ :=
    funext fun z => pullback.lift_fst _ _ _
  have eb : (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) = e₂ :=
    funext fun z => pullback.lift_snd _ _ _
  have ha : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.fst p₁ p₂) := by
    rw [ea]
    intro U f
    simpa using hol₁ U f
  have hb : IsHolTo (Set.univ : Set (Fin N → ℂ))
      (fun z => pullback.lift (e₁ z) (e₂ z) ((h₁ z).trans (h₂ z).symm) ≫ pullback.snd p₁ p₂) := by
    rw [eb]
    intro U f
    simpa using hol₂ U f
  have hc := GlobalTheory.HolFibre.isHolTo_of_isPullback (IsPullback.of_hasPullback p₁ p₂) ha hb
  intro U f
  simpa using hc U f

end GlobalTheory.AnVal
end

