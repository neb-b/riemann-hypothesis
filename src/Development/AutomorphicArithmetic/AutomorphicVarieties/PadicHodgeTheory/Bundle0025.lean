module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PosExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Z1fMap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem crOn_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have he : Function.Surjective (fun g : (⊤ : Subgroup G) => (g : G)) := fun g => ⟨⟨g, trivial⟩, rfl⟩
  have hr : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    ext σ
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, trivial⟩, hg⟩⟩
  have hc : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact he.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold CrOn IsCr
  rw [hr, hc]

private def glOn {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G)
    (r : G →* GG (m := m) (R := R))
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B]
    (r : GQ l →* GG (m := 3) (R := B))
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glOn D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glOn D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

theorem UpperTheory.V.Loc.dualCr :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
      [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
      (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E]
      [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
      [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
      (r : GQ l →* GG (m := 3) (R := E)), HasMult D.η r → Continuous (fun g => (r g).mat) →
      ∀ γ ∈ Z1 (adRep r), ∀ r' : GQ l →* GG (m := 3) (R := DualNumber E), DualDef r γ r' →
        (D.IsLCr r' ↔ D.IsLCr r ∧ γ ∈ finiteCocycles (MonoidHom.id _) (adRep r)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _ r hm hr γ hγ r' hd
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    haveI := D.Kv.2
    rw [e]
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hH : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  haveI : D.HL.Normal := inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal
  haveI : Finite (GQ l ⧸ D.HL) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : D.HL.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have h1' : ∀ g ∈ D.HL, (r' g).right = 1 := fun g hg => (hd g).1.trans (h1 g hg)
  have had : ((adRep r).comp D.HL.subtype : Representation E D.HL _) = adGL (glOn D.HL r h1) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun X => ?_
    change (r g).adFun X = _
    rw [GG.adFun, if_pos (h1 g g.2)]
    rfl
  have hy : (fun h : D.HL => γ h) ∈ Z1 (adGL (glOn D.HL r h1)) := by
    rw [← had]
    exact ⟨hγ.1.comp continuous_subtype_val, fun g h => hγ.2 g h⟩
  have key := deformCr D.HL.subtype hH.isOpenEmbedding_subtypeVal (glOn D.HL r h1)
    (hr.comp continuous_subtype_val) _ hy (glOn D.HL r' h1') (fun g i j => (hd g).2 i j) ⊤ (by simp)
  rw [isLCr_iff D r' h1', isLCr_iff D r h1, ← crOn_top, ← crOn_top, key,
    z1fDesc (MonoidHom.id _) (adRep r) D.HL γ hγ, had, MonoidHom.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsContinuousIsGamOfTorusCocycle
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem gam_cocycle {G B : Type} [Group G] [CommRing B] {η : G →* ℤˣ} (T : Tor η B) (h : B)
    (β : G → B × B) (hβ : ∀ g g', β (g * g') = β g + T.M1 g (β g')) (a b c : G) :
    (T.χ2 a : B) * (-(h * omg (β b) (T.M1 b (β c)))) - (-(h * omg (β (a * b)) (T.M1 (a * b) (β c))))
      + (-(h * omg (β a) (T.M1 a (β (b * c))))) - (-(h * omg (β a) (T.M1 a (β b)))) = 0 := by
  have e := T.alternatingForm_adjointSuperdiagRep a (β b) (T.M1 b (β c))
  rw [hβ a b, hβ b c, map_mul, Module.End.mul_apply, map_add (f := _)]
  generalize T.M1 a (T.M1 b (β c)) = u at e ⊢
  generalize T.M1 a (β b) = w at e ⊢
  simp only [omg, Prod.fst_add, Prod.snd_add] at e ⊢
  linear_combination h * e

theorem UpperTheory.exists_continuous_isGam_of_torus_cocycle :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {η : GQ l →* ℤˣ} {Ψ : GQ l →* Eˣ} {H : Subgroup (GQ l)} {e : ℕ} (hD : TriDat η Ψ H e) {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (T : Tor η B), T.Good π Ψ → ∀ (h : B), ∀ β ∈ Z1 T.M1, ∃ γ : GQ l → B, Continuous γ ∧ T.IsGam h β γ := by
  intro hP l _ E _ _ _ _ _ η Ψ H e hD B _ _ _ _ _ _ _ _ _ _ π hπ T hT h β hβ
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  have hχ := Tor.continuous_χ2 hD.ηlc T hT.cont hT.cont_inv
  have hM := Tor.contAction_torus_module hD.ηlc T hT.cont hT.cont_inv
  have hρ : ContAction (resCoef E (chRep T.χ2)) := contAction_chRep hχ
  obtain ⟨-, f2, -, e2⟩ := tateRat hP (v := l) (l := l) (MonoidHom.id (GQ l)) IsOpenEmbedding.id
    (resCoef E (chRep T.χ2)) hρ
  obtain ⟨s, hs, hsi⟩ := ((cycInertia l).2 H hD.isOpen).2
  have hsH : s ∈ H := hs.1
  have hsI : s ∈ Iq l := hs.2
  have hχs : (T.χ2 s : B) = algebraMap E B ((cycA l l E s ^ (2 * e) : Eˣ) : E) := by
    have h0 := hT.ine s hsI 0
    have h2 := hT.ine s hsI 2
    have w0 : wt1 (0 : Fin 3) = 1 := by decide
    have w2 : wt1 (2 : Fin 3) = -1 := by decide
    rw [w0, zpow_one] at h0
    rw [w2, zpow_neg_one] at h2
    have k0 : T.t s 0 = Units.map (algebraMap E B : E →* B) (Ψ s) := Units.ext h0
    have k2 : T.t s 2 = Units.map (algebraMap E B : E →* B) (Ψ s)⁻¹ := Units.ext h2
    rw [Tor.χ2_apply, hD.ηH s hsH, k0, k2, ← map_div, div_inv_eq_mul, hD.ΨH s hsH hsI, ← pow_add, ← two_mul]
    simp
  have hne : ((cycA l l E s ^ (2 * e) : Eˣ) : E) ≠ (cycA l l E s : E) := by
    intro hc
    apply hsi
    have h1 : cycA l l E s ^ (2 * e - 1) = 1 := by
      have := Units.ext hc
      have he := hD.e_pos
      rw [show 2 * e = (2 * e - 1) + 1 by omega, pow_succ] at this
      exact mul_eq_right.1 this
    have inj : Function.Injective (algebraMap ℤ_[l] E) := by
      rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨2 * e - 1, by have := hD.e_pos; omega, ?_⟩
    apply Units.map_injective (f := (algebraMap ℤ_[l] E : ℤ_[l] →* E)) inj
    rw [map_pow, map_one]
    exact h1
  have hbot : H0dual ((cycA l l E).comp (MonoidHom.id (GQ l))) (resCoef E (chRep T.χ2)) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    have h1 : f ((T.χ2 s : B) * x) = (cycA l l E s : E) * f x := hf s x
    rw [hχs, ← Algebra.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.1 (show (_ - _) * f x = 0 by rw [sub_mul, h1, sub_self])).resolve_left (sub_ne_zero.2 hne)
  rw [hbot, finrank_bot] at e2
  haveI := f2
  have hsub : Subsingleton (H2 (resCoef E (chRep T.χ2))) := Module.finrank_zero_iff.1 e2
  have hc : Continuous fun p : GQ l × GQ l => -(h * omg (β p.1) (T.M1 p.1 (β p.2))) := by
    have a1 : Continuous fun p : GQ l × GQ l => β p.1 := hβ.1.comp continuous_fst
    have a2 : Continuous fun p : GQ l × GQ l => T.M1 p.1 (β p.2) :=
      hM.comp (continuous_fst.prodMk (hβ.1.comp continuous_snd))
    exact (continuous_const.mul ((a1.fst.mul a2.snd).sub (a1.snd.mul a2.fst))).neg
  let z : Z2 (resCoef E (chRep T.χ2)) := ⟨fun p => -(h * omg (β p.1) (T.M1 p.1 (β p.2))), hc,
    fun a b c => gam_cocycle T h β hβ.2 a b c⟩
  have hz : z ∈ (B2 (resCoef E (chRep T.χ2))).comap (Z2 (resCoef E (chRep T.χ2))).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim _ _)
  obtain ⟨γ, hγ, hγ2⟩ := (separated_dvr_second_cohomology_mem _ _).1 hz
  refine ⟨γ, hγ, fun g g' => ?_⟩
  have h1 : (T.χ2 g : B) * γ g' - γ (g * g') + γ g = -(h * omg (β g) (T.M1 g (β g'))) := congrFun hγ2 (g, g')
  linear_combination -h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallineTriangularLiftOfMemFiniteCocycl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem mem_ker_smul {B E : Type} [CommRing B] [CommRing E] (π : B →+* E) (u v : B) (hu : π u = 0)
    (hv : π v = 0) : ((u, v) : B × B) ∈ (RingHom.ker π) • (⊤ : Submodule B (B × B)) := by
  have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
  rw [h]
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hu trivial) (Submodule.smul_mem_smul hv trivial)

private def triHom {G B : Type} [Group G] [CommRing B] (κ : Fin 3 → G →* Bˣ) (x y z : G → B)
    (hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h)
    (hy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h)
    (hz : ∀ g h, z (g * h) = z g + (((κ 0 / κ 2) g : Bˣ) * z h + x g * ((κ 1 / κ 2) g : Bˣ) * y h)) :
    G →* Matrix (Fin 3) (Fin 3) B where
  toFun g := triM (fun i => κ i g) (x g) (y g) (z g)
  map_one' := by
    have h1 := hx 1 1
    have h2 := hy 1 1
    have h3 := hz 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add] at h1 h2
    simp only [mul_one, map_one, Units.val_one, one_mul, left_eq_add, h1, zero_mul, add_zero] at h3
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3]
  map_mul' g h := by
    have e : ∀ i j, (κ i g : B) = (((κ i / κ j) g : Bˣ) : B) * κ j g := fun i j => by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have e1 := e 0 1
    have e2 := e 1 2
    have e3 := e 0 2
    have h1 := hx g h
    have h2 := hy g h
    have h3 := hz g h
    generalize (((κ 0 / κ 1) g : Bˣ) : B) = p at *
    generalize (((κ 1 / κ 2) g : Bˣ) : B) = q at *
    generalize (((κ 0 / κ 2) g : Bˣ) : B) = r at *
    ext i j
    fin_cases i <;> fin_cases j <;> simp [triM, h1, h2, h3, Matrix.mul_apply, Fin.sum_univ_three]
    · linear_combination (-(x h * κ 1 h)) * e1
    · linear_combination (-(z h * κ 2 h)) * e3 - (x g * y h * κ 2 h) * e2
    · linear_combination (-(y h * κ 2 h)) * e2

theorem UpperTheory.exists_crystalline_triangular_lift_of_mem_finiteCocycles :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)), ∀ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)), (∀ g, π (x g) = 0) → ∃ (z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z ∧ (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) ∧ IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e ψ κ hκ x hx y hy hx0
  haveI : ContinuousConstSMul E B := contConstSMul_alg E
  haveI : Module.Finite E B := Module.Finite.of_restrictScalars_finite ℚ_[l] E B
  have hxc : Continuous x := hx.1.1
  have hyc : Continuous y := hy.1.1
  have hxm : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := hx.1.2
  have hym : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := hy.1.2
  have hab : (κ 0 / κ 2) / (κ 1 / κ 2) = κ 0 / κ 1 := div_div_div_cancel_right _ _ _
  have hxm' : ∀ g h, x (g * h) = x g + (((κ 0 / κ 2) / (κ 1 / κ 2)) g : Bˣ) * x h := by rw [hab]; exact hxm
  have hcr : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ _ (contAction_chRep (hκ.cont i)) (e * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg, smul_eq_mul]
  have hcd : ∀ i j, Continuous fun g => (((κ i / κ j) g : Bˣ) : B) := fun i j => cont_char_div (hκ.cont i) (hκ.cont j)
  have hcr' : ∀ i j, IsCr φ (chRep (κ i / κ j)) := fun i j =>
    crUnr φ hφ _ (contAction_chRep (hcd i j)) (e * wt1 i - e * wt1 j) fun g hg v => by
      rw [chRep_apply, MonoidHom.div_apply, hκ.ine g hg, hκ.ine g hg, smul_eq_mul, zpow_sub, div_eq_mul_inv]
  have hred : ∀ i j g, π (((κ i / κ j) g : Bˣ) : B) = ((ψ g ^ (wt1 i - wt1 j) : Eˣ) : E) := fun i j g => by
    have h1 : (((κ i / κ j) g : Bˣ) : B) * κ j g = κ i g := by
      rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
    have h2 := congrArg π h1
    rw [map_mul, hκ.red, hκ.red] at h2
    rw [zpow_sub, Units.val_mul, ← h2, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  let T := ext2 (κ 0 / κ 2) (κ 1 / κ 2) x hxm'
  have hTc : ContAction T := contAction_charExtension_of_continuous_cocycle (hcd 0 2) (hcd 1 2) hxm' hxc
  have hTcr : IsCr φ T :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hcd 0 2) (hcd 1 2) x hxm' hxc (hcr' 0 2) (hcr' 1 2)).2 (by rw [hab]; exact hx)
  have hTdr : IsDr φ (resCoef E T) := (isCrys_isDR_restrict_openSubgroup φ hφ T hTc).1 hTcr
  have hwt : ∀ n : ℕ, 1 ≤ n → ψ ^ n ∈ {κ : G →* Eˣ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := fun n hn =>
    ⟨((e * n : ℕ) : ℤ), by exact_mod_cast Nat.mul_pos hκ.e_pos hn, ⊤, by simp, fun g _ hg => by
      rw [MonoidHom.pow_apply, hκ.wt g hg, zpow_natCast, pow_mul]⟩
  have hTf : FiltBy (resCoef E T) {κ | ∃ w : ℤ, 1 ≤ w ∧ HasWeight φ κ w} := by
    refine UpperTheory.filtBy_restrictScalars_of_residual_characters π hπ T _ (ι := Fin 2) ![(1, 0), (0, 1)] ![ψ ^ 2, ψ ^ 1] ?_ ?_ ?_
    · rw [eq_top_iff]
      rintro ⟨u, v⟩ -
      have h : ((u, v) : B × B) = u • ((1, 0) : B × B) + v • ((0, 1) : B × B) := by simp
      rw [h]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · intro j
      fin_cases j
      · exact hwt 2 (by norm_num)
      · exact hwt 1 le_rfl
    · intro g j
      have a1 := hred 0 2 g
      have a2 := hred 1 2 g
      have w1 : wt1 0 - wt1 2 = ((2 : ℕ) : ℤ) := by decide
      have w2 : wt1 1 - wt1 2 = ((1 : ℕ) : ℤ) := by decide
      rw [w1, zpow_natCast] at a1
      rw [w2, zpow_natCast] at a2
      fin_cases j
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 1 + x g * ((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, mul_zero, add_zero, map_sub, a1, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
        · change π (((κ 1 / κ 2) g : Bˣ) * 0 - ((ψ g ^ 2 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_zero, smul_zero, sub_zero, map_zero]
      · refine mem_ker_smul (π : B →+* E) _ _ ?_ ?_
        · change π (((κ 0 / κ 2) g : Bˣ) * 0 + x g * ((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (0 : B)) = 0
          rw [mul_one, mul_zero, zero_add, smul_zero, sub_zero, map_mul, hx0, zero_mul]
        · change π (((κ 1 / κ 2) g : Bˣ) * 1 - ((ψ g ^ 1 : Eˣ) : E) • (1 : B)) = 0
          rw [mul_one, map_sub, a2, map_smul, map_one, smul_eq_mul, mul_one, sub_self]
  obtain ⟨c, hc, hcy⟩ := (posExact hP φ hφ (resCoef E T) (resCoef E (chRep (κ 1 / κ 2))) hTc
    (contAction_chRep (hcd 1 2)) ⟨hTdr, hTf⟩ (LinearMap.snd E B B) (fun g v => rfl)).1 Prod.snd_surjective y hy
  have hcT : c ∈ UpperTheory.V.Loc.finiteCocycles φ T := hc
  have hc2 : ∀ g, (c g).2 = y g := fun g => congrFun hcy g
  have hzc : Continuous fun g => (c g).1 := hcT.1.1.fst
  have hzm : ∀ g h, (c (g * h)).1 =
      (c g).1 + (((κ 0 / κ 2) g : Bˣ) * (c h).1 + x g * ((κ 1 / κ 2) g : Bˣ) * y h) := fun g h => by
    rw [← hc2 h]
    exact congrArg Prod.fst (hcT.1.2 g h)
  let ρ := (triHom κ x y (fun g => (c g).1) hxm hym hzm).toHomUnits
  refine ⟨fun g => (c g).1, ρ, hzc, fun g => rfl, ?_⟩
  have h01 : IsCr φ (ext2 (κ 0) (κ 1) x hxm) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x hxm hxc (hcr 0) (hcr 1)).2 hx
  refine (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ.cont x y _ ρ hxc hyc hzc (fun g => rfl) hxm h01 (hcr 2)).2 ?_
  have hT : twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hxm) = T := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, characterExtensionRep_apply, characterExtensionRep_apply]
    simp only [div_eq_mul_inv, MonoidHom.mul_apply, Units.val_mul, Prod.smul_mk, smul_eq_mul]
    ext <;> simp only [] <;> ring
  have hc' : (fun g => ((c g).1, y g)) = c := funext fun g => by rw [← hc2 g]
  rw [hT, hc']
  exact hcT
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffOfCharData
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem coc {G B : Type} [Group G] [CommRing B] (a b : G →* Bˣ) (x : G → B) (g h : G)
    (H : x (g * h) * (b (g * h) : B) = (a g : B) * (x h * b h) + x g * b g * b h) :
    x (g * h) = x g + ((a / b) g : Bˣ) * x h := by
  have e : (((a / b) g : Bˣ) : B) * b g = a g := by
    rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
  refine (b (g * h)).mul_left_inj.1 ?_
  rw [H, map_mul, Units.val_mul, ← e]
  ring

theorem UpperTheory.isCrystalline_triangular_iff_of_charData :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → IsCr φ (colRep ρ) → x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)) ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ e ψ κ hκ x y z ρ hx hy hz hρ hcr
  have hm : ∀ g h, triM (fun i => κ i (g * h)) (x (g * h)) (y (g * h)) (z (g * h)) =
      triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i h) (x h) (y h) (z h) := fun g h => by
    rw [← hρ, ← hρ, ← hρ, map_mul, Units.val_mul]
  have cx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 0) 1
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have cy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 1) 2
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have hch : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ.cont i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg i, smul_eq_mul]
  have hc : ContAction (colRep ρ) := contAction_colRep (by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ.cont hx hy hz)
  let f1 : (B × B) →ₗ[ℚ_[l]] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  let f2 : (Fin 3 → B) →ₗ[ℚ_[l]] (B × B) :=
    { toFun := fun v => (v 1, v 2)
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }
  refine ⟨(UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x cx hx (hch 0) (hch 1)).1 ?_,
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 1) (hκ.cont 2) y cy hy (hch 1) (hch 2)).1 ?_⟩
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ (contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) cx hx) hc f1 fun g v => ?_).1
      fun v w h => ?_).1 hcr
    · rw [colRep_apply, hρ, characterExtensionRep_apply]
      ext i
      fin_cases i <;> simp [f1, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · exact Prod.ext (congrFun h 0) (congrFun h 1)
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ hc (contAction_charExtension_of_continuous_cocycle (hκ.cont 1) (hκ.cont 2) cy hy) f2 fun g v => ?_).2
      fun v => ⟨![0, v.1, v.2], rfl⟩).1 hcr
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext <;> simp [f2, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NormLeOneOfFrobeniusPowEigenvectorMemFilZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

private theorem shift_prod {R : Type} [CommMonoid R] (a : ℕ → R) (f : ℕ) :
    (∏ i ∈ Finset.range f, a (i + 1)) * a 0 = (∏ i ∈ Finset.range f, a i) * a f := by
  rw [← Finset.prod_range_succ', Finset.prod_range_succ]

private theorem descend {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [IsDomain B]
    (PD : PeriodData G Qp K₀ K B BdR) (f : ℕ) (hσ : ∀ x, (PD.σ ^ f) x = x) (b : B) (δ : K₀) (hb : b ≠ 0)
    (hφ : (PD.φ ^ f) b = algebraMap K₀ B δ * b) (hF : ∀ i : ℕ, PD.ι ((PD.φ ^ i) b) ∈ PD.Fil 0) :
    ∃ (c : B) (x : Qp), c ≠ 0 ∧ PD.φ c = algebraMap Qp B x * c ∧ PD.ι c ∈ PD.Fil 0 ∧
      algebraMap Qp K₀ x = ∏ i ∈ Finset.range f, (PD.σ ^ i) δ := by
  have hinj : ∀ (i : ℕ) (y : B), y ≠ 0 → (PD.φ ^ i) y ≠ 0 := by
    intro i y hy h
    apply hy
    have h1 : Function.Injective (PD.φ ^ i) := by
      rw [AlgHom.coe_pow]; exact PD.φ_inj.iterate i
    exact h1 (h.trans (map_zero _).symm)
  have hK : ∀ (i : ℕ) (y : K₀), (PD.φ ^ i) (algebraMap K₀ B y) = algebraMap K₀ B ((PD.σ ^ i) y) := by
    intro i y
    induction i with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, PD.φ_K₀]
  have hprod : ∀ a : ℕ → B, (∀ i, PD.ι (a i) ∈ PD.Fil 0) → PD.ι (∏ i ∈ Finset.range f, a i) ∈ PD.Fil 0 := by
    intro a ha
    rw [map_prod]
    exact Finset.prod_induction _ (fun y => y ∈ PD.Fil 0)
      (fun y z hy hz => by simpa using PD.Fil_mul 0 0 y z hy hz) PD.one_mem fun i _ => ha i
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hinj f b hb (by rw [hφ, map_zero, zero_mul])
  set c := ∏ i ∈ Finset.range f, (PD.φ ^ i) b with hc
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hinj i b hb
  have hφc : PD.φ c = algebraMap K₀ B δ * c := by
    apply mul_right_cancel₀ hb
    have h := shift_prod (fun i => (PD.φ ^ i) b) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hc, hφ] at h
    rw [h]; ring
  set N := ∏ i ∈ Finset.range f, (PD.σ ^ i) δ with hN
  have hσN : PD.σ N = N := by
    apply mul_right_cancel₀ hδ
    have h := shift_prod (fun i => (PD.σ ^ i) δ) f
    simp only [pow_succ', AlgHom.mul_apply, pow_zero, AlgHom.one_apply] at h
    rw [← map_prod, ← hN, hσ] at h
    exact h
  obtain ⟨x, hx⟩ := PD.fund (algebraMap K₀ B N) (by rw [PD.φ_K₀, hσN]) (by
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply K₀ K BdR, Algebra.algebraMap_eq_smul_one]
    exact (PD.Fil 0).smul_mem _ PD.one_mem)
  refine ⟨∏ i ∈ Finset.range f, (PD.φ ^ i) c, x, Finset.prod_ne_zero_iff.2 fun i _ => hinj i c hc0, ?_,
    hprod _ fun i => ?_, ?_⟩
  · rw [hx, hN, map_prod, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hφc, map_mul, hK]
  · rw [hc, map_prod]
    refine hprod _ fun j => ?_
    rw [← AlgHom.mul_apply, ← pow_add]
    exact hF _
  · rw [IsScalarTower.algebraMap_apply Qp K₀ B] at hx
    exact (algebraMap K₀ B).injective hx

private theorem norm_algHom' {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (Om l)}
    (f : ↥K →ₐ[ℚ_[l]] Om l) (x : ↥K) : ‖f x‖ = ‖(x : Om l)‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm]
  have h1 := minpoly.algHom_eq f f.toRingHom.injective x
  have h2 := minpoly.algHom_eq K.val K.val.toRingHom.injective x
  exact congrArg spectralValue (h1.trans h2.symm)

theorem UpperTheory.norm_le_one_of_frobenius_pow_eigenvector_mem_fil_zero :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (f : ℕ), 0 < f → (∀ x : ↥(K0 K), (((PP l).PD K).σ)^[f] x = x) → ∀ (b : Bcr l) (δ : ↥(K0 K)), b ≠ 0 → ((PP l).φB)^[f] b = algebraMap ↥(K0 K) (Bcr l) δ * b → (∀ i : ℕ, (PP l).ιB (((PP l).φB)^[i] b) ∈ ((PP l).PD (botExt l)).Fil 0) → ‖(δ : Om l)‖ ≤ 1 := by
  intro l _ K f hf hσ b δ hb hφ hF
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ((PP l).PD K).φ = (PP l).φB := AlgHom.ext ((PP l).PD_φ K)
  have hFil : ∀ y, y ∈ ((PP l).PD K).Fil 0 ↔ y ∈ ((PP l).PD (botExt l)).Fil 0 := fun y => by
    rw [← SetLike.mem_coe, (PP l).PD_Fil K (botExt l), SetLike.mem_coe]
  obtain ⟨c, x, hc, hφc, hFc, hx⟩ := descend ((PP l).PD K) f (fun y => by rw [AlgHom.coe_pow, hσ]) b δ hb
    (by rw [e, AlgHom.coe_pow, hφ]) (fun i => by rw [e, AlgHom.coe_pow, (PP l).PD_ι, hFil]; exact hF i)
  rw [e] at hφc
  rw [(PP l).PD_ι, hFil] at hFc
  have h1 := UpperTheory.norm_le_one_of_frobenius_eigenvector_mem_fil_zero c x hc hφc hFc
  have h2 := congrArg (fun y : ↥(K0 K) => ‖(K0 K).val y‖) hx
  simp only [map_prod, norm_prod, AlgHom.commutes] at h2
  have h3 : ∀ i : ℕ, ‖(K0 K).val ((((PP l).PD K).σ ^ i) δ)‖ = ‖(δ : Om l)‖ :=
    fun i => norm_algHom' ((K0 K).val.comp (((PP l).PD K).σ ^ i)) δ
  simp only [h3] at h2
  rw [Finset.prod_const, Finset.card_range, norm_algebraMap'] at h2
  rw [h2] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hf.ne').1 h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PrF
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.prF :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Positive φ ρ → H0dual ((cycA l l E).comp φ) ρ = ⊥ → UpperTheory.V.Loc.finiteCocycles φ ρ = Z1 ρ := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hc hpos hd
  obtain ⟨h0, -, -, hf⟩ := UpperTheory.V.Loc.posBasic hP φ hφ ρ hc hpos
  obtain ⟨hfin, -, h1, h2⟩ := UpperTheory.V.Loc.tateRat (v := l) (l := l) hP φ hφ ρ hc
  have hB := (UpperTheory.V.Loc.z1fMap φ ρ ρ).1 hc
  rw [hd, finrank_bot] at h2
  rw [h0, finrank_bot, h2, if_pos rfl, zero_add, zero_add] at h1
  have htop : finiteCohomology φ ρ = ⊤ := Submodule.eq_top_of_finrank_eq (hf.trans h1.symm)
  refine le_antisymm (fun c hc' => hc'.1) (fun c hc' => ?_)
  have hm : (Submodule.mkQ _ (⟨c, hc'⟩ : ↥(ReciprocityTheory.Gal.Z1 ρ)) : ReciprocityTheory.Gal.H1 ρ) ∈ finiteCohomology φ ρ := by
    rw [htop]; trivial
  obtain ⟨y, hy, hyc⟩ := hm
  have hsub := (Submodule.Quotient.eq _).1 hyc
  have h3 : (y : G → V) - c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := hB hsub
  have h4 := (UpperTheory.V.Loc.finiteCocycles φ ρ).sub_mem hy h3
  simpa using h4
end

