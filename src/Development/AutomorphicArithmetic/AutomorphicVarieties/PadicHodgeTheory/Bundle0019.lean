module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormSubgroupOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ConjugateRestrictionOpenNormal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem isCr_comp {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l) (c : G →* G)
    (hc : Function.Surjective c) (ρ : Representation A G V) :
    IsCr (φ.comp c) (ρ.comp c : Representation A G V) ↔ IsCr φ ρ := by
  have hr : (φ.comp c).range = φ.range := by
    ext σ
    refine ⟨fun ⟨g, hg⟩ => ⟨c g, hg⟩, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨g, rfl⟩ := hc g
    exact ⟨g, hg⟩
  have hd : Dcr (φ.comp c) (resCoef ℚ_[l] (ρ.comp c : Representation A G V)) = Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hc.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold IsCr
  rw [hr, hd]

private theorem conj_left {B : Type} [CommRing B] (w : GG (m := 3) (R := B)) (x y : GL (Fin 3) B)
    (h : GG.ofGL y = w * GG.ofGL x * w⁻¹) : y = w.left * sgnAct 3 B w.right x * w.left⁻¹ := by
  have := congrArg SemidirectProduct.left h
  have e : sgnAct 3 B w.right (sgnAct 3 B w.right w.left) = w.left := by
    rw [← MulAut.mul_apply, ← map_mul, Int.units_mul_self, map_one, MulAut.one_apply]
  simpa [e] using this

private theorem dot_inv {B : Type} [CommRing B] (a m : GL (Fin 3) B) (u x : Fin 3 → B) :
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec
      (((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec u))
      ((m : Matrix (Fin 3) (Fin 3) B).mulVec x) =
    dotProduct ((Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)).mulVec u) x := by
  have e : Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) *
      ((a * theta m * a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      ((m⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).transpose *
        (Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    rw [Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
      theta_val]
    simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec x, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem UpperTheory.conjugate_restriction_open_normal :
    ∀ {l : ℕ} [Fact l.Prime] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] (H : Subgroup (GQ l)) [H.Normal], IsOpen (H : Set (GQ l)) → ∀ (ρ ρ' : ↥H →* GL (Fin 3) B), Continuous (fun g => (ρ g : Matrix (Fin 3) (Fin 3) B)) → ∀ (s : GQ l) (w : GG (m := 3) (R := B)), (∀ g g' : H, (g' : GQ l) = s⁻¹ * g * s → GG.ofGL (ρ' g) = w * GG.ofGL (ρ g') * w⁻¹) → IsCr H.subtype (colRep ρ) → IsCr H.subtype (colRep ρ') := by
  intro l _ B _ _ _ _ _ _ H hN hH ρ ρ' hρ s w hw hcr
  have hψ : IsOpenEmbedding H.subtype := hH.isOpenEmbedding_subtypeVal
  let c : H →* H := (MulAut.conjNormal (H := H) s⁻¹).toMonoidHom
  have hc : ∀ g : H, (c g : GQ l) = s⁻¹ * g * s := fun g => by
    change ((MulAut.conjNormal (H := H) s⁻¹ g : H) : GQ l) = _
    rw [MulAut.conjNormal_apply, inv_inv]
  have hcc : Continuous c := by
    refine continuous_induced_rng.2 ?_
    have : Subtype.val ∘ c = fun g : H => s⁻¹ * (g : GQ l) * s := funext hc
    rw [this]
    fun_prop
  let σ : H →* GL (Fin 3) B := ρ.comp c
  have hσ : Continuous (fun g => (σ g : Matrix (Fin 3) (Fin 3) B)) := hρ.comp hcc
  have hσi : Continuous (fun g => (((σ g)⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)) := by
    simp only [← map_inv]
    exact hσ.comp continuous_inv
  have hσcr : IsCr H.subtype (colRep σ) := by
    have h1 := (isCr_comp H.subtype c (MulAut.conjNormal (H := H) s⁻¹).surjective (colRep ρ)).2 hcr
    have h2 : H.subtype.comp c = (MulAut.conj s⁻¹).toMonoidHom.comp H.subtype := by
      refine MonoidHom.ext fun g => ?_
      change (c g : GQ l) = s⁻¹ * g * s⁻¹⁻¹
      rw [hc, inv_inv]
    rw [h2] at h1
    exact (admissible_conjugate H.subtype hψ (colRep σ) s⁻¹).1.1 h1
  have he : ∀ g, ρ' g = w.left * sgnAct 3 B w.right (σ g) * w.left⁻¹ := fun g =>
    conj_left w _ _ (hw g (c g) (hc g))
  generalize w.left = a at he
  rcases Int.units_eq_one_or w.right with h | h
  · simp only [h, sgnAct_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul]
      exact (continuous_const.matrix_mul hσ).matrix_mul continuous_const
    refine ((isCrys_isDR_sub_quot H.subtype hψ (colRep σ) (colRep ρ') (contAction_colRep hσ) (contAction_colRep hρ')
      ((Matrix.toLin' (a : Matrix (Fin 3) (Fin 3) B)).restrictScalars ℚ_[l]) (fun g x => ?_)).2
      (fun v => ?_)).1 hσcr
    · simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, colRep_apply, Matrix.mulVec_mulVec, he,
        ← Units.val_mul, inv_mul_cancel_right]
    · refine ⟨((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B).mulVec v, ?_⟩
      simp only [LinearMap.restrictScalars_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · simp only [h, sgnAct_neg_one] at he
    have hρ' : Continuous (fun g => (ρ' g : Matrix (Fin 3) (Fin 3) B)) := by
      simp only [he, Units.val_mul, theta_val]
      exact (continuous_const.matrix_mul ((continuous_const.matrix_mul hσi.matrix_transpose).matrix_mul
        continuous_const)).matrix_mul continuous_const
    have c1 : ContAction (chRep (1 : H →* Bˣ)) := contAction_chRep continuous_const
    have cr1 : IsCr H.subtype (chRep (1 : H →* Bˣ)) :=
      crUnr (A := ℚ_[l]) H.subtype hψ (resCoef ℚ_[l] (chRep (1 : H →* Bˣ))) c1 0
        (fun g _ x => by simp [resCoef, chRep])
    let N : Matrix (Fin 3) (Fin 3) B := Jmat B 3 * ((a⁻¹ : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B)
    refine (isCrys_isDR_internalHom H.subtype hψ (colRep σ) (chRep (1 : H →* Bˣ)) (colRep ρ') (contAction_colRep hσ) c1
      (contAction_colRep hρ')
      (LinearMap.mk₂ ℚ_[l] (fun (u x : Fin 3 → B) => dotProduct (N.mulVec u) x)
        (fun _ _ _ => by rw [Matrix.mulVec_add, add_dotProduct])
        (fun _ _ _ => by rw [Matrix.mulVec_smul, smul_dotProduct])
        (fun _ _ _ => dotProduct_add _ _ _) (fun _ _ _ => dotProduct_smul _ _ _))
      (fun g u x => ?_) (fun u u' huu => ?_)).1 hσcr cr1
    · simp only [LinearMap.mk₂_apply, colRep_apply, chRep_apply, MonoidHom.one_apply, Units.val_one, one_mul]
      rw [he]
      exact dot_inv a (σ g) u x
    · have h1 : N.mulVec u = N.mulVec u' := by
        funext i
        have := LinearMap.congr_fun huu (Pi.single i 1)
        simpa only [LinearMap.mk₂_apply, dotProduct_single, mul_one] using this
      have h2 : ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3) * N = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Jmat B 3), Jmat_mul_Jmat, Matrix.one_mul, Units.mul_inv]
      have h3 := congrArg ((a : Matrix (Fin 3) (Fin 3) B) * Jmat B 3).mulVec h1
      simpa only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] using h3
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsAlgebraicElementOfAlgebraicVectorSubspace
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial
open GlobalTheory.UnramifiedCrys

private def algSub (p : ℕ) [hp : Fact p.Prime] (R : Type) [CommRing R] [CharP R p] : Subring R where
  carrier := {y | ∃ m, 0 < m ∧ y ^ p ^ m = y}
  one_mem' := ⟨1, one_pos, one_pow _⟩
  zero_mem' := ⟨1, one_pos, zero_pow (pow_pos hp.out.pos _).ne'⟩
  mul_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [add_pow_char_pow, pow_pow_mul hx, mul_comm a b, pow_pow_mul hy]
  neg_mem' := by
    rintro x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    have h := sub_pow_char_pow (p := p) (n := a) (0 : R) x
    rwa [zero_sub, hx, zero_pow (pow_pos hp.out.pos _).ne', zero_sub] at h

private theorem exists_alg {p : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] {R : Type} [CommRing R]
    (ρ : G →* (R ≃+* R)) [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [CharP R p]
    (hopen : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ g in 𝓝 (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hM : Continuous M)
    (hJ : ∀ g, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ g (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        (M g).map (zlW p R) * W.map (WittVector.map f) = W :=
  _root_.UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg ρ hopen M hM hJ

theorem UpperTheory.exists_algebraic_element_of_algebraicVectorSubspace :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ_[l]), IsUnit C.det → ∃ N N' : Matrix (Fin n) (Fin n) (Bcr l), N * N' = 1 ∧ (∀ i j, (PP l).ιB (N i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ (∀ i j, (PP l).ιB (N' i j) ∈ ((PP l).PD (botExt l)).Fil 0) ∧ N.map (PP l).φB = C.map (fun z => algebraMap ℚ_[l] (Bcr l) (z : ℚ_[l])) * N ∧ ∀ g ∈ Iq l, N.map ((PP l).actQ g) = N := by
  intro l _ n C hC
  obtain ⟨-, -, hI, ⟨σ, hσ⟩, -⟩ := iqBasic l
  obtain ⟨Ti⟩ := tiedP l
  obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det C).2 hC
  haveI : CompactSpace (Matrix (Fin n) (Fin n) ℤ_[l]) := inferInstanceAs (CompactSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l]) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → ℤ_[l]))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℤ_[l])).symm.isEmbedding.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) ℤ_[l])ˣ :=
    Units.isEmbedding_embedProduct.isTotallyDisconnected_range.1
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨f, hf, hfI, hfσ⟩ := frobFree σ hσ (Matrix (Fin n) (Fin n) ℤ_[l])ˣ u⁻¹
  obtain ⟨W, hW, hWg⟩ := exists_alg (p := l) (AIP l).actT (eventually_actT_eq (AIP l))
    ((Units.coeHom _).comp f) (Units.continuous_val.comp hf)
    (fun g hg => congrArg Units.val (hfI g ((hI g).2 (norm_sub_lt_one_of_fix (AIP l) g hg))))
  refine ⟨(AIP l).ιA.mapMatrix W, (AIP l).ιA.mapMatrix W⁻¹, ?_, fun i j => (AIP l).ainf_image_mem_filtration_zero _ _,
    fun i j => (AIP l).ainf_image_mem_filtration_zero _ _, ?_, fun g hg => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have h := hWg σ (frobenius _ l) fun m hm y hy => ((UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).1 σ hσ).symm
    have h1 : W.map (WittVector.map (frobenius _ l)) = (zlW l (OCb l)).mapMatrix u * W := by
      conv_rhs => rw [← h, ← Matrix.mul_assoc]
      have e : (((Units.coeHom _).comp f) σ).map (zlW l (OCb l)) = (zlW l (OCb l)).mapMatrix (↑u⁻¹) := by
        rw [← hfσ]; rfl
      rw [e, ← map_mul, Units.mul_inv, map_one, Matrix.one_mul]
    have h2 := congrArg (AIP l).ιA.mapMatrix h1
    rw [map_mul] at h2
    convert h2 using 1
    · ext i j
      change (PP l).φB ((AIP l).ιA (W i j)) = (AIP l).ιA (WittVector.map (frobenius _ l) (W i j))
      rw [← (AIP l).ιA_φ, WittVector.frobenius_eq_map_frobenius]
    · congr 1
      ext i j
      exact (ιA_zlW (AIP l) Ti _).symm
  · have h := hWg 1 ((AIP l).actT g).toRingHom fun m hm y hy => by
      rw [map_one, RingAut.one_apply]
      exact (UpperTheory.tilt_frobenius_action_pow_and_inertia_trivial_of_pow_eq_self y m hm hy).2 g hg
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul] at h
    ext i j
    change (PP l).actQ g ((AIP l).ιA (W i j)) = (AIP l).ιA (W i j)
    rw [← (AIP l).ιA_act]
    exact congrArg (AIP l).ιA (congrFun (congrFun h i) j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCocycleExtensionOfConjugationInvariantRest
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem zm_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * (g * q.out) ∈ H := by
  rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rfl

private noncomputable def zm_h {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) : H :=
  ⟨(g • q).out⁻¹ * (g * q.out), zm_mem H g q⟩

private theorem zm_h_mul {G : Type} [Group G] (H : Subgroup G) (g g' : G) (q : G ⧸ H) :
    zm_h H (g * g') q = zm_h H g (g' • q) * zm_h H g' q := by
  apply Subtype.ext
  simp only [zm_h, Subgroup.coe_mul, mul_smul]
  group

private theorem zm_out {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out * (zm_h H g q : G) = g * q.out := by
  simp only [zm_h]
  group

private theorem zm_fix {G : Type} [Group G] (H : Subgroup G) [hN : H.Normal] (h : H) (q : G ⧸ H) :
    (h : G) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm, QuotientGroup.eq]
    have := hN.conj_mem _ h.2 x⁻¹
    simpa [mul_assoc] using this

private theorem zm_sum {G : Type} [Group G] (H : Subgroup G) [Fintype (G ⧸ H)] {V : Type} [AddCommGroup V]
    (g : G) (f : G ⧸ H → V) : ∑ q, f (g • q) = ∑ q, f q :=
  Equiv.sum_comp (MulAction.toPerm g) f

private theorem zm_cont {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (q : G ⧸ H) : Continuous fun g : G => (g • q).out := by
  haveI : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  have h1 : Continuous fun g : G => g • q := by fun_prop
  exact (continuous_of_discreteTopology (f := fun x : G ⧸ H => x.out)).comp h1

theorem UpperTheory.exists_cocycle_extension_of_conjugation_invariant_restriction :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → ∀ (N : Submodule A (H → V)), ∀ c ∈ Z1 (ρ.comp H.subtype : Representation A H V), (∀ (s : G) (c' : H → V), (∀ g g' : H, (g' : G) = s⁻¹ * g * s → c' g = ρ s (c g')) → c' - c ∈ N) → ∃ b ∈ Z1 ρ, (fun g : H => b g) - c ∈ N := by
  intro l _ G _ _ _ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ H hHN _ hH N c hc hs
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set n : ℕ := Fintype.card (G ⧸ H) with hn
  have hn0 : (n : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  obtain ⟨a, ha⟩ : ∃ a : A, ∀ x : V, a • (n • x) = x :=
    ⟨algebraMap ℚ_[l] A (n : ℚ_[l])⁻¹, fun x => by
      rw [algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, inv_mul_cancel₀ hn0, one_smul]⟩
  have hmul : ∀ g g' x, ρ g (ρ g' x) = ρ (g * g') x := fun g g' x => by
    rw [map_mul, Module.End.mul_apply]
  rw [mem_Z1_iff_cocycle] at hc
  have hc2 : ∀ h h' : H, c (h * h') = c h + ρ h (c h') := hc.2
  let cor : G → V := fun g => ∑ q : G ⧸ H, ρ (g • q).out (c (zm_h H g q))
  have hcor : cor ∈ Z1 ρ := by
    refine ⟨continuous_finsetSum _ fun q _ => ?_, fun g g' => ?_⟩
    · have h1 := zm_cont H hH q
      have h2 : Continuous fun g : G => zm_h H g q :=
        Continuous.subtype_mk (h1.inv.mul (continuous_id.mul continuous_const)) _
      exact hρ.comp (h1.prodMk (hc.1.comp h2))
    · simp only [cor]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← zm_sum H g' (fun q => ρ (g • q).out (c (zm_h H g q))), map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [zm_h_mul, hc2, map_add (f := _), hmul, hmul, mul_smul, zm_out]
  let c' : G ⧸ H → H → V := fun q h => ρ q.out (c (zm_h H h q))
  have hc' : ∀ q, c' q - c ∈ N := fun q => hs q.out (c' q) fun g g' hg => by
    have : zm_h H g q = g' := by
      apply Subtype.ext
      simp only [zm_h, zm_fix, hg, mul_assoc]
    simp only [c', this]
  refine ⟨a • cor, (Z1 ρ).smul_mem a hcor, ?_⟩
  have e : (fun g : H => (a • cor) g) - c = a • ∑ q : G ⧸ H, (c' q - c) := by
    funext h
    have e1 : cor h = ∑ q : G ⧸ H, c' q h := by
      simp only [cor, c', zm_fix]
    simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, e1, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, ← hn, smul_sub, ha]
  rw [e]
  exact N.smul_mem a (N.sum_mem fun q _ => hc' q)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsLiftFactorCompactSubalgebra
section
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem continuous_linear_functional_comp {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℚ_[l] V]
    (φ : V →ₗ[ℚ_[l]] ℚ_[l]) (f : X → V) (hf : QCont l f) : Continuous fun x => φ (f x) := by
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  exact (IsModuleTopology.continuous_of_linearMap φ).comp hf

private theorem continuous_bounded_lattice {l : ℕ} [Fact l.Prime] {X V : Type} [TopologicalSpace X] [CompactSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module.Finite ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    (f : X → V) (hf : QCont l f) : ∃ M : Submodule ℤ_[l] V, M.FG ∧ ∀ g, f g ∈ M := by
  let e := Module.finBasis ℚ_[l] V
  have h1 : Continuous fun g => fun i => e.coord i (f g) := continuous_pi fun i => continuous_linear_functional_comp _ f hf
  obtain ⟨C, hC⟩ := (isCompact_range h1).isBounded.exists_norm_le
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  refine ⟨Submodule.span ℤ_[l] (Set.range fun i => c • e i), Submodule.fg_span (Set.finite_range _), fun g => ?_⟩
  rw [← e.sum_repr (f g)]
  refine sum_mem fun i _ => ?_
  have h2 : ‖e.repr (f g) i / c‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 hc0)]
    exact ((norm_le_pi_norm (fun i => e.coord i (f g)) i).trans (hC _ ⟨g, rfl⟩)).trans hc
  let z : ℤ_[l] := ⟨_, h2⟩
  have h3 : e.repr (f g) i • e i = z • c • e i := by
    rw [← algebraMap_smul ℚ_[l] z, smul_smul]
    congr 1
    exact (div_mul_cancel₀ _ hc0).symm
  rw [h3]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem eventually_congruent_mod_l_pow {l : ℕ} [Fact l.Prime] {X V M : Type} [TopologicalSpace X] [AddCommGroup V]
    [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [AddCommGroup M] [Module ℤ_[l] M]
    [Module.Finite ℤ_[l] M] (j : M →ₗ[ℤ_[l]] V) (hj : Function.Injective j)
    (f : X → M) (hf : QCont l fun g => j (f g)) (N : ℕ) (g₀ : X) :
    ∀ᶠ g in nhds g₀, ∃ m : M, f g - f g₀ = (l : ℤ_[l]) ^ N • m := by
  haveI : Module.IsTorsionFree ℤ_[l] V := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] V
  haveI : Module.IsTorsionFree ℤ_[l] M := Function.Injective.moduleIsTorsionFree j hj (map_smul j)
  let b := Module.finBasis ℤ_[l] M
  have h1 : LinearIndependent ℚ_[l] (j ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 (b.linearIndependent.map' j (LinearMap.ker_eq_bot.2 hj))
  obtain ⟨ψ, hψ⟩ := (Finsupp.linearCombination ℚ_[l] (j ∘ b)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 h1)
  have h2 : ∀ m i, ψ (j m) i = (b.repr m i : ℚ_[l]) := by
    intro m i
    have h3 : j m = Finsupp.linearCombination ℚ_[l] (j ∘ b)
        ((Finsupp.linearEquivFunOnFinite ℚ_[l] ℚ_[l] _).symm fun i => algebraMap ℤ_[l] ℚ_[l] (b.repr m i)) := by
      rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply, Fintype.linearCombination_apply]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← b.sum_repr m, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, algebraMap_smul]
      rfl
    rw [h3, ← LinearMap.comp_apply, hψ]
    rfl
  have h4 : ∀ i, ∀ᶠ g in nhds g₀, ‖b.repr (f g - f g₀) i‖ ≤ (l : ℝ) ^ (-N : ℤ) := by
    intro i
    have h5 : Continuous fun g => ψ (j (f g)) i := continuous_linear_functional_comp ((Finsupp.lapply i).comp ψ) _ hf
    have hp : (0 : ℝ) < (l : ℝ) ^ (-N : ℤ) := zpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos) _
    filter_upwards [Metric.tendsto_nhds.1 (h5.tendsto g₀) _ hp] with g hg
    rw [dist_eq_norm, h2, h2] at hg
    rw [map_sub, Finsupp.sub_apply]
    exact hg.le
  filter_upwards [Filter.eventually_all.2 h4] with g hg
  choose c hc using fun i => Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ N).1 (hg i))
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← b.sum_repr (f g - f g₀), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul]

private theorem isIntegral_of_nilpotent_kernel {O B E : Type} [CommRing O] [CommRing B] [CommRing E] [Algebra O B] [Algebra O E]
    (π : B →ₐ[O] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : B) (ha : IsIntegral O (π a)) : IsIntegral O a := by
  obtain ⟨p, hp, hpe⟩ := ha
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at hpe
  obtain ⟨n, hn⟩ := hπ _ hpe
  exact ⟨p ^ n, hp.pow n, by rw [← Polynomial.aeval_def, map_pow, hn]⟩

private theorem isUnit_of_nilpotent_kernel {O C A : Type} [CommRing O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A]
    [Algebra.IsIntegral O A] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) (a : C) (ha : IsUnit (π a)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨p, hp, hpe⟩ := Algebra.IsIntegral.isIntegral (R := O) ((u⁻¹ : Aˣ) : A)
  letI : Invertible ((u⁻¹ : Aˣ) : A) := Units.invertible _
  have h1 := (Polynomial.eval₂_reverse_eq_zero_iff (algebraMap O A) ((u⁻¹ : Aˣ) : A) p).2 hpe
  rw [invOf_units, inv_inv, hu, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply] at h1
  have h4 : p.reverse = Polynomial.X * p.reverse.divX + Polynomial.C 1 := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add p.reverse]
    rw [Polynomial.coeff_zero_reverse, hp.leadingCoeff]
  have h5 := (hπ _ h1).isUnit_sub_one
  rw [h4, map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one, add_sub_cancel_right] at h5
  exact isUnit_of_mul_isUnit_left h5

private theorem complete_of_nilpotent_kernel_finite {O C A : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing C] [CommRing A] [Algebra O C] [Algebra O A] [IsCO O A]
    [Algebra.IsIntegral O A] [Module.Finite O C] (π : C →ₐ[O] A) (hπ : ∀ a, π a = 0 → IsNilpotent a) : IsCO O C := by
  haveI : Nontrivial C := π.toRingHom.domain_nontrivial
  haveI : IsLocalRing C := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (π a) with h | h
    · exact Or.inl (isUnit_of_nilpotent_kernel π hπ a h)
    · exact Or.inr (isUnit_of_nilpotent_kernel π hπ _ (by rwa [map_sub, map_one]))
  refine co_finite O O C fun x => ?_
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (π x)
  refine ⟨a, fun h => ha ?_⟩
  have := h.map π
  rwa [map_sub, AlgHom.commutes] at this

theorem UpperTheory.V.Loc.exists_lift_factor_compact_subalgebra :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (x : R →ₐ[O] E) (r : Γ →* Matrix ι ι B), (∀ g a b, π (r g a b) = x (ρ.hom g a b)) → (∀ a b, QCont l fun g => r g a b) → ∃ (C : Subalgebra O B) (_ : IsCO O ↥C) (ρ' : Lift O rbar ↥C), ∀ g a b, (ρ'.hom g a b : B) = r g a b := by
  intro l _ O _ _ _ _ _ _ _ Γ ι _ _ _ _ _ _ rbar R _ _ _ ρ E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ x r hr hc
  classical
  have hint : ∀ a, IsIntegral O (x a) := fun a =>
    (((ptCont (l := l) R E x).2 (Field.toIsField E)).1 a).tower_top
  let πO : B →ₐ[O] E := π.restrictScalars O
  let S : Set B := Set.range fun s : Γ × ι × ι => r s.1 s.2.1 s.2.2
  let C : Subalgebra O B := Algebra.adjoin O S
  have hSC : ∀ g a b, r g a b ∈ C := fun g a b => Algebra.subset_adjoin ⟨(g, a, b), rfl⟩
  have hCx : ∀ c ∈ C, πO c ∈ x.range := fun c hc =>
    (Algebra.adjoin_le (S := x.range.comap πO) (by
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact ⟨ρ.hom g a b, (hr g a b).symm⟩)) hc
  haveI hfin : Module.Finite O C := by
    choose M hM hMr using fun p : ι × ι => continuous_bounded_lattice _ (hc p.1 p.2)
    have h1 : (Submodule.span ℤ_[l] S).FG := by
      refine Submodule.FG.of_le (Submodule.fg_iSup M hM) (Submodule.span_le.2 ?_)
      rintro _ ⟨⟨g, a, b⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem (a, b) (hMr (a, b) g)
    obtain ⟨T, hT⟩ := h1
    have h2 : Submodule.span O (T : Set B) = Submodule.span O S := by
      rw [← Submodule.span_span_of_tower ℤ_[l] O (T : Set B), hT, Submodule.span_span_of_tower]
    have h3 : C = Algebra.adjoin O (T : Set B) := by
      rw [← Algebra.adjoin_span (R := O) (s := (T : Set B)), h2, Algebra.adjoin_span]
    have h4 : ∀ t ∈ (T : Set B), IsIntegral O t := fun t ht => by
      obtain ⟨y, hy⟩ := hCx t (h3 ▸ Algebra.subset_adjoin ht)
      exact isIntegral_of_nilpotent_kernel πO hπ t (hy ▸ hint y)
    rw [h3]
    exact Algebra.finite_adjoin_of_finite_of_isIntegral T.finite_toSet h4
  haveI : IsCO O x.range := co_quot O R _ x.rangeRestrict x.rangeRestrict_surjective
  haveI : Algebra.IsIntegral O x.range := ⟨fun z => by
    obtain ⟨a, rfl⟩ := x.rangeRestrict_surjective z
    exact (isIntegral_algHom_iff x.range.val Subtype.val_injective).1 (hint a)⟩
  let p : C →ₐ[O] x.range := (πO.comp C.val).codRestrict _ fun c => hCx c c.2
  haveI hCO : IsCO O C := complete_of_nilpotent_kernel_finite p fun a ha => by
    obtain ⟨n, hn⟩ := hπ a (congrArg Subtype.val ha)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  let r' : Γ →* Matrix ι ι C :=
    { toFun := fun g => Matrix.of fun a b => ⟨r g a b, hSC g a b⟩
      map_one' := by
        ext a b
        simp [Matrix.one_apply, apply_ite Subtype.val]
      map_mul' := fun g h => by
        ext a b
        simp [Matrix.mul_apply] }
  refine ⟨C, hCO, ⟨r', fun a b N => ?_, fun g a b => ?_⟩, fun g a b => rfl⟩
  · letI : Algebra ℤ_[l] C := ((algebraMap O C).comp (algebraMap ℤ_[l] O)).toAlgebra
    haveI : IsScalarTower ℤ_[l] O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : Module.Finite ℤ_[l] C := Module.Finite.trans O C
    have hl : algebraMap ℤ_[l] C l ∈ maximalIdeal C := by
      haveI := (dvrFacts l O).2.2.1
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O C]
      refine map_nonunit _ _ (map_nonunit _ _ ?_)
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.subset_span rfl
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun g₀ => ?_
    filter_upwards [eventually_congruent_mod_l_pow (l := l) (C.val.toLinearMap.restrictScalars ℤ_[l]) Subtype.val_injective
      (fun g => r' g a b) (hc a b) N g₀] with g hg
    obtain ⟨m, hm⟩ := hg
    refine Ideal.Quotient.eq.2 ?_
    rw [hm, Algebra.smul_def, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl N)
  · rw [← res_map p _, ← ρ.red, ← res_map x.rangeRestrict _]
    congr 1
    exact Subtype.ext (hr g a b)
end

