module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixOfSaturated
section
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.StableLattice

theorem exists_matrix_of_saturated {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {n : ℕ} (L : Submodule O (Fin n → O))
    (hL : ∀ (c : O) (v : Fin n → O), c ≠ 0 → c • v ∈ L → v ∈ L) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) O) (P : Matrix (Fin m) (Fin n) O),
      P * B = 1 ∧ ∀ v, v ∈ L ↔ B.mulVec (P.mulVec v) = v := by
  have : Module.IsTorsionFree O ((Fin n → O) ⧸ L) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x hx
    obtain ⟨v, rfl⟩ := L.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hL c v hc hx
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  have hs' : ∀ x, L.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  let p : (Fin n → O) →ₗ[O] L := LinearMap.codRestrict L (LinearMap.id - s ∘ₗ L.mkQ) (by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self])
  have hp : ∀ x : L, p x = x := by
    intro x
    apply Subtype.ext
    have : L.mkQ (x : Fin n → O) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, this, map_zero, sub_zero]
  let e := (Module.finBasis O L).equivFun
  refine ⟨Module.finrank O L, LinearMap.toMatrix' (L.subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ p), ?_, fun v => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hp, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    constructor
    · intro hv
      exact congrArg Subtype.val (hp ⟨v, hv⟩)
    · intro hv
      rw [← hv]
      exact (p v).2

theorem exists_integral_model (O Γ : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Group Γ] [TopologicalSpace Γ] (n a : ℕ)
    (r : Γ →* GL (Fin n) O) (hr : LatticeContinuous r)
    (W : Submodule (FractionRing O) (Fin n → FractionRing O))
    (hW : ∀ g, ∀ v ∈ W, fracRep r g v ∈ W) (ha : Module.finrank (FractionRing O) W = a) :
    ∃ (ρ : Γ →* GL (Fin a) O)
      (k : (Fin a → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O)),
      LatticeContinuous ρ ∧ Function.Injective k ∧ LinearMap.range k = W ∧
        ∀ g v, fracRep r g (k v) = k (fracRep ρ g v) := by
  set φ := algebraMap O (FractionRing O) with hφ
  have hφi : Function.Injective φ := IsFractionRing.injective O (FractionRing O)
  let c : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  have hc : ∀ v, c v = φ ∘ v := fun v => rfl
  let L : Submodule O (Fin n → O) := (W.restrictScalars O).comap c
  have hLm : ∀ v, v ∈ L ↔ φ ∘ v ∈ W := fun v => Iff.rfl
  have hsm : ∀ (x : O) (v : Fin n → O), φ ∘ (x • v) = φ x • (φ ∘ v) := by
    intro x v; funext i; simp
  obtain ⟨m, B, P, hPB, hL⟩ := exists_matrix_of_saturated L (by
    intro x v hx hv
    rw [hLm, hsm] at hv
    rw [hLm]
    exact (W.smul_mem_iff (by simpa using (map_ne_zero_iff φ hφi).2 hx)).1 hv)
  have hfr : ∀ {b : ℕ} (σ : Γ →* GL (Fin b) O) g v, fracRep σ g v =
      (((σ g : GL (Fin b) O) : Matrix (Fin b) (Fin b) O).map φ).mulVec v := fun σ g v => rfl
  have hmv : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) O) (v : Fin q → O),
      φ ∘ A.mulVec v = (A.map φ).mulVec (φ ∘ v) := by
    intro p q A v; funext i; exact RingHom.map_mulVec φ A v i
  have hBL : ∀ u, B.mulVec u ∈ L := by
    intro u
    rw [hL, Matrix.mulVec_mulVec u P B, hPB, Matrix.one_mulVec]
  have hst : ∀ g, B * (P * (r g : Matrix (Fin n) (Fin n) O) * B) =
      (r g : Matrix (Fin n) (Fin n) O) * B := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : (r g : Matrix (Fin n) (Fin n) O).mulVec (B.mulVec (Pi.single j 1)) ∈ L := by
      rw [hLm, hmv, ← hfr]
      exact hW g _ ((hLm _).1 (hBL _))
    have h2 := (hL _).1 h1
    simp only [← Matrix.mulVec_mulVec]
    exact h2
  let k : (Fin m → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O) :=
    (B.map φ).mulVecLin
  have hk : ∀ v, k v = (B.map φ).mulVec v := fun v => rfl
  have hki : Function.Injective k := by
    apply Function.LeftInverse.injective (g := (P.map φ).mulVec)
    intro v
    rw [hk, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero φ) (map_one φ),
      Matrix.one_mulVec]
  have hkr : LinearMap.range k = W := by
    apply le_antisymm
    · rw [Matrix.range_mulVecLin, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := (hLm _).1 (hBL (Pi.single j 1))
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro w hw
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
        (nonZeroDivisors O) (S := FractionRing O) w
      choose v hv using hd
      have hd0 : φ (d : O) ≠ 0 := (map_ne_zero_iff φ hφi).2 (nonZeroDivisors.coe_ne_zero d)
      have hvw : φ ∘ v = φ (d : O) • w := by
        funext i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        rw [hφ, hv i, Algebra.smul_def]
      have hvL : v ∈ L := by rw [hLm, hvw]; exact W.smul_mem _ hw
      rw [← (LinearMap.range k).smul_mem_iff hd0, ← hvw, ← (hL v).1 hvL, hmv]
      exact ⟨_, hk _⟩
  obtain rfl : m = a := by
    rw [← ha, ← hkr, LinearMap.finrank_range_of_inj hki, Module.finrank_fin_fun]
  let ρ₀ : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => P * (r g : Matrix (Fin n) (Fin n) O) * B
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, hPB]
      map_mul' := by
        intro g h
        rw [Matrix.mul_assoc (P * _) B, hst, map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc] }
  refine ⟨ρ₀.toHomUnits, k, ?_, hki, hkr, fun g v => ?_⟩
  · exact (continuous_const.matrix_mul hr).matrix_mul continuous_const
  · rw [hfr, hfr, hk, hk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← Matrix.map_mul, ← hst g]
    rfl

end GlobalTheory.StableLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CocycleKernel

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {rho : Representation R Γ M} (x : Z1 rho) {L : Subgroup Γ}

theorem cocycle_one : x.1 1 = 0 := by
  have h := x.2.2 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem cocycle_conj (hL : ∀ g ∈ L, ∀ m, rho g m = m) (k : Γ) {g : Γ} (hg : g ∈ L) :
    x.1 (k * g * k⁻¹) = rho k (x.1 g) := by
  have h := x.2.2 k k⁻¹
  rw [mul_inv_cancel, cocycle_one] at h
  rw [x.2.2, x.2.2, map_mul, Module.End.mul_apply, hL g hg, add_right_comm, ← h, zero_add]

def zeros (L : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ L ∧ x.1 g = 0}
  one_mem' := ⟨L.one_mem, cocycle_one x⟩
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by rw [x.2.2, ha.2, hb.2, map_zero, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    have h := x.2.2 a⁻¹ a
    rwa [inv_mul_cancel, cocycle_one, ha.2, map_zero, add_zero, eq_comm] at h⟩

theorem zeros_normal (hN : L.Normal) (hL : ∀ g ∈ L, ∀ m, rho g m = m) : (zeros x L).Normal :=
  ⟨fun g hg k => ⟨hN.conj_mem g hg.1 k, by rw [cocycle_conj x hL k hg.1, hg.2, map_zero]⟩⟩

theorem isOpen_zeros [DiscreteTopology M] (hO : IsOpen (L : Set Γ)) : IsOpen (zeros x L : Set Γ) :=
  hO.inter ((isOpen_discrete ({0} : Set M)).preimage x.2.1)

theorem cocycle_eq (hL : ∀ g ∈ L, ∀ m, rho g m = m) {h σ g : Γ} (hh : h ∈ L)
    (hu : g * σ * g⁻¹ * h⁻¹ ∈ zeros x L) : x.1 σ = rho g⁻¹ (x.1 h) := by
  have e : σ = g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ := by group
  rw [e, cocycle_conj x hL _ (L.mul_mem hu.1 hh), x.2.2, hu.2, hL _ hu.1, zero_add]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem dot_repOn {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ)
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (k : GE N) (a b : Fin D.R.r → A) :
    repOn (Tgl i s) κ A k a ⬝ᵥ repOn ρ κ⁻¹ A k b =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) * a ⬝ᵥ b := by
  have e : (Tmat i s k).transpose * Tdual i s k = ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ (X.O0 i)) := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, ← Tgl_coe, ← Matrix.coe_units_inv, Units.inv_mul,
      Matrix.transpose_one]
  have e2 : ((Tmat i s k).map (algebraMap (X.O0 i) A)).transpose * (Tdual i s k).map (algebraMap (X.O0 i) A) =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ A) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, e]
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  change ((κ k : A) • ((Tgl i s k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec a) ⬝ᵥ
    ((((κ k)⁻¹ : Aˣ) : A) • ((ρ k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec b) = _
  rw [hρ k, Tgl_coe, smul_dotProduct, dotProduct_smul, smul_smul, Units.mul_inv, one_smul, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]

theorem exists_open_normal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  intro D N X i s hl M L z hM hS A _ _ _ _ κ ρ hK hρ hκ x y h hh hb
  have h1 : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ ρ hK hρ A g hg).1, hκ g hg, Units.val_one, one_smul]
  have h2 : ∀ g ∈ L, ∀ m, repOn ρ κ⁻¹ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ⁻¹ ρ hK hρ A g hg).2.1, MonoidHom.inv_apply, hκ g hg, inv_one,
      Units.val_one, one_smul]
  obtain ⟨⟨hO, hN, hc, -⟩, -⟩ := hS
  have hc' : ∀ g ∈ L, cConj X g ∈ L := fun g hg => (hc g _ (cConj_apply X g)).1 hg
  haveI := zeros_normal x hN h1
  haveI := zeros_normal y hN h2
  refine ⟨(zeros x L ⊓ (zeros x L).comap (cConj X)) ⊓ (zeros y L ⊓ (zeros y L).comap (cConj X)),
    ((isOpen_zeros x hO).inter (isOpen_comap_cConj X (isOpen_zeros x hO))).inter
      ((isOpen_zeros y hO).inter (isOpen_comap_cConj X (isOpen_zeros y hO))), inferInstance,
    fun g hg => hg.1.1.1, fun g hg a b c d => ⟨⟨⟨hg, a⟩, hc' g hg, b⟩, ⟨hg, c⟩, hc' g hg, d⟩, ?_⟩
  rintro σ g ⟨⟨a, b⟩, c, d⟩ h0
  have e : cConj X (g * σ * g⁻¹ * h⁻¹) = cConj X g * cConj X σ * (cConj X g)⁻¹ * (cConj X h)⁻¹ := by
    simp only [map_mul, map_inv]
  have b' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros x L := b
  have d' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros y L := d
  rw [e] at b' d'
  rw [bform, cocycle_eq x h1 hh a, cocycle_eq y h2 hh c, cocycle_eq x h1 (hc' h hh) b', cocycle_eq y h2 (hc' h hh) d',
    dot_repOn i s κ hρ, dot_repOn i s κ hρ, ← map_inv (cConj X), GlobalTheory.ResConjTriv.auxiliaryCharacter_complexConj_invariant, ← mul_sub] at h0
  exact hb (((Units.isUnit _).map (algebraMap (X.O0 i) A)).mul_right_eq_zero.1 h0)

end GlobalTheory.CocycleKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
section
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.CoeffEmbedding

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem exists_norm_le : ∃ C : ℝ, ∀ b : N.O i, ‖iotaOQ N A i b‖ ≤ C := by

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[N.l i] (N.O i)).FG)
  refine ⟨∑ a ∈ s, ‖iotaOQ N A i a‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hz : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) (c a)) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i]) := A.iotaQ_alg i (c a)
  rw [Algebra.smul_def, map_mul, norm_mul, hz]
  have h1 : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ ≤ 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ = ‖(c a : ℚ_[N.l i])‖ :=
      PadicAlgCl.norm_extends (p := N.l i) _
    rw [he, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  exact mul_le_of_le_one_left (norm_nonneg _) h1


include A in
theorem exists_pow_le_span : ∃ e : ℕ, IsLocalRing.maximalIdeal (N.O i) ^ e ≤
    Ideal.span {((N.l i : ℕ) : N.O i)} := by

  have hl : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h' := congrArg (iotaOQ N A i) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : (N.l i).Prime).ne_zero) h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {((N.l i : ℕ) : N.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨n, ?_⟩
  rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem continuous_iotaOQ : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  intro R H what₂ N A i

  obtain ⟨C, hC⟩ := exists_norm_le N A i
  obtain ⟨e, he⟩ := exists_pow_le_span N A i
  refine continuous_of_continuousAt_zero (iotaOQ N A i) ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set q : ℝ := ‖((N.l i : ℕ) : Qbar (N.l i))‖ with hq
  have hq1 : q < 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i])‖ =
        ‖((N.l i : ℕ) : ℚ_[N.l i])‖ := PadicAlgCl.norm_extends (p := N.l i) _
    rw [map_natCast] at he
    rw [hq, he]
    exact Padic.norm_p_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC1) hq1
  obtain ⟨hopen, -⟩ := isAdic_iff.mp (N.O_adic i)
  filter_upwards [(hopen (e * k)).mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {((N.l i : ℕ) : N.O i) ^ k} := by
    rw [← Ideal.span_singleton_pow, pow_mul] at *
    exact Ideal.pow_right_mono he k hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow, ← hq]
  calc ‖iotaOQ N A i b‖ * q ^ k ≤ (|C| + 1) * q ^ k :=
        mul_le_mul_of_nonneg_right ((hC b).trans (by linarith [le_abs_self C])) (pow_nonneg hq0 k)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hk hC1
    _ = ε := by field_simp

end GlobalTheory.CoeffEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiOperatorEtalePhiGammaModuleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_psi_operator_etale_phiGamma_module : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), ∃ ψ : W.DD T →ₗ[↥(OL LL)] W.DD T, (∀ x, ψ (W.φD T x) = x) ∧ (∀ (a : W.EE) x, ψ (W.φE a • x) = a • ψ x) ∧ ∀ g x, ψ (W.γD T g x) = W.γD T g (ψ x) := by
  first | exact @GlobalTheory.psiD_exists | exact GlobalTheory.psiD_exists | (intros; apply GlobalTheory.psiD_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueTiltInjectiveRetractStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residueTilt_injective_retract : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (ek : (Fq l bk.a)⟦X⟧ →+* OCb l) (pr : OCb l →+ (Fq l bk.a)⟦X⟧), (∀ s : bk.S, ek (PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s) = (bk.ev s).coeff 0) ∧ Function.Injective ek ∧ (∀ a y, pr (ek a * y) = a * pr y) ∧ pr 1 = 1 := by
  first | exact @GlobalTheory.BSP.exists_resTilt_retract | exact GlobalTheory.BSP.exists_resTilt_retract | (intros; apply GlobalTheory.BSP.exists_resTilt_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThreePrimesOneModLeRpow
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems (TwDatum Twisted SameBelow SamePair LiesUnder TwistedPlaceSettings namedPrimes expDat GoodDatum GoodSystem
  recorded ExistsChoice WithToricIntegralityConstant FamTwGood TwGoodClosed)

namespace GlobalTheory.TwistGoodCompare

variable {D : D7}

def AtPlace (t : D.what₂.places.Pl → TwDatum D) : Prop :=
  ∀ w, Twisted D w → LiesUnder D (t w).1 w ∨ LiesUnder D (t w).1 (D.what₂.places.conj w)

theorem isUnit_of_toOe (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w))
    (h : IsUnit (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
      (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w))
        (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)))) : IsUnit y := by
  haveI := c.Oe_loc w
  have h1 := (isUnit_map_iff _ _).1 h
  clear h
  generalize c.k' w = k at h1
  generalize c.twI w = i at y k h1
  haveI := D.ntw.Ok_fin i k
  haveI : FaithfulSMul (D.ntw.O i) (D.ntw.Ok i k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (D.ntw.Ok_inj i _)
  have h2 := (isUnit_map_iff (algebraMap (D.ntw.O i) (D.ntw.Ok i k)) _).1 h1
  by_contra hy
  have hl : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))) h0
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 i), map_eq_zero] at this
    exact (D.ntw.lPrime i).out.ne_zero (by exact_mod_cast this)
  have hP : ((IsLocalRing.maximalIdeal (D.ntw.O i)).comap (algebraMap (D.ntw.O0 i) (D.ntw.O i))).IsMaximal := by
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => hl ?_
    rw [← Ideal.mem_bot, ← h0, Ideal.mem_comap, map_natCast]
    exact D.ntw.O_l i
  have hm : y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := hy
  rw [← IsLocalRing.eq_maximalIdeal hP, Ideal.mem_comap] at hm
  exact hm h2

theorem pos_iff_not_isUnit (c : NChoice D) (w : D.what₂.places.Pl) (x : D.what₂.LL) (z : c.Oe w)
    (h : c.embW w x = algebraMap (c.Oe w) (FractionRing (c.Oe w)) z) :
    0 < D.what₂.places.val w x ↔ ¬ IsUnit z := by
  rcases eq_or_ne x 0 with rfl | h0
  · have : z = 0 := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (by rw [← h, map_zero, map_zero])
    simp [this]
  have hx : 0 ≤ D.what₂.places.val w x := (c.embW_w w x).2 ⟨z, h.symm⟩
  have hmul := (D.what₂.places.val w).map_mul x x⁻¹
  rw [mul_inv_cancel₀ h0, AddValuation.map_one] at hmul
  have e1 : 0 < D.what₂.places.val w x ↔ ¬ 0 ≤ D.what₂.places.val w x⁻¹ := by
    rw [D.val_eq w x h0, D.val_eq w _ (inv_ne_zero h0)] at *
    norm_cast at *
    omega
  rw [e1, c.embW_w, not_iff_not]
  have hz : c.embW w x ≠ 0 := by simpa using h0
  constructor
  · rintro ⟨u, hu⟩
    refine IsUnit.of_mul_eq_one u (IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) ?_)
    rw [map_mul, hu, ← h, map_one, ← map_mul, mul_inv_cancel₀ h0, map_one]
  · rintro ⟨u, rfl⟩
    refine ⟨((u⁻¹ : (c.Oe w)ˣ) : c.Oe w), ?_⟩
    rw [map_inv₀, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

theorem exists_star (hG : IsGalois ℚ ↥D.LL0) (x : ↥D.LL0) : ∃ x' : ↥D.LL0, (x' : D.what₂.LL) = star (x : D.what₂.LL) := by
  let σ : D.what₂.LL →ₐ[ℚ] D.what₂.LL := (starRingEnd D.what₂.LL).toRatAlgHom
  exact ⟨σ.restrictNormal ↥D.LL0 x, σ.restrictNormal_commutes ↥D.LL0 x⟩

theorem liesUnder_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) (w : D.what₂.places.Pl) :
    LiesUnder D (c.twI w) (if c.sd w then w else D.what₂.places.conj w) := by
  intro x
  have hint : IsIntegral (D.ntw.O0 (c.twI w)) (D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) :=
    (RingOfIntegers.isIntegral_coe x).map_of_comp_eq (Int.castRingHom _) (D.ntw.emb0 (c.twI w))
      (RingHom.ext_int _ _)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hleft : (∃ y' ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (c.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y' = D.ntw.emb0 (c.twI w) (x : ↥D.LL0)) ↔ ¬ IsUnit y := by
    refine ⟨fun ⟨y', h1, h2⟩ => ?_, fun h1 => ⟨y, h1, hy⟩⟩
    rw [← IsFractionRing.injective _ _ (h2.trans hy.symm)]
    exact h1
  have key : ∀ x' : ↥D.LL0, (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) x' =
      D.ntw.emb0 (c.twI w) (x : ↥D.LL0) → (0 < D.what₂.places.val w (x' : D.what₂.LL) ↔ ¬ IsUnit y) := by
    intro x' hx'
    have e := h.embedding_baseField_condition w x' y 1 one_ne_zero (by rw [hx', map_one, mul_one, hy])
    simp only [map_one, mul_one] at e
    rw [pos_iff_not_isUnit c w _ _ e, not_iff_not]
    exact ⟨isUnit_of_toOe c w y, fun hu => ((hu.map _).map _).map _⟩
  rw [hleft]
  cases hs : c.sd w
  · obtain ⟨x', hx'⟩ := exists_star hG (x : ↥D.LL0)
    rw [if_neg (by simp), D.conj_val, ← hx']
    refine (key x' ?_).symm
    rw [hs, if_neg (by simp)]
    exact D.ntw.restX_coefficientEmbedding_conj _ _ _ (by rw [hx', star_star])
  · rw [if_pos rfl]
    exact (key x (by rw [hs, if_pos rfl])).symm

theorem atPlace_of_tie (hG : IsGalois ℚ ↥D.LL0) {c : NChoice D} (h : NChTie D c) : AtPlace (recorded c) := by
  intro w _
  have := liesUnder_of_tie hG h w
  split_ifs at this
  exacts [Or.inl this, Or.inr this]

end GlobalTheory.TwistGoodCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExportAllOfSixInputs
section
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem GlobalTheory.exportAll_of_six_inputs :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E →
      IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.GoodLatticePoints D.nexp →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i :=
  fun D E N0 h2 h3 h5 h7 h10 h11 i hi =>
    GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp (BlochKatoReduction.bk0 D) E N0 h2 h3 h5 h7 h10 h11 i hi
end

