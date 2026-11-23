module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacter
section
noncomputable section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.MemN

theorem nonempty_places_closure (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] :
    Nonempty (Formalism.GaloisCohomology.Places E Ω) :=
  ⟨⟨fun v => (exists_valuationSubring_over (Ω := Ω) v).choose,
    fun v => (exists_valuationSubring_over (Ω := Ω) v).choose_spec⟩⟩

def emptyLayer (B : Base) (C : Cols B) (W : RowsRest B C) (χ : Chi B.toPre)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E (AlgebraicClosure B.host.E) p)
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ)) :
    NData B.R B.host W.what₂ where
  Om := AlgebraicClosure B.host.E
  plOm := (nonempty_places_closure B.host.E (AlgebraicClosure B.host.E)).some
  ldat := ldat
  sha_eq := h
  Loc := Empty
  l := fun i => i.elim
  lPrime := fun i => i.elim
  j := fun i => i.elim
  j_range := fun i => i.elim
  mu := fun i => i.elim
  w := fun i => i.elim
  w_l := fun i => i.elim
  mu_w := fun i => i.elim
  w_tw := fun i => i.elim
  locs := fun _ _ => ∅
  locs_mem := fun _ _ i => i.elim
  O := fun i => i.elim
  instO := fun i => i.elim
  domO := fun i => i.elim
  dvrO := fun i => i.elim
  algO := fun i => i.elim
  finO := fun i => i.elim
  topO := fun i => i.elim
  trO := fun i => i.elim
  O_adic := fun i => i.elim
  O_complete := fun i => i.elim
  embK := fun i => i.elim
  embK_w := fun i => i.elim
  X := fun i => i.elim
  finX := fun i => i.elim
  neX := fun i => i.elim
  T := fun i => i.elim
  T_local := fun i => i.elim
  T_sep := fun i => i.elim
  Mt := fun i => i.elim
  acgMt := fun i => i.elim
  modMt := fun i => i.elim
  freeMt := fun i => i.elim
  finMt := fun i => i.elim
  act := fun i => i.elim
  act_inj := fun i => i.elim
  prMt := fun i => i.elim
  prMt_span := fun i => i.elim
  prMt_lat := fun i => i.elim
  eig_ne := fun i => i.elim
  chi := fun i => i.elim
  chi_cont := fun i => i.elim
  chi_def := fun i => i.elim
  Z := fun i => i.elim
  Zgood := fun i => i.elim
  s0 := fun i => i.elim
  restNLevelExponent_of_odd := fun i => i.elim
  restNLevelExponent_of_two := fun i => i.elim
  S := fun i => i.elim
  Q := fun i => i.elim
  SQ_split := fun i => i.elim
  SQ_disj := fun i => i.elim
  SQ_l := fun i => i.elim
  S_def := fun i => i.elim
  hT := fun i => i.elim
  T_gen := fun i => i.elim
  gam0 := fun i => i.elim
  locNd_chebotarevPlace_mem := fun i => i.elim
  restN_tameGenerator_generates := fun i => i.elim
  chi_ram_Q := fun i => i.elim
  Bj := fun i => i.elim
  acgBj := fun i => i.elim
  modBj := fun i => i.elim
  freeBj := fun i => i.elim
  finBj := fun i => i.elim
  g_split := fun k =>
    (GlobalTheory.HostSplit.split_of_one_mod B.R B.host _ (B.host.g_prime k) (B.toPre.g_cond k)).1
  PlG := fun _ => Fin B.R.f
  card_PlG := fun _ => Fintype.card_fin _
  lab := fun _ _ _ => (Polynomial.X - 1) ^ B.R.r
  lab_monic := fun k _ _ => by
    haveI : Fact (B.host.g k).Prime := ⟨B.host.g_prime k⟩
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod (B.host.g k))) = Polynomial.X - Polynomial.C 1 := by simp
    rw [h1]
    exact ⟨(Polynomial.monic_X_sub_C _).pow _, by
      rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]⟩
  chiT := χ
  restN_card_levelGroup_eq := rfl

end GlobalTheory.MemN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

private theorem eq_spMap_of_specializes {X : Scheme.{0}} {K : Type} [Field K] (g : Sp K ⟶ X) {z : X}
    (h : g (IsLocalRing.closedPoint K) ⤳ z) :
    g = spMap (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) g).hom ≫
      X.fromSpecStalk z := by
  conv_lhs => rw [← spMap_stalkClosedPointTo g]
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  show Spec.map _ ≫ _ = Spec.map _ ≫ _
  simp only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]

private theorem spMap_comp_spMap_divisor {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_isHom_of_generic (M : RatModel F Ω) (M' : RatModel F Ω') (f : M'.Z ⟶ M.Z) (hs : f ≫ M.s = M'.s)
    (hg : f (genericPoint M'.Z) = genericPoint M.Z) : ∃ φ : Ω →ₐ[F] Ω', M.IsHom M' φ f := by
  classical
  have hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z := by
    have h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω')) := rfl
    rw [h1]
    exact (congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg
  have hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z := by rw [hp0]
  have hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z) :=
    eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))
  have hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z)) := by
    intro x
    have hx : x ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← RatModel.coe_stalkEquiv, ha]
  let E := RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩
  let α := (M.Z.presheaf.stalkSpecializes hp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom
  let φ₀ : Ω →+* Ω' := α.comp E.symm.toRingHom
  have key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α := by
    ext a
    show α (E.symm (E a)) = α a
    rw [E.symm_apply_apply]
  have hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt := by
    rw [eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]
  have hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω') := by
    rw [spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]
  have hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω' := by
    have h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω') :=
      Spec.map_injective hc
    ext a
    exact congrArg (fun g => g.hom a) h2
  exact ⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩

theorem apply_eq_of_isHom_id {M : RatModel F Ω} {χ : Ω →ₐ[F] Ω} (h : M.IsHom M χ (𝟙 M.Z)) (x : Ω) : χ x = x := by
  have hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z := by
    exact M.pt_apply _
  have hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω))) := by
    rw [hpt, M.O_genericPoint]; exact Algebra.mem_top
  have h2 := h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx
  rw [Category.comp_id, RatModel.val_pt, RatModel.val_pt] at h2
  exact h2.symm

theorem iso_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom (genericPoint X) = genericPoint Y := by
  exact genericPoint_eq_of_isOpenImmersion e.hom

private theorem mat_map_mul_inv {ι : Type} {m : ι → ℕ} {K K' : Type} [Field K] [Field K'] (σ : K →+* K')
    (X Y : Mat m K) : (X * Y⁻¹).map σ = X.map σ * (Y.map σ)⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv]

theorem exists_refines_of_iso {ι : Type} {m k : ι → ℕ} (M : RatModel F Ω) (M' : RatModel F Ω') (e : M'.Z ≅ M.Z)
    (hs : e.hom ≫ M.s = M'.s) (S : Fr M m k) :
    ∃ (φ : Ω →ₐ[F] Ω') (S' : Fr M' m k), Refines S S' φ e.hom := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)
  have hs' : e.inv ≫ M'.s = M.s := by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨ψ, hψ⟩ := exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)
  have hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z) := by
    have h1 := hφ.comp hψ
    rwa [e.inv_hom_id] at h1
  have hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z) := by
    have h1 := hψ.comp hφ
    rwa [e.hom_inv_id] at h1
  have hψφ : ∀ x, ψ (φ x) = x := fun x => apply_eq_of_isHom_id hid x
  have hφψ : ∀ x, φ (ψ x) = x := fun x => apply_eq_of_isHom_id hid' x
  have pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z' := fun z' => by simp
  have memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z' := fun hx => hφ.map_mem_O hx
  have memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z') := by
    intro z' x hx
    apply hψ.map_mem_O
    rwa [pt2]
  have mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hψφ]
  have mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hφψ]
  have I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ := by
    intro B A
    have h1 := mat_map_mul_inv ψ.toRingHom B (A.map φ)
    have h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹ := h1
    rw [h2, mm1]
  have I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹ := by
    intro B A
    have h1 := mat_map_mul_inv φ.toRingHom (B.map ψ) A
    have h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹ := h1
    rw [h2, mm2]
  have hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0 := by
    intro A hA τ
    have h1 : ((A.map φ) τ).det = φ (A τ).det := Mat.det_map A φ.toRingHom τ
    rw [h1]
    exact (map_ne_zero φ).2 (hA τ)
  let S' : Fr M' m k :=
    { S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')}
      loc := by
        intro z'
        obtain ⟨U, A, hzU, hA, hU⟩ := S.loc (e.hom z')
        refine ⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩
        show A''.map ψ ∈ S.S (e.hom z'') ↔ _
        rw [hU (e.hom z'') hz'' (A''.map ψ), I1]
        constructor
        · intro h
          have h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ) :=
            h.map φ.toRingHom (fun x hx => memφ hx)
          rwa [mm2] at h1
        · intro h
          exact h.map ψ.toRingHom (fun x hx => memψ hx) }
  refine ⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩
  · intro z' A' hA' A hA
    have h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹) :=
      (Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')
    have h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ) :=
      h1.map φ.toRingHom (fun x hx => memφ hx)
    rwa [I2] at h2
  · unfold KeepsRad Rad
    intro z' g hg
    obtain ⟨hg0, hgO, hgr⟩ := hg
    refine ⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩
    have hx' : ψ x ∈ M.O (e.hom z') := memψ hx
    have hxn' : ψ x ^ n / g ∈ M.O (e.hom z') := by
      have h1 := memψ hxn
      rw [map_div₀, map_pow, hψφ] at h1
      exact h1
    have h2 := memφ (hgr (ψ x) n hx' hxn')
    rw [map_div₀, hφψ] at h2
    exact h2
  · intro K _ x A hA h hh
    refine ⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩
    · have hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
        have h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K)) := rfl
        rw [h1]
        simp
      have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := hdet (Fr.det_ne hA)
      have hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1 := by
        funext τ; ext i j
        simp only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact RatModel.val_one _
        · exact RatModel.val_zero _
      have hinv : (1 : Mat m K)⁻¹ = 1 := by
        have h1 := Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)
        rwa [one_mul] at h1
      unfold Bears
      refine ⟨A.map φ, ?_, ?_⟩
      · show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))
        rw [mm1, hx1]
        exact hA
      · rw [Mat.mul_inv hd, hone, hinv, mul_one]
        exact hh
    · rw [← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem exists_var_refines (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (h : Good M d) :
    ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k),
      Y.dim = d ∧ Refines S S' φ f := by
  obtain ⟨hP, hSm, hGI⟩ := h
  haveI : SmoothOfRelativeDimension d M.s := hSm
  haveI : GeometricallyIntegral M.s := hGI
  haveI : GeometricallyConnected M.s := by
    constructor
    intro a b y c fst snd hpb
    have := GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb
    infer_instance
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso M.s d hP
  have hs : e.inv ≫ M.s = (ratOf Y).s := by
    show e.inv ≫ M.s = Y.str
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨φ, S', hS'⟩ := exists_refines_of_iso M (ratOf Y) e.symm hs S
  exact ⟨Y, φ, e.inv, S', hd, hS'⟩

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.CoefInt

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] K]


omit [FiniteDimensional ℚ_[l] K] in
theorem dvd_iff_norm_le {a : integralClosure ℤ_[l] K} (ha : a ≠ 0) (x : integralClosure ℤ_[l] K) :
    a ∣ x ↔ ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((a : K) : PadicAlgCl l)‖ := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (GlobalTheory.mem_integralClosure_padicInt_iff K y).mp y.2
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro h
    have h0 : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : ((a : K) : PadicAlgCl l) ≠ 0 := fun h1 => h0 (Subtype.ext h1)
    have hm : (x : K) / (a : K) ∈ integralClosure ℤ_[l] K := by
      rw [GlobalTheory.mem_integralClosure_padicInt_iff, IntermediateField.coe_div, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_div_cancel₀ _ h0).symm⟩

theorem isAdic_maximalIdeal : IsAdic (maximalIdeal (integralClosure ℤ_[l] K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[l] K)
  have hind : IsInducing (fun x : integralClosure ℤ_[l] K => ((x : K) : PadicAlgCl l)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hlt : ‖((π : K) : PadicAlgCl l)‖ < 1 :=
    (GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).1 hπ.not_isUnit
  have hpos : 0 < ‖((π : K) : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h => hπ.ne_zero (Subtype.ext (Subtype.ext h))
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[l] K),
      x ∈ maximalIdeal (integralClosure ℤ_[l] K) ^ n ↔
        ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((π : K) : PadicAlgCl l)‖ ^ n := fun n x => by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm_le K (pow_ne_zero n hπ.ne_zero)]
    push_cast
    rw [norm_pow]
  have hn : ∀ s : Set (integralClosure ℤ_[l] K), s ∈ 𝓝 (0 : integralClosure ℤ_[l] K) ↔
      ∃ ε > 0, ∀ x : integralClosure ℤ_[l] K, ‖((x : K) : PadicAlgCl l)‖ < ε → x ∈ s := fun s => by
    rw [hind.nhds_eq_comap, ((Metric.nhds_basis_ball).comap _).mem_iff]
    refine exists_congr fun ε => and_congr_right fun _ => ?_
    simp [Set.subset_def]
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds
      (maximalIdeal (integralClosure ℤ_[l] K) ^ n).toAddSubgroup (g := 0) ?_
    exact (hn _).2 ⟨_, pow_pos hpos n, fun x hx => (hmem n x).2 hx.le⟩
  · obtain ⟨ε, hε, h⟩ := (hn s).1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    exact ⟨n, fun x hx => h x (((hmem n x).1 hx).trans_lt hn)⟩

theorem finite_residueField : Finite (ResidueField (integralClosure ℤ_[l] K)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] K
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] K
  have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

theorem integers_laws : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (_ : IsDiscreteValuationRing ↥(Loc.OL LL)), Module.Finite ℤ_[l] ↥(Loc.OL LL) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ↥(Loc.OL LL) ∧ Finite (IsLocalRing.ResidueField ↥(Loc.OL LL)) ∧ IsFractionRing ↥(Loc.OL LL) ↥LL.1 := by
  intro l _ LL
  have := LL.2
  exact ⟨GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l LL.1,
    GlobalTheory.finite_integralClosure_padicInt l LL.1, isAdic_maximalIdeal LL.1,
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] (integralClosure ℤ_[l] LL.1),
    finite_residueField LL.1, GlobalTheory.isFractionRing_integralClosure_padicInt l LL.1⟩

end GlobalTheory.CoefInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
section
namespace GlobalTheory.UnrLoc

theorem fixed_ne_bot_of_mem_iSup_range :
    ∀ {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
      {ι : Type} [Finite ι] {σ : Representation ℂ G V}, σ.IsIrreducible →
      ∀ {ρ : Representation ℂ G X} (T : ι → σ.IntertwiningMap ρ) (K : Subgroup G) {f : X},
      f ∈ ⨆ j, LinearMap.range (T j).toLinearMap → f ≠ 0 → (∀ k ∈ K, ρ k f = f) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
  intro G V X _ _ _ _ _ ι _ σ hσ ρ T K f hf hf0 hfix
  classical
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  haveI : Fintype ι := Fintype.ofFinite ι

  let Y : Finset ι → Submodule ℂ X := fun t => ⨆ j ∈ t, LinearMap.range (T j).toLinearMap
  have hYst : ∀ (t : Finset ι) (g : G) (x : X), x ∈ Y t → ρ g x ∈ Y t := by
    intro t g x hx
    have hle : Y t ≤ (Y t).comap (ρ g) := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_comap]
      have : ρ g ((T j).toLinearMap v) = (T j).toLinearMap (σ g v) := by
        simp only [Representation.IntertwiningMap.toLinearMap_apply,
          Representation.IntertwiningMap.isIntertwining]
      rw [this]
      exact (le_iSup₂ (f := fun j (_ : j ∈ t) => LinearMap.range (T j).toLinearMap) j hj)
        (LinearMap.mem_range_self _ _)
    exact hle hx
  have key : ∀ (t : Finset ι) (x : X), x ∈ Y t → x ≠ 0 → (∀ k ∈ K, ρ k x = x) →
      GlobalTheory.PRep.fixed σ K ≠ ⊥ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro x hx hx0 _
      exact absurd (by simpa [Y] using hx) hx0
    | insert j t hjt ih =>
      intro x hx hx0 hxfix
      have hx' : x ∈ LinearMap.range (T j).toLinearMap ⊔ Y t := by
        simpa [Y, Finset.iSup_insert] using hx
      obtain ⟨y, ⟨v, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      let U : Subrepresentation σ :=
        ⟨(Y t).comap (T j).toLinearMap, fun g w hw => by
          rw [Submodule.mem_comap] at hw ⊢
          have : (T j).toLinearMap (σ g w) = ρ g ((T j).toLinearMap w) := by
            simp only [Representation.IntertwiningMap.toLinearMap_apply,
              Representation.IntertwiningMap.isIntertwining]
          rw [this]
          exact hYst t g _ hw⟩
      rcases eq_bot_or_eq_top U with hU | hU
      · have hU' : (Y t).comap (T j).toLinearMap = ⊥ := congrArg Subrepresentation.toSubmodule hU
        have hvfix : ∀ k ∈ K, σ k v = v := by
          intro k hk
          have hmem : σ k v - v ∈ (Y t).comap (T j).toLinearMap := by
            rw [Submodule.mem_comap, map_sub]
            have h1 := hxfix k hk
            have h2 : (T j).toLinearMap (σ k v) = ρ k ((T j).toLinearMap v) := by
              simp only [Representation.IntertwiningMap.toLinearMap_apply,
                Representation.IntertwiningMap.isIntertwining]
            rw [map_add (f := _)] at h1
            have h3 : (T j).toLinearMap (σ k v) - (T j).toLinearMap v = z - ρ k z := by
              rw [h2, sub_eq_sub_iff_add_eq_add, h1, add_comm]
            rw [h3]
            exact sub_mem hz (hYst t k z hz)
          rw [hU'] at hmem
          exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hmem)
        by_cases hv : v = 0
        · subst hv
          simp only [map_zero, zero_add] at hx0 hxfix hz ⊢
          exact ih z hz hx0 hxfix
        · rw [Submodule.ne_bot_iff]
          refine ⟨v, ?_, hv⟩
          intro h
          simp [hvfix _ h.2]
      · have hv : (T j).toLinearMap v ∈ Y t := by
          have : v ∈ (⊤ : Subrepresentation σ).toSubmodule := Submodule.mem_top
          rw [← hU] at this
          exact this
        exact ih _ (add_mem hv hz) hx0 hxfix
  refine key Finset.univ f ?_ hf0 hfix
  simpa [Y] using hf

end GlobalTheory.UnrLoc
end

