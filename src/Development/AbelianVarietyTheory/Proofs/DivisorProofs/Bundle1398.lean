module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1295
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalQuotientTransitionCocycle
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cocycle_local_quotient_transition : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A)
    (B : ∀ j, Over (𝒰.X j)) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j) (b : ∀ j k, pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k) ⟶ (B k).left),
    (∀ j, Flat (q j).left) → (∀ j, Surjective (q j).left) → (∀ j, QuasiCompact (q j).left) →
    (∀ j k, b j k ≫ (B k).hom = pullback.snd _ _) →
    (∀ (j k : 𝒰.I₀) (T : Scheme.{0}) (y : T ⟶ pullback A.hom (𝒰.f j)) (z : T ⟶ pullback A.hom (𝒰.f k))
        (w : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k)), y ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ →
        w ≫ pullback.fst _ _ = y ≫ (q j).left → w ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ → w ≫ b j k = z ≫ (q k).left) →
    ∀ (j k l : 𝒰.I₀) (T : Scheme.{0}) (x : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f k))
      (y : T ⟶ pullback ((B k).hom ≫ 𝒰.f k) (𝒰.f l)) (z : T ⟶ pullback ((B j).hom ≫ 𝒰.f j) (𝒰.f l)),
      x ≫ b j k = y ≫ pullback.fst _ _ → x ≫ pullback.fst _ _ = z ≫ pullback.fst _ _ → y ≫ b k l = z ≫ b j l := by
  intro S 𝒰 A H _ _ i B q b hfl hsu hqc hb hchar j k l T x y z hxy hxz
  let κ : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ T := pullback.fst _ _
  let α : pullback (x ≫ pullback.fst _ _) (q j).left ⟶ pullback A.hom (𝒰.f j) := pullback.snd _ _
  have hκα : κ ≫ x ≫ pullback.fst _ _ = α ≫ (q j).left := by
    simpa [κ, α, Category.assoc] using pullback.condition (f := x ≫ pullback.fst _ _) (g := (q j).left)
  haveI : Flat κ := by dsimp [κ]; infer_instance
  haveI : Surjective κ := by dsimp [κ]; infer_instance
  haveI : QuasiCompact κ := by dsimp [κ]; infer_instance
  haveI : Epi κ := Flat.epi_of_flat_of_surjective _
  have hqj : (q j).left ≫ (B j).hom = pullback.snd A.hom (𝒰.f j) := by
    simpa using Over.w (q j)
  have ha : (α ≫ pullback.fst _ _) ≫ A.hom = κ ≫ x ≫ pullback.fst _ _ ≫ (B j).hom ≫ 𝒰.f j := by
    simp only [Category.assoc]
    rw [pullback.condition, ← reassoc_of% hqj, ← reassoc_of% hκα]
  have hak : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ x ≫ pullback.snd _ _) ≫ 𝒰.f k := by
    rw [ha]; simp only [Category.assoc, pullback.condition]
  have hyz : y ≫ pullback.snd _ _ = z ≫ pullback.snd _ _ := by
    rw [← cancel_mono (𝒰.f l)]
    simp only [Category.assoc]
    rw [← pullback.condition, ← pullback.condition, ← reassoc_of% hxy, reassoc_of% (hb j k),
      ← pullback.condition, ← reassoc_of% hxz]
  have hal : (α ≫ pullback.fst _ _) ≫ A.hom = (κ ≫ z ≫ pullback.snd _ _) ≫ 𝒰.f l := by
    rw [ha]; simp only [Category.assoc, ← pullback.condition]
    rw [← reassoc_of% hxz]
  have hk1 := pullback.lift_fst _ _ hak
  have hk2 := pullback.lift_snd _ _ hak
  have hl1 := pullback.lift_fst _ _ hal
  have hl2 := pullback.lift_snd _ _ hal
  have h1 := hchar j k _ α (pullback.lift _ _ hak) (κ ≫ x) hk1.symm
    (by rw [Category.assoc]; exact hκα) (by rw [hk2, Category.assoc])
  have h2 := hchar j l _ α (pullback.lift _ _ hal) (κ ≫ z) hl1.symm
    (by rw [Category.assoc, ← hxz]; exact hκα) (by rw [hl2, Category.assoc])
  have h3 := hchar k l _ (pullback.lift _ _ hak) (pullback.lift _ _ hal) (κ ≫ y) (hk1.trans hl1.symm)
    (by rw [Category.assoc, ← hxy, ← Category.assoc]; exact h1)
    (by rw [hl2, Category.assoc, hyz])
  rw [← cancel_epi κ, ← Category.assoc, h3, ← h2, Category.assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingFiniteIdealsOfMaximalIdealPrincipalNilp
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory

theorem localRing_finite_ideals_of_maximalIdeal_principal_nilpotent :
    ∀ (S : Type) [CommRing S] [IsLocalRing S], (IsLocalRing.maximalIdeal S).IsPrincipal →
    IsNilpotent (IsLocalRing.maximalIdeal S) → (Set.univ : Set (Ideal S)).Finite := by
  intro S _ _ hprin hnil
  classical
  obtain ⟨x, hx⟩ := hprin.principal
  obtain ⟨M, hM⟩ := hnil
  set m := IsLocalRing.maximalIdeal S with hm
  have hM' : m ^ M = ⊥ := hM
  have hpow : ∀ n : ℕ, m ^ n = Ideal.span {x ^ n} := by
    intro n
    rw [hx]
    exact Ideal.span_singleton_pow x n
  apply ((Set.finite_Iic M).image fun n => m ^ n).subset
  intro I _
  by_cases hI : I = ⊥
  · exact ⟨M, Set.mem_Iic.mpr le_rfl, by simp only [hM', hI]⟩
  · have hnot : ¬ I ≤ m ^ M := by
      rw [hM']; exact fun h => hI (le_bot_iff.mp h)
    have hex : ∃ k, ¬ I ≤ m ^ k := ⟨M, hnot⟩
    have hk := Nat.find_spec hex
    have hkM : Nat.find hex ≤ M := Nat.find_min' hex hnot
    have hk0 : Nat.find hex ≠ 0 := by
      intro h; apply hk; rw [h, pow_zero]; rw [Ideal.one_eq_top]; exact le_top
    obtain ⟨n, hn⟩ : ∃ n, Nat.find hex = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hIn : I ≤ m ^ n := by
      by_contra h
      exact Nat.find_min hex (show n < Nat.find hex by omega) h
    rw [hn] at hk
    obtain ⟨a, haI, ha⟩ := SetLike.not_le_iff_exists.mp hk
    have ha' : a ∈ m ^ n := hIn haI
    rw [hpow, Ideal.mem_span_singleton'] at ha'
    obtain ⟨y, rfl⟩ := ha'
    have hy : IsUnit y := by
      by_contra hy
      apply ha
      have hym : y ∈ m := (IsLocalRing.mem_maximalIdeal y).mpr hy
      rw [hx, Ideal.mem_span_singleton'] at hym
      obtain ⟨z, rfl⟩ := hym
      rw [hpow, Ideal.mem_span_singleton']
      exact ⟨z, by ring⟩
    refine ⟨n, Set.mem_Iic.mpr (by omega), ?_⟩
    show m ^ n = I
    apply le_antisymm _ hIn
    rw [hpow, Ideal.span_le, Set.singleton_subset_iff]
    have := I.mul_mem_left ((hy.unit⁻¹ : Sˣ) : S) haI
    rwa [← _root_.mul_assoc, IsUnit.val_inv_mul, _root_.one_mul] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaIntegralAtInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.IntegralDetModule

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def bas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    Module.Basis (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Pi.basis fun _ => (Module.finBasis F E).baseChange (AF F)

def big {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    Matrix (Σ _ : Fin n, Fin (Module.finrank F E)) (Σ _ : Fin n, Fin (Module.finrank F E)) (AF F) :=
  LinearMap.toMatrix (bas F E n) (bas F E n) ((Matrix.toLin' t).restrictScalars (AF F))

theorem big_apply {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (x y) :
    big t x y = (bas F E n).repr (t *ᵥ bas F E n y) x := by
  rw [big, LinearMap.toMatrix_apply]
  rfl

theorem det_big {n : ℕ} (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    (big t).det = Algebra.norm (AF F) t.det := by
  rw [big, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']

theorem bas_eq {n : ℕ} (x) :
    bas F E n x = fun i => inclR (F := F) (AF F) ((Pi.single x.1 (Module.finBasis F E x.2) : Fin n → E) i) := by
  rw [bas, Pi.basis_apply]
  funext i
  by_cases h : i = x.1
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, Module.Basis.baseChange_apply]
    rfl
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem map_norm_det {n : ℕ} {K : Type} [CommRing K] (φ : AF F →+* K) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (u : AF F) (hu : φ u = 1) (ht : u • (t - 1) = 0) : φ (Algebra.norm (AF F) t.det) = 1 := by
  rw [← det_big, RingHom.map_det]
  have : φ.mapMatrix (big t) = 1 := by
    ext x y
    have h1 : u • (t *ᵥ bas F E n y) = u • bas F E n y := by
      have h2 : (u • (t - 1)) *ᵥ bas F E n y = 0 := by rw [ht, Matrix.zero_mulVec]
      rwa [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, sub_eq_zero] at h2
    have h3 := congrArg (fun z => φ ((bas F E n).repr z x)) h1
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hu, one_mul, Module.Basis.repr_self] at h3
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, big_apply, h3, Matrix.one_apply, Finsupp.single_apply]
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_one]

theorem exists_bound {n : ℕ} (W : Spc F E n) (hL : W.L.FG) (v : Pl (F := F)) :
    ∃ C : ℝ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, ∀ x, ‖evFin F v ((bas F E n).repr z x)‖ ≤ C := by
  first
  | exact @_root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main
  | (apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoordinateEmbeddingMaps.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoordinateEmbeddingMaps.main ..)

theorem exists_mul_mem {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.IsFullLattice E) (y : Fin n → E) :
    ∃ D : ℤ, D ≠ 0 ∧ D • y ∈ L := by
  exact _root_.GlobalTheory.LatticeIntegerMultipleMembership.exists_int_smul_mem_of_isLattice L hL y

theorem exists_entry_bound {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) :
    ∃ C : ℝ, ∀ t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      (∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) → ∀ x y, ‖evFin F v (big t x y)‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound W hL.fg v
  choose D hD0 hD using fun x : (Σ _ : Fin n, Fin (Module.finrank F E)) =>
    exists_mul_mem W.L hL (Pi.single x.1 (Module.finBasis F E x.2))
  haveI : CharZero (Fv F v) := algebraRat.charZero _
  refine ⟨∑ y, |C| / ‖(D y : Fv F v)‖, fun t ht x y => ?_⟩
  set e := GlobalTheory.EmbChart.atPlace v (1 : Fv F v) with he
  have he1 : evFin F v e = 1 := GlobalTheory.EmbChart.evFin_atPlace v 1
  have hmem : e • (D y • bas F E n y) ∈ GlobalTheory.InertSph.latAt W v := by
    refine AddSubgroup.subset_closure ⟨e, ?_, ?_, _, hD y, ?_⟩
    · intro u hu
      rw [smul_eq_mul, mul_comm, he, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
    · rw [he1]; exact one_mem _
    · rw [bas_eq]
      congr 1
      funext i
      simp only [Pi.smul_apply, map_zsmul]
  have h1 := hC _ (ht _ hmem) x
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, map_smul, map_zsmul, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul,
    map_mul, he1, one_mul, map_zsmul, zsmul_eq_mul, norm_mul, ← big_apply] at h1
  have hpos : 0 < ‖(D y : Fv F v)‖ := norm_pos_iff.2 (Int.cast_ne_zero.2 (hD0 y))
  calc ‖evFin F v (big t x y)‖ ≤ |C| / ‖(D y : Fv F v)‖ := by
        rw [le_div_iff₀ hpos, mul_comm]; exact h1.trans (le_abs_self C)
    _ ≤ _ := Finset.single_le_sum (f := fun y => |C| / ‖(D y : Fv F v)‖)
        (fun y _ => div_nonneg (abs_nonneg _) (norm_nonneg _)) (Finset.mem_univ y)

theorem norm_le_one {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (ht : ∀ z ∈ GlobalTheory.InertSph.latAt W v, t *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    ‖evFin F v (Algebra.norm (AF F) t.det)‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := exists_entry_bound W hL v
  have hk : ∀ k : ℕ, ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t ^ k) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih => intro z hz; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (ht z hz)
  have hb : ∃ B : ℝ, ∀ k : ℕ, ‖evFin F v (Algebra.norm (AF F) t.det)‖ ^ k ≤ B := by
    refine ⟨(Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E))).factorial •
      C ^ Fintype.card (Σ _ : Fin n, Fin (Module.finrank F E)), fun k => ?_⟩
    rw [← norm_pow, ← map_pow, ← map_pow, ← Matrix.det_pow, ← det_big]
    have := Matrix.det_le (abv := (NormedField.toAbsoluteValue (Fv F v))) (A := (big (t ^ k)).map (evFin F v)) (x := C)
      (fun x y => hC _ (hk k) x y)
    have e : evFin F v (big (t ^ k)).det = ((big (t ^ k)).map (evFin F v)).det :=
      RingHom.map_det (evFin F v).toRingHom _
    rw [e]
    exact this
  obtain ⟨B, hB⟩ := hb
  by_contra h
  obtain ⟨k, hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt (not_le.1 h)).eventually_gt_atTop B).exists
  exact absurd (hB k) (not_le.2 hk)

theorem modu_eq_one (a : (AF F)ˣ) (h1 : (a : AF F).1 = 1) (h2 : ∀ v, ‖evFin F v a‖ = 1) :
    (adeleClass F).modu a = 1 := by
  apply NNReal.eq
  change (MeasureTheory.distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ) = _
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h3 : ∀ v : HeightOneSpectrum (𝓞 F), ‖(a : AF F).2 v‖ = 1 := h2
  have h4 : ∀ w : InfinitePlace F, ‖(a : AF F).1 w‖ = 1 := fun w => by
    rw [h1]; exact norm_one
  simp only [h3, h4, one_pow, Finset.prod_const_one, finprod_one, mul_one, NNReal.coe_one]

theorem modu_norm_det {n : ℕ} (W : Spc F E n) (hL : W.L.IsFullLattice E) (v : Pl (F := F)) (t : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (h1 : At (evFin F v) ((t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1))
    (h2 : ∀ z ∈ GlobalTheory.InertSph.latAt W v, (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧
      ((t⁻¹ : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) :
    (adeleClass F).modu (Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  have h0 := h1 (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
  apply modu_eq_one
  · refine map_norm_det (fstA F).toRingHom _ _ ?_ h0
    rw [map_sub, map_one, sub_eq_self]
    rfl
  · intro u
    by_cases hu : u = v
    · subst hu
      have a1 := norm_le_one W hL u _ fun z hz => (h2 z hz).1
      have a2 := norm_le_one W hL u _ fun z hz => (h2 z hz).2
      have a3 : ‖evFin F u (Algebra.norm (AF F) (t : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det)‖ *
          ‖evFin F u (Algebra.norm (AF F) ((t⁻¹ : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))).det)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, map_one, map_one, norm_one]
      refine le_antisymm a1 ?_
      rw [← a3]
      exact mul_le_of_le_one_right (norm_nonneg _) a2
    · have := map_norm_det (evFin F u).toRingHom _ _ (by
        rw [map_sub, map_one, sub_eq_self]
        exact evalV_singleFin_ne hu 1) h0
      exact (congrArg norm this).trans norm_one

end GlobalTheory.IntegralDetModule

theorem GlobalTheory.IntegralDetModule.modu_norm_det_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      (adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) (Matrix.GeneralLinearGroup.det t)) = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v _ _ _ t ht
  exact GlobalTheory.IntegralDetModule.modu_norm_det G.W hT.geo.hW.lat v t ht.1 ht.2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan
section
noncomputable section

namespace GlobalTheory.MajFrameCartan

open scoped TensorProduct Matrix ComplexOrder
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

theorem isCartanInv_transpose {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (h : IsCartan M θ) :
    Formalism.IndefR.Datum.IsCartanInv Mᵀ θ := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : θᴴ * Mᵀ * θ = Mᵀ := by
    have := congrArg Matrix.transpose h2
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.transpose_map] at this
    show θᵀ.map star * Mᵀ * θ = Mᵀ
    rw [Matrix.mul_assoc]
    exact this
  have hMt : (Mᵀ)ᴴ = Mᵀ := by
    ext i j
    have := congrFun (congrFun hM j) i
    simpa [Matrix.conjTranspose_apply] using this
  have hH : (Mᵀ * θ)ᴴ = Mᵀ * θ := by
    rw [Matrix.conjTranspose_mul, hMt]
    calc θᴴ * Mᵀ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = (θᴴ * Mᵀ * θ) * θ := by simp only [Matrix.mul_assoc]
      _ = Mᵀ * θ := by rw [h2']
  refine ⟨h1, h2', Matrix.posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩⟩
  have e : star x ⬝ᵥ ((Mᵀ * θ) *ᵥ x) = (θ *ᵥ x) ⬝ᵥ (M *ᵥ star x) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have him := Matrix.IsHermitian.im_star_dotProduct_mulVec_self (A := Mᵀ * θ) hH x
  refine Complex.pos_iff.mpr ⟨?_, ?_⟩
  · rw [e]; exact h3 x hx
  · simpa using him.symm

theorem exists_majorantFrame_commute : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ X.Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ X.Jᵀ w),
      k ∈ stabArch σ X.Jᵀ w (bc (compInf F E w) a) →
        Commute ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w))) (X.θ w) := by
  intro F E _ _ _ _ _ σ B n X r s hB hX
  have hcm := hB.cm
  have hM : ∀ w : InfinitePlace F, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hX.herm]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (X.Jᵀ.map (B.emb w).1) (X.θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact isCartanInv_transpose (hM w) (hX.cartan w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k hk => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) X.Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)))ᴴ * X.Jᵀ.map (B.emb w).1 *
        (matHom w.Completion σ X.Jᵀ k).1.map (infEmb (B.emb w)) = X.Jᵀ.map (B.emb w).1 :=
      (archEquiv X.Jᵀ hcm (B.emb w) k).2
    have hbc : (b w).1 * ((b w)⁻¹).1 = 1 := Units.mul_inv _
    have key : ∀ x : GL (Fin n) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 →
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x hx => by
      have hx' : cT (sigR w.Completion σ) x.1 * 1 * x.1 = 1 := hx
      have := congrArg (fun y => y.map (infEmb (B.emb w))) hx'
      simpa only [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
        using this
    rw [mem_stabArch, ha w] at hk
    have hu := key _ hk
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, hc, hc'] at hu
    have := (GlobalTheory.Doubling.unitary_iff_commute hbc (h1 w) (GlobalTheory.Doubling.diagonal_sign_mul_self (ε w)) hK).1 hu
    rwa [h2 w] at this

end GlobalTheory.MajFrameCartan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKUConjOfComp
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def thAt (u : Pl E) : GLw n (cPl E u) →* GLw n u :=
  (MulAut.conj (PhiU n (u.adicCompletion E))).toMonoidHom.comp
    ((invT n (u.adicCompletion E)).comp (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv u)))

theorem thAt_apply (u : Pl E) (h : GLw n (cPl E u)) (i j : Fin n) :
    (thAt u h).val i j =
      (-1) ^ ((i : ℕ) + j) * conjLoc (IsCMField.complexConj E).toRingEquiv u ((h⁻¹).val j.rev i.rev) :=
  GlobalTheory.ThetaPull.phi_mul_apply _ i j

theorem map_thF (u : Pl E) (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    GeneralLinearGroup.map (pLoc E u) (thF E n g) = thAt u (GeneralLinearGroup.map (pLoc E (cPl E u)) g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h := GlobalTheory.ThetaPull.thetaGL_apply (a := n) (conjFin (IsCMField.complexConj E).toRingEquiv) g i j
  change pLoc E u ((thetaGL n (conjFin (IsCMField.complexConj E).toRingEquiv) g).val i j) = _
  rw [h, thAt_apply, map_mul, map_pow, map_neg, map_one, pLoc_conjFin]
  rfl

theorem mem_KGL_of_thAt (u : Pl E) (k : GLw n (cPl E u)) (hk : thAt u k ∈ GlobalTheory.LFun.KGL u (n := n)) :
    k ∈ GlobalTheory.LFun.KGL (cPl E u) (n := n) := by
  have hv : ∀ (h : GLw n (cPl E u)) (i j : Fin n),
      Valued.v ((thAt u h).val i j) = Valued.v ((h⁻¹).val j.rev i.rev) := by
    intro h i j
    rw [thAt_apply, Valuation.map_mul, Valuation.map_pow, Valuation.map_neg, Valuation.map_one, one_pow, one_mul]
    exact (conjLoc_spec (IsCMField.complexConj E).toRingEquiv u).2.2 _
  rw [GlobLev.mem_KGL_iff_val] at hk ⊢
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := h2 j.rev i.rev
    rw [← map_inv, hv, inv_inv, Fin.rev_rev, Fin.rev_rev] at this
    exact this
  · have := h1 j.rev i.rev
    rwa [hv, Fin.rev_rev, Fin.rev_rev] at this

end GlobalTheory.EulerTw.IntRead

namespace GlobalTheory.EulerTw.IntRead

open GlobalTheory.EulerTw

end GlobalTheory.EulerTw.IntRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatVecIff
section
noncomputable section

open NumberField

namespace GlobalTheory.ThetaParseval

def ratVec (F : Type) [Field F] [NumberField F] (κ : Type) : AddSubgroup (κ → AdeleRing (𝓞 F) F) :=
  (AddMonoidHom.compLeft (algebraMap F (AdeleRing (𝓞 F) F)).toAddMonoidHom κ).range

theorem mem_ratVec_iff {F : Type} [Field F] [NumberField F] {κ : Type} (x : κ → AdeleRing (𝓞 F) F) :
    x ∈ ratVec F κ ↔ ∃ ξ : κ → F, x = fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i) := by
  constructor
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩
  · rintro ⟨ξ, rfl⟩
    exact ⟨ξ, rfl⟩

end GlobalTheory.ThetaParseval

end
end

