module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Formalism.LocalRingCardinality.DataSpaces
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeTraceOrthogonalVolumeRat
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.VolPerp

open GlobalTheory.HL.DualInter

theorem relIndex_split {G : Type} [AddCommGroup G] {M A : AddSubgroup G} (Z : AddSubgroup G)
    (h : M ≤ A) : M.relIndex A = (M ⊓ Z).relIndex (A ⊓ Z) * (M ⊔ Z).relIndex (A ⊔ Z) := by
  have h1 : (M ⊔ Z) ⊓ A = M ⊔ (Z ⊓ A) := sup_inf_assoc_of_le Z h
  have h2 : M ≤ (M ⊔ Z) ⊓ A := le_inf le_sup_left h
  rw [← AddSubgroup.relIndex_mul_relIndex M _ A h2 inf_le_right]
  congr 1
  · rw [h1, AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right M, inf_comm Z A,
      ← inf_assoc, inf_eq_left.2 h]
  · rw [AddSubgroup.inf_relIndex_right, ← AddSubgroup.relIndex_sup_right A (M ⊔ Z),
      ← sup_assoc, sup_eq_left.2 h]

theorem relIndex_split' {G : Type} [AddCommGroup G] (A B Z : AddSubgroup G) :
    B.relIndex A = (B ⊓ Z).relIndex (A ⊓ Z) *
      (((A ⊓ B) ⊔ Z).relIndex ((A ⊔ Z) ⊓ (B ⊔ Z)) * (B ⊔ Z).relIndex (A ⊔ Z)) := by
  rw [← AddSubgroup.inf_relIndex_left, relIndex_split Z inf_le_left]
  congr 1
  · rw [inf_inf_distrib_right, AddSubgroup.inf_relIndex_left]
  · rw [← AddSubgroup.inf_relIndex_left (A ⊔ Z) (B ⊔ Z), AddSubgroup.relIndex_mul_relIndex _ _ _
      (le_inf (sup_le_sup_right inf_le_left _) (sup_le_sup_right inf_le_right _)) inf_le_left]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}

theorem expand {m : ℕ} {b c : Fin m → Fin n → E}
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) {v : Fin n → E}
    (hv : v ∈ Submodule.span E (Set.range b)) : v = ∑ j, hf L Hm v (c j) • b j := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  simp [sum_l, smul_l, hbc]

theorem inter_eq {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0) :
    Λ ⊓ (Submodule.span E (Set.range b)).restrictScalars L.O
      = Submodule.span L.O (Set.range b) := by
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rintro v ⟨hv, hvY⟩
    rw [expand hbc hvY]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range b))
      ⟨_, (hΛ.2 _).2 (hc j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · rintro _ ⟨j, rfl⟩
    exact ⟨hb j, Submodule.subset_span ⟨j, rfl⟩⟩

theorem map_eq (h : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ) {m : ℕ}
    {b c : Fin m → Fin n → E} (hb : ∀ i, b i ∈ Λ) (hc : ∀ i, c i ∈ Λ)
    (hbc : ∀ i j, hf L Hm (b i) (c j) = if i = j then 1 else 0)
    (φ : (Fin n → E) →ₗ[E] (Fin m → E)) (w : Fin m → Fin m → E)
    (hφ : ∀ v, φ v = ∑ j, hf L Hm v (b j) • w j) :
    Λ.toAddSubgroup.map φ.toAddMonoidHom = (Submodule.span L.O (Set.range w)).toAddSubgroup := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    change φ v ∈ Submodule.span L.O (Set.range w)
    rw [hφ]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact Submodule.smul_mem (Submodule.span L.O (Set.range w))
      ⟨_, (hΛ.2 _).2 (hb j) _ hv⟩ (Submodule.subset_span ⟨j, rfl⟩)
  · intro hx
    have : Submodule.span L.O (Set.range w) ≤ Λ.map (φ.restrictScalars L.O) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine ⟨c j, hc j, ?_⟩
      have : ∀ i, hf L Hm (c j) (b i) = if i = j then 1 else 0 := fun i => by
        rw [← cj_hf h, hbc]; split_ifs <;> simp
      simp [hφ, this]
    exact this hx

theorem key (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') {m : ℕ} (y : Fin m → Fin n → E) (hy : LinearIndependent E y)
    {Y Z : Submodule L.O (Fin n → E)}
    (hY : Y = (Submodule.span E (Set.range y)).restrictScalars L.O)
    (hZ : Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O) :
    (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧
    (Λ.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup =
    (Λ'.toAddSubgroup ⊔ Z.toAddSubgroup).relIndex (Λ.toAddSubgroup ⊔ Z.toAddSubgroup) *
      (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have := L.free
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  obtain ⟨b, c, hb, hc, hs, hbc⟩ := exists_dual_family h hΛ m y hy
  obtain ⟨b', c', hb', hc', hs', hbc'⟩ := exists_dual_family h hΛ' m y hy
  have hQ : Λ ⊓ Y = Submodule.span L.O (Set.range b) := by
    rw [hY, ← hs]; exact inter_eq hΛ hb hc hbc
  have hQ' : Λ' ⊓ Y = Submodule.span L.O (Set.range b') := by
    rw [hY, ← hs']; exact inter_eq hΛ' hb' hc' hbc'
  let A : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b' j) (c i)
  let B : Matrix (Fin m) (Fin m) E := fun i j => hf L Hm (b j) (c' i)
  have hA : ∀ j, b' j = ∑ i, A i j • b i := fun j =>
    expand hbc (by rw [hs, ← hs']; exact Submodule.subset_span ⟨j, rfl⟩)
  have hBA : B * A = 1 := by
    ext k j
    have := hbc' j k
    rw [hA j, sum_l] at this
    simp only [smul_l] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← if_congr eq_comm rfl rfl, ← this]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hu : IsUnit A.det := Matrix.isUnit_det_of_left_inverse hBA
  obtain ⟨d, hd⟩ := (L.cj_fix (A.det * L.cj A.det)).1 (by rw [map_mul, L.cj_cj, mul_comm])
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (hu.mul (hu.map L.cj)).ne_zero (by rw [← hd, map_zero])
  have hli : LinearIndependent E b := by
    refine Fintype.linearIndependent_iff.2 fun g hg k => ?_
    have := congrArg (fun v => hf L Hm v (c k)) hg
    simp only [sum_l, smul_l, hbc] at this
    simpa [hf] using this
  obtain ⟨-, p2, p3⟩ := _root_.GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ b hli A d hd0 hd.symm (Λ ⊓ Y) (Λ' ⊓ Y) hQ
    (by rw [hQ']; congr 2; exact funext hA)
  have hdet : (cT L A).det = L.cj A.det := by
    have : cT L A = ((L.cj : E →+* E).mapMatrix A).transpose := rfl
    rw [this, Matrix.det_transpose, ← RingHom.map_det]; rfl
  obtain ⟨-, -, r3⟩ := _root_.GlobalTheory.HL.FrameIndex.relIndex_span_matrix L ϖ hϖ (Pi.basisFun E (Fin m))
    (Pi.basisFun E (Fin m)).linearIndependent (cT L A) d hd0
    (by rw [hdet, L.cj_cj, mul_comm, hd]) _ _ rfl rfl
  let φ : (Fin n → E) →ₗ[E] (Fin m → E) := LinearMap.pi fun j => hfL L Hm (b' j)
  have hφ : ∀ v k, φ v k = hf L Hm v (b' k) := fun v k => rfl
  have m1 := map_eq h hΛ' hb' hc' hbc' φ (Pi.basisFun E (Fin m))
    (fun v => by ext k; simp [hφ, Pi.single_apply])
  have m2 := map_eq h hΛ hb hc hbc φ (fun j => ∑ i, cT L A i j • Pi.basisFun E (Fin m) i)
    (fun v => by
      ext k
      rw [hφ, hA k]
      simp [sum_r, smul_r, cT, Pi.single_apply, mul_comm])
  rw [← m1, ← m2, AddSubgroup.relIndex_map_map, AddSubgroup.relIndex_map_map] at r3
  have hker : φ.toAddMonoidHom.ker = Z.toAddSubgroup := by
    ext x
    rw [hZ, ← hs']
    constructor
    · intro hx v hv
      rw [← cj_hf h, hf_eq_zero_of_span (S := Set.range b') ?_ v hv, map_zero]
      rintro _ ⟨j, rfl⟩
      have : hf L Hm x (b' j) = 0 := congrFun hx j
      rw [← cj_hf h, this, map_zero]
    · intro hx
      funext j
      exact hx _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [hker] at r3
  refine ⟨p2, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [p3, r3]
  ring

theorem relIndex_symm (h : IsHermND L Hm) {Λ Λ' : Submodule L.O (Fin n → E)} (hΛ : IsSD L Hm Λ)
    (hΛ' : IsSD L Hm Λ') : Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ≠ 0 ∧
    Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup = Λ'.toAddSubgroup.relIndex Λ.toAddSubgroup := by
  have hY : (⊤ : Submodule L.O (Fin n → E))
      = (Submodule.span E (Set.range (Pi.basisFun E (Fin n)))).restrictScalars L.O := by
    rw [Module.Basis.span_eq]; rfl
  have hZ : (⊥ : Submodule L.O (Fin n → E))
      = (perp L Hm (Submodule.span E (Set.range (Pi.basisFun E (Fin n))))).restrictScalars L.O := by
    rw [Module.Basis.span_eq, eq_comm, eq_bot_iff]
    intro x hx
    refine eq_zero_of_hf h fun v => ?_
    rw [← cj_hf h, hx v trivial, map_zero]
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' _ (Pi.basisFun E (Fin n)).linearIndependent hY hZ
  simp only [inf_top_eq, Submodule.bot_toAddSubgroup, sup_bot_eq] at k1 k2
  exact ⟨k1, Nat.mul_self_inj.1 k2⟩

theorem vol_perp : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∀ (m : ℕ) (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Y Z : Submodule L.O (Fin n → E), Y = (Submodule.span E (Set.range y)).restrictScalars L.O → Z = (perp L Hm (Submodule.span E (Set.range y))).restrictScalars L.O → (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup ≠ 0 ∧ (Λ ⊓ Z).toAddSubgroup.relIndex (Λ' ⊓ Z).toAddSubgroup * (Λ' ⊓ Y).toAddSubgroup.relIndex (Λ ⊓ Y).toAddSubgroup = (Λ' ⊓ Z).toAddSubgroup.relIndex (Λ ⊓ Z).toAddSubgroup * (Λ ⊓ Y).toAddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup := by
  intro F _ _ _ _ _ E _ _ _ L n Hm h Λ Λ' hΛ hΛ' m y hy Y Z hY hZ
  obtain ⟨k1, k2⟩ := key h hΛ hΛ' y hy hY hZ
  obtain ⟨a1, a2⟩ := relIndex_symm h hΛ hΛ'
  have s1 := relIndex_split' Λ.toAddSubgroup Λ'.toAddSubgroup Z.toAddSubgroup
  have s2 := relIndex_split' Λ'.toAddSubgroup Λ.toAddSubgroup Z.toAddSubgroup
  rw [inf_comm Λ'.toAddSubgroup Λ.toAddSubgroup, inf_comm (Λ'.toAddSubgroup ⊔ _)] at s2
  have e1 : (Λ ⊓ Z).toAddSubgroup = Λ.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  have e2 : (Λ' ⊓ Z).toAddSubgroup = Λ'.toAddSubgroup ⊓ Z.toAddSubgroup := rfl
  rw [e1, e2]
  have b1 := a2 ▸ a1
  rw [s1] at b1
  rw [s1, s2] at a2
  rw [s2] at a1
  simp only [ne_eq, mul_eq_zero, not_or] at a1 b1
  refine ⟨a1.1, k1, ?_⟩
  rw [mul_left_comm, mul_left_comm _ (AddSubgroup.relIndex (_ ⊓ _ ⊔ _) _)] at a2
  have a3 := mul_left_cancel₀ a1.2.1 a2
  refine mul_right_cancel₀ b1.2.2 ?_
  rw [mul_assoc, mul_comm (AddSubgroup.relIndex (Λ' ⊓ Y).toAddSubgroup _), ← k2, ← mul_assoc, a3]
  ring

end GlobalTheory.HL.VolPerp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfNonarchimedeanLocalField
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocAtTopology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

theorem secondCountable_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

theorem t2Space_of_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

theorem isOpen_integer_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsOpen (𝒪[k] : Set k) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  exact Valued.isOpen_integer k

theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

theorem mem_closure_int (T : LocAt F E sig p) (c : T.Fp) (hc : c ∈ 𝒪[T.Fp]) :
    c ∈ closure (Set.range fun a : 𝓞 F => T.ιF (algebraMap (𝓞 F) F a)) := by
  haveI := T.lf
  have hc' : valuation T.Fp c ≤ 1 := hc
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.1 hU
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero T.Fp)
  have hn : ∀ (y : T.Fp) (δ : (ValueGroupWithZero T.Fp)ˣ),
      {z : T.Fp | valuation T.Fp (z - y) < δ} ∈ nhds y := fun y δ =>
    IsValuativeTopology.mem_nhds_iff'.2 ⟨δ, fun z hz => hz⟩
  obtain ⟨b, hb⟩ := T.dense.mem_nhds (hn t γ)
  have hb' : valuation T.Fp (T.ιF b - t) < valuation T.Fp t := by rw [ht]; exact hb
  have hbv : valuation T.Fp (T.ιF b) = γ := by
    rw [← ht]; exact Valuation.map_eq_of_sub_lt _ hb'
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hbv
    exact γ.ne_zero hbv.symm
  obtain ⟨x, hx1, hx2⟩ := T.dense.mem_nhds (Filter.inter_mem (hn c γ) (hn c 1))
  have hx1' : valuation T.Fp (T.ιF x - c) < γ := hx1
  have hx2' : valuation T.Fp (T.ιF x - c) < 1 := by simpa using hx2
  have hx : valuation T.Fp (T.ιF x) ≤ 1 := by
    have : T.ιF x = (T.ιF x - c) + c := by ring
    rw [this]
    exact (valuation T.Fp).map_add_le hx2'.le hc'
  have hxF : p.valuation F x ≤ 1 := by
    have h := val_le_iff T x 1
    simp only [map_one] at h
    exact h.1 hx
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hxF
    (Units.mk0 (p.valuation F b) (by simpa using hb0))
  refine ⟨T.ιF (algebraMap (𝓞 F) F a), hγ ?_, a, rfl⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - x)) < γ := by
    rw [← hbv, ← not_le, val_le_iff, not_le]
    exact ha
  have : T.ιF (algebraMap (𝓞 F) F a) - c = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - c) := by
    rw [map_sub]; ring
  change valuation T.Fp (_ - c) < γ
  rw [this]
  exact (valuation T.Fp).map_add_lt ha' hx1'

theorem locAt_topology : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), IsTopologicalRing A.Ep ∧ T2Space A.Ep ∧ LocallyCompactSpace A.Ep ∧ SecondCountableTopology A.Ep ∧ IsOpen (A.O : Set A.Ep) ∧ IsCompact (A.O : Set A.Ep) ∧ DenseRange A.ιE ∧ Function.Injective A.ιE ∧ (∀ x : E, x ≠ 0 → IsUnit (A.ιE x)) ∧ closure (Set.range fun x : 𝓞 E => A.ιE (x : E)) = (A.O : Set A.Ep) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A
  have hO := _root_.GlobalTheory.LocSpan.mem_O_iff hc sig hsig p A
  haveI := A.lf
  haveI := A.char0
  haveI := A.free
  haveI := A.top
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  haveI := secondCountable_localField A.Fp
  haveI := t2Space_of_nonarchimedeanLocalField A.Fp
  haveI hR : IsTopologicalRing A.Ep := IsModuleTopology.isTopologicalRing A.Fp A.Ep
  haveI : ContinuousSMul A.Fp A.Ep := IsModuleTopology.toContinuousSMul A.Fp A.Ep
  have hcont : Continuous (algebraMap A.Fp A.Ep) := continuous_algebraMap _ _
  let b := Module.finBasis A.Fp A.Ep
  let h : A.Ep ≃ₜ (Fin (Module.finrank A.Fp A.Ep) → A.Fp) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI hT2 : T2Space A.Ep := h.symm.t2Space
  have hLC : LocallyCompactSpace A.Ep := h.isClosedEmbedding.locallyCompactSpace
  have hSC : SecondCountableTopology A.Ep := h.secondCountableTopology
  let w := RingOfIntegers.basis E
  let L : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A.Fp) →ₗ[A.Fp] A.Ep :=
    Fintype.linearCombination A.Fp (fun i => A.ιE (w i : E))
  have hL : ∀ c, L c = ∑ i, c i • A.ιE (w i : E) := fun c => Fintype.linearCombination_apply _ _ _
  have hint : ∀ x : 𝓞 E, A.ιE (x : E) = L (fun i => (w.repr x i : A.Fp)) := by
    intro x
    rw [hL]
    conv_lhs => rw [← w.sum_repr x]
    simp [Int.cast_smul_eq_zsmul]
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← A.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, y, hn, hy⟩ : ∃ (n : ℤ) (y : 𝓞 E), n ≠ 0 ∧ (y : E) = n • x := by
      obtain ⟨n, hn, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
      exact ⟨n, ⟨_, hi⟩, hn, rfl⟩
    have h1 : A.ιE x = ((n : A.Fp)⁻¹) • A.ιE (y : E) := by
      rw [hy, map_zsmul, ← Int.cast_smul_eq_zsmul A.Fp, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [h1, hint]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hOeq : (A.O : Set A.Ep) = L '' (Set.univ.pi fun _ => (𝒪[A.Fp] : Set A.Fp)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      refine ⟨∑ j, (c j : A.Fp) • (fun i => (w.repr (x j) i : A.Fp)), ?_, ?_⟩
      · intro i _
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (c j).2 (intCast_mem _ _)
      set_option synthInstance.maxHeartbeats 100000 in
        · rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_smul, ← hint, Algebra.smul_def]
    · rintro ⟨c, hc, rfl⟩
      rw [hL]
      refine Subring.sum_mem _ fun i _ => (hO _).2 ⟨1, fun _ => ⟨c i, hc i trivial⟩, fun _ => w i, ?_⟩
      simp [Algebra.smul_def]
  have hopen : IsOpen (A.O : Set A.Ep) := by
    rw [hOeq]
    exact IsModuleTopology.isOpenMap_of_surjective hsurj _
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integer_localField A.Fp)
  have hcomp : IsCompact (A.O : Set A.Ep) := by
    rw [hOeq]
    exact (isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[A.Fp]))).image
      (IsModuleTopology.continuous_of_linearMap L)
  refine ⟨hR, hT2, hLC, hSC, hopen, hcomp, ?_, A.ιE.injective,
    fun x hx => (IsUnit.mk0 x hx).map A.ιE, ?_⟩
  · let S : Subring A.Ep := A.ιE.range.topologicalClosure
    have hS : ∀ a : A.Fp, algebraMap A.Fp A.Ep a ∈ S := by
      intro a
      refine map_mem_closure (t := Set.range A.ιE) hcont (A.dense a) ?_
      rintro _ ⟨r, rfl⟩
      exact ⟨_, A.compat r⟩
    intro y
    have hy : y ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
    change y ∈ S
    induction hy using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact S.mul_mem (hS a) hx
  · apply le_antisymm
    · refine closure_minimal ?_ hcomp.isClosed
      rintro _ ⟨x, rfl⟩
      exact (hO _).2 ⟨1, fun _ => 1, fun _ => x, by simp⟩
    · let S : Subring A.Ep := (A.ιE.comp (algebraMap (𝓞 E) E)).range.topologicalClosure
      intro y hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      change _ ∈ S
      refine S.sum_mem fun j _ => S.mul_mem ?_ (subset_closure ⟨x j, rfl⟩)
      refine map_mem_closure (t := Set.range (A.ιE.comp (algebraMap (𝓞 E) E))) hcont
        (mem_closure_int A _ (c j).2) ?_
      rintro _ ⟨r, rfl⟩
      refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
      rw [← A.compat]
      rfl

end GlobalTheory.LocAtTopology
end

