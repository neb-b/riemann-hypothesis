module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorIntegralHermitianLatticeRankOne
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0082
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0083

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesReferenceSubgroupsRelIndexEq
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.RefVol

theorem relIndex_inf_of_le {G : Type*} [AddGroup G] (P A K : AddSubgroup G) (h : K ≤ P) :
    (P ⊓ A).relIndex K = A.relIndex K := by
  rw [← AddSubgroup.inf_relIndex_right (P ⊓ A) K, ← AddSubgroup.inf_relIndex_right A K]
  congr 1
  ext x
  simp only [AddSubgroup.mem_inf]
  exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨h hx.2, hx.1⟩, hx.2⟩⟩

theorem relIndex_prod {G H : Type*} [AddGroup G] [AddGroup H] (A A' : AddSubgroup G)
    (B B' : AddSubgroup H) :
    (A.prod B).relIndex (A'.prod B') = A.relIndex A' * B.relIndex B' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective _ (f := (AddSubgroup.prodEquiv A' B').toAddMonoidHom)
      (AddSubgroup.prodEquiv A' B').surjective]
  congr 1

theorem relIndex_inf_comap {G H : Type*} [AddGroup G] [AddGroup H] (φ : G →+ H) (P : AddSubgroup G)
    (A B : AddSubgroup H) :
    (P ⊓ A.comap φ).relIndex (P ⊓ B.comap φ) = (A ⊓ P.map φ).relIndex (B ⊓ P.map φ) := by
  rw [relIndex_inf_of_le _ _ _ inf_le_left, AddSubgroup.relIndex_comap, inf_comm A,
    relIndex_inf_of_le _ _ _ inf_le_right]
  congr 1
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_comap]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨h2, x, h1, rfl⟩
  · rintro ⟨h2, x, h1, rfl⟩
    exact ⟨x, ⟨h1, h2⟩, rfl⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

noncomputable def sumDiv : S.V × S.V →+ S.V :=
  (algebraMap F E S.th⁻¹ • (LinearMap.id : S.V →ₗ[E] S.V)).toAddMonoidHom.comp
    (AddMonoidHom.fst S.V S.V + AddMonoidHom.snd S.V S.V)

theorem sumDiv_apply (p : S.V × S.V) : sumDiv S p = algebraMap F E S.th⁻¹ • (p.1 + p.2) := rfl

theorem th_mul : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ (th_ne S), map_one]

theorem refB_eq (J : ℕ) (Λ : Submodule L.O S.V) :
    S.refB J Λ = ((S.spanTo S.f J).toAddSubgroup.prod (S.spanTo S.f' J).toAddSubgroup) ⊓
      Λ.toAddSubgroup.comap (sumDiv S) := by
  unfold Frames.refB
  congr 1
  ext p
  simp only [AddSubgroup.mem_comap, AddSubgroup.mem_map, sumDiv_apply]
  constructor
  · rintro ⟨y, hy, h⟩
    have h' : algebraMap F E S.th • y = p.1 + p.2 := h
    rw [← h', smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    change algebraMap F E S.th • (algebraMap F E S.th⁻¹ • (p.1 + p.2)) = p.1 + p.2
    rw [smul_smul, th_mul, one_smul]

theorem map_sumDiv (X X' : Submodule E S.V) :
    (X.toAddSubgroup.prod X'.toAddSubgroup).map (sumDiv S) = (X ⊔ X').toAddSubgroup := by
  ext y
  simp only [AddSubgroup.mem_map, AddSubgroup.mem_prod, Submodule.mem_toAddSubgroup, sumDiv_apply]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.add_mem_sup h1 h2)
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    refine ⟨(algebraMap F E S.th • a, algebraMap F E S.th • b),
      ⟨X.smul_mem _ ha, X'.smul_mem _ hb⟩, ?_⟩
    rw [← smul_add, smul_smul, mul_comm (algebraMap F E S.th⁻¹), th_mul, one_smul]

theorem refB_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refB J Λ).relIndex (S.refB J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup := by
  rw [refB_eq, refB_eq, relIndex_inf_comap, map_sumDiv]
  rfl

theorem refA_relIndex (J : ℕ) (Λ Λ' : Submodule L.O S.V) :
    (S.refA J Λ).relIndex (S.refA J Λ') =
      (Λ ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (S.spanTo S.f J ⊔ S.spanTo S.f' J).restrictScalars L.O).toAddSubgroup *
      (Λ ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup.relIndex
        (Λ' ⊓ (perp L S.Hm (S.spanTo S.f J ⊔ S.spanTo S.f' J)).restrictScalars L.O).toAddSubgroup := by
  unfold Frames.refA
  rw [relIndex_prod, relIndex_prod, AddSubgroup.relIndex_self, mul_one, refB_relIndex]
  rfl

end GlobalTheory.RefVol

theorem GlobalTheory.RefVol.main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ Λ', S.IsTerm d Λ' → S.InFF β (j + 1) βJ d Λ' → (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') = (S.refA (j + 1) Λ').relIndex (S.refA (j + 1) Λ) ∧ (S.refA (j + 1) Λ).relIndex (S.refA (j + 1) Λ') ≠ 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ h1 h2 Λ' h3 h4
  have a := _root_.GlobalTheory.HL.FamilyVol.family_vol L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inl rfl)
  have b := _root_.GlobalTheory.HL.FamilyVol.family_vol L r k S j β βJ d Λ h1 h2 Λ' h3 h4 _ (Or.inr rfl)
  rw [GlobalTheory.RefVol.refA_relIndex, GlobalTheory.RefVol.refA_relIndex]
  exact ⟨by rw [a.1, b.1], mul_ne_zero a.2.1 b.2.1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatInIsLattice
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimCount

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L) (x : V) :
    ∃ r : 𝓞 K, r ≠ 0 ∧ r • x ∈ L :=
  _root_.GlobalTheory.SmulMemSpan.exists_smul_mem L hL x

theorem latIn_isLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
theorem latIn_isFullLattice (L : Submodule (𝓞 K) V) (hL : Submodule.IsFullLattice K L)
    (U : Submodule K V) : Submodule.IsFullLattice K (latIn U L) := by
  let _ := latIn_isLattice L hL.toIsLattice U
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨r, hr, hx⟩ := exists_smul_mem L hL (x : V)
  have hrK : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
  have hx' : r • x ∈ latIn U L := hx
  have hmem : r • x ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hx'
  have hmem' := (Submodule.span K (latIn U L : Set U)).smul_mem
    (algebraMap (𝓞 K) K r)⁻¹ hmem
  rw [← algebraMap_smul K r x, smul_smul, inv_mul_cancel₀ hrK, one_smul] at hmem'
  exact hmem'
end

theorem one_le_rd (K : Type) [Field K] [NumberField K] : 1 ≤ 2 * vInv K := by
  have h : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have := Int.one_le_abs (discr_ne_zero K)
    exact_mod_cast this
  have := Real.one_le_rpow h (z := (1 : ℝ) / (2 * fDeg K)) (by positivity)
  unfold vInv
  linarith

theorem real_bound (a : ℝ) (ha : 1 ≤ a) (n k f : ℕ) (hn : 1 ≤ n) (hf : 0 < f) :
    (1 + 2 * Real.sqrt (a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)))) ^ (2 * k * f) ≤
      (9 * a) ^ (k * f) * (n : ℝ) ^ ((k : ℝ) / 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have h1 : 1 ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * f)) := Real.one_le_rpow hn' (by positivity)
  have e : (n : ℝ) ^ ((k : ℝ) / 2) = ((n : ℝ) ^ ((1 : ℝ) / (2 * f))) ^ (k * f) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [e, ← mul_pow, mul_assoc 2, pow_mul]
  set B := a * (n : ℝ) ^ ((1 : ℝ) / (2 * f)) with hB
  have hB1 : 1 ≤ B := one_le_mul_of_one_le_of_one_le ha h1
  have hs : 1 ≤ Real.sqrt B := Real.one_le_sqrt.2 hB1
  have hq : Real.sqrt B ^ 2 = B := Real.sq_sqrt (by linarith)
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [mul_assoc, ← hB]
  nlinarith

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → ∀ n : ℕ, 1 ≤ n → (((primSp h L 1 n).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((9 * (2 * vInv K)) ^ (Module.finrank K V * fDeg K) * (n : ℝ) ^ ((Module.finrank K V : ℝ) / 2)) ∧ (primSp h L 0 n).encard ≤ 1 := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL n hn
  constructor
  · set B : ℝ := (2 * vInv K) * (n : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) with hB
    have hrd := one_le_rd K
    have hB0 : 0 ≤ B := by positivity
    have hsub : primSp h L 1 n ⊆ (fun x : V => Submodule.span K {x}) ''
        {x : V | x ∈ L ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ B} := by
      rintro U ⟨hU, hd⟩
      obtain ⟨x, hx, hx0, hxB⟩ := _root_.GlobalTheory.Mass.ShortVector.main K U (hRes h U) hK ⟨fun x y => hs.eq x y⟩
        (fun τ x hx => hp τ x (by simpa using hx)) hU (latIn U L)
        ⟨latIn_isFullLattice L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
      rw [hd] at hxB
      refine ⟨x, ⟨hx, hxB⟩, ?_⟩
      refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 x.2) ?_
      rw [hU, finrank_span_singleton (by simpa using hx0)]
    have h1 := (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)
    refine le_trans (by exact_mod_cast h1) ((_root_.GlobalTheory.Mass.encard_shortVectors_le K V h hK hs hp L hL B hB0).trans ?_)
    exact ENNReal.ofReal_le_ofReal (real_bound _ hrd n _ _ hn Fintype.card_pos)
  · rw [Set.encard_le_one_iff]
    rintro U W ⟨hU, -⟩ ⟨hW, -⟩
    rw [Submodule.finrank_eq_zero.1 hU, Submodule.finrank_eq_zero.1 hW]

end GlobalTheory.Mass.PrimCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeSummandAtTermOrbit
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.HL.amp_summand_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∀ Λ, ∀ h ∈ S.St, P (h • Λ) ↔ P Λ) → ∀ Λ, S.IsTerm d Λ → IsLat L Λ → ∀ o : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V), o = Quotient.mk'' Λ → S.IsTerm d o.out ∧ (∃ h ∈ S.St, o.out = h • Λ) ∧ (if S.IsTerm d o.out ∧ P o.out then (S.mu o.out : ℂ) * S.om d o.out else 0) = (if P Λ then (S.mu Λ : ℂ) * S.om d Λ else 0) ∧ (if S.IsTerm d o.out ∧ P o.out then ENNReal.ofReal (S.mu o.out) else 0) = (if P Λ then ENNReal.ofReal (S.mu Λ) else 0) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d P hP Λ hT hL o ho
  have hrel : MulAction.orbitRel S.St (Submodule L.O S.V) o.out Λ := by
    have h1 : (Quotient.mk'' o.out : MulAction.orbitRel.Quotient S.St (Submodule L.O S.V)) = Quotient.mk'' Λ :=
      (Quotient.out_eq' o).trans ho
    exact Quotient.exact' h1
  obtain ⟨g, hg⟩ := hrel
  have hout : o.out = (g : S.GLV) • Λ := by rw [← hg]; rfl
  have hgm : (g : S.GLV) ∈ S.St := g.2
  obtain ⟨hT', hom, -⟩ := _root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT _ hgm
  have hmu : S.mu ((g : S.GLV) • Λ) = S.mu Λ := (GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ hL |>.2.2 _ hgm
  have hPg : P ((g : S.GLV) • Λ) ↔ P Λ := hP Λ _ hgm
  refine ⟨hout ▸ hT', ⟨_, hgm, hout⟩, ?_, ?_⟩
  · rw [hout]; simp only [hT', true_and, hPg, hmu, hom]
  · rw [hout]; simp only [hT', true_and, hPg, hmu]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveHermitianSublatticeDiscriminantGenerato
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimDisc

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [FiniteDimensional K V] in
theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [dual, Formalism.E.hdual, Submodule.mem_iInf]

omit [NumberField K] in
theorem star_range (r : 𝓞 K) : star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem nondeg (h : V →ₗ⋆[K] V →ₗ[K] K) (hp : PD h) : h.Nondegenerate := by
  let φ : K →+* ℂ := (IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom
  constructor
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this
  · intro x hx
    by_contra h0
    have := hp φ x h0
    rw [hx x] at this
    simp at this

omit [StarRing K] [FiniteDimensional K V] in
theorem lat_map (A : Submodule K V) (p : V →ₗ[K] A) (hp : Function.Surjective p)
    (N : Submodule (𝓞 K) V) (hN : Submodule.IsFullLattice K N) :
    Submodule.IsFullLattice K (N.map (p.restrictScalars (𝓞 K))) := by
  haveI : Submodule.IsLattice K (N.map (p.restrictScalars (𝓞 K))) :=
    Submodule.IsLattice.of_fg K (hN.fg.map _)
  refine ⟨?_⟩
  change Submodule.span K (p '' (N : Set V)) = ⊤
  rw [← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hp]

theorem dual_latIn (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hp : PD h) (A : Submodule K V)
    (hsA : (hRes h A).IsSymm) (hpA : PD (hRes h A)) (p : V →ₗ[K] A) (hsur : Function.Surjective p)
    (hh : ∀ (x : V) (a : A), h (p x : V) (a : V) = h x a)
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L) :
    IsIntLat (hRes h A) (latIn A L) ∧
      dual (hRes h A) (latIn A L) = (dual h L).map (p.restrictScalars (𝓞 K)) := by
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K V h hs (nondeg h hp) star_range L hL.1
  obtain ⟨k1, k2, -⟩ := Formalism.HermitianLatticesTheory.dualLattice (𝓞 K) K A (hRes h A) hsA (nondeg _ hpA) star_range _
    (lat_map A p hsur _ h1)
  have e : dual (hRes h A) ((dual h L).map (p.restrictScalars (𝓞 K))) = latIn A L := by
    ext a
    have : a ∈ latIn A L ↔ (a : V) ∈ dual h (dual h L) := by rw [h2]; rfl
    rw [this, mem_dual, mem_dual]
    constructor
    · intro H y hy
      rw [← hh]
      exact H (p y) ⟨y, hy, rfl⟩
    · rintro H _ ⟨y, hy, rfl⟩
      have := H y hy
      rw [← hh] at this
      exact this
  rw [e] at k1 k2
  exact ⟨⟨k1, fun x hx y hy => hL.2 x hx y hy⟩, k2⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) :
    idxN (L.map (p.restrictScalars (𝓞 K))) (latIn A L) =
      idxN (L.map (q.restrictScalars (𝓞 K))) (latIn B L) := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup, ← AddSubgroup.relIndex_comap,
    ← AddSubgroup.relIndex_comap, ← AddSubgroup.inf_relIndex_right]
  conv_rhs => rw [← AddSubgroup.inf_relIndex_right]
  congr 1
  ext x
  change ((p x : V) ∈ L ∧ x ∈ L) ↔ ((q x : V) ∈ L ∧ x ∈ L)
  refine and_congr_left fun hx => ?_
  rw [← hpq x] at hx
  exact ⟨fun H => (L.add_mem_iff_right H).1 hx, fun H => (L.add_mem_iff_left H).1 hx⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem idx_map_dvd (A : Submodule K V) (p : V →ₗ[K] A) (L N : Submodule (𝓞 K) V) :
    idxN (N.map (p.restrictScalars (𝓞 K))) (L.map (p.restrictScalars (𝓞 K))) ∣ idxN N L := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup _ N, ← AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_dvd_of_le_left _ fun x hx => ⟨x, hx, rfl⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem idx_mul (A B C : Submodule (𝓞 K) V) (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem latIn_le (A : Submodule K V) (p : V →ₗ[K] A) (hp : ∀ a : A, p a = a)
    (L : Submodule (𝓞 K) V) : latIn A L ≤ L.map (p.restrictScalars (𝓞 K)) :=
  fun a ha => ⟨a, ha, hp a⟩

omit [StarRing K] [FiniteDimensional K V] [NumberField K] in
theorem gens_swap (A B : Submodule K V) (p : V →ₗ[K] A) (q : V →ₗ[K] B)
    (hp : ∀ a : A, p a = a) (hpq : ∀ x, (p x : V) + q x = x) (L : Submodule (𝓞 K) V) (t : Finset B)
    (ht : L.map (q.restrictScalars (𝓞 K)) = latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B)) :
    ∃ t' : Finset A, t'.card ≤ t.card ∧
      L.map (p.restrictScalars (𝓞 K)) = latIn A L ⊔ Submodule.span (𝓞 K) (t' : Set A) := by
  have hl : ∀ b : t, ∃ l ∈ L, q l = b := fun b => by
    have : (b : B) ∈ L.map (q.restrictScalars (𝓞 K)) := by
      rw [ht]
      exact Submodule.mem_sup_right (Submodule.subset_span b.2)
    exact this
  choose f hf1 hf2 using hl
  refine ⟨Finset.univ.image fun b => p (f b), Finset.card_image_le.trans (by simp), ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hq : q x ∈ latIn B L ⊔ Submodule.span (𝓞 K) (t : Set B) := ht ▸ ⟨x, hx, rfl⟩
    have e : (t : Set B) = (q.restrictScalars (𝓞 K)) '' Set.range f := by
      ext b
      constructor
      · intro hb
        exact ⟨f ⟨b, hb⟩, ⟨_, rfl⟩, hf2 _⟩
      · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
        have : q (f c) ∈ t := by rw [hf2]; exact c.2
        exact this
    rw [e, ← Submodule.map_span] at hq
    obtain ⟨s, hs, _, ⟨y, hy, rfl⟩, hsy⟩ := Submodule.mem_sup.1 hq
    have hyL : y ∈ L := (Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hf1 c)) hy
    refine Submodule.mem_sup.2 ⟨p (x - y), ?_, p y, ?_, by simp⟩
    · have e1 : q (x - y) = s := by
        rw [map_sub, ← hsy]; simp
      have e2 := hpq (x - y)
      rw [e1] at e2
      change (p (x - y) : V) ∈ L
      rw [eq_sub_of_add_eq e2]
      exact L.sub_mem (L.sub_mem hx hyL) hs
    · have : p y ∈ (Submodule.span (𝓞 K) (Set.range f)).map (p.restrictScalars (𝓞 K)) := ⟨y, hy, rfl⟩
      rw [Submodule.map_span, ← Set.range_comp] at this
      simpa [Function.comp_def] using this
  · refine sup_le (latIn_le A p hp L) (Submodule.span_le.2 ?_)
    intro a ha
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ] at ha
    obtain ⟨b, rfl⟩ := ha
    exact ⟨f b, hf1 b, rfl⟩

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ (L : Submodule (𝓞 K) V) (U : Submodule K V) (e : ℕ), IsIntLat h L → (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set _)) → IsIntLat (hRes h U) (latIn U L) ∧ IsIntLat (hRes h (perp h U)) (latIn (perp h U) L) ∧ discN (hRes h (perp h U)) (latIn (perp h U) L) ≤ discN (hRes h U) (latIn U L) * discN h L ∧ (∃ t : Finset ↥U, t.card ≤ (Module.finrank K (perp h U) + e) ∧ dual (hRes h U) (latIn U L) = (latIn U L) ⊔ Submodule.span (𝓞 K) (t : Set _)) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L U e hL ⟨t, hte, ht⟩
  obtain ⟨hc, hsU, hpU, -⟩ := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp).2 U
  obtain ⟨-, hsW, hpW, -⟩ := (_root_.GlobalTheory.Mass.Witt.witt_definite K V h hK hs hp).2 (perp h U)
  set W := perp h U with hW
  have horth : ∀ (u : U) (w : W), h (u : V) (w : V) = 0 := fun u w => by
    have := w.2
    simp only [hW, perp, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this u u.2
  have horth' : ∀ (u : U) (w : W), h (w : V) (u : V) = 0 := fun u w => by
    rw [← hs.eq, horth, map_zero]
  let p : V →ₗ[K] U := U.projectionOnto W hc
  let q : V →ₗ[K] W := W.projectionOnto U hc.symm
  have hpq : ∀ x, (p x : V) + q x = x := Submodule.projection_add_projection_eq_self hc
  have hp1 : ∀ a : U, p a = a := Submodule.projectionOnto_apply_left hc
  have hq1 : ∀ a : W, q a = a := Submodule.projectionOnto_apply_left hc.symm
  obtain ⟨iU, dU⟩ := dual_latIn h hs hp U hsU hpU p (Submodule.projectionOnto_surjective hc)
    (fun x a => by conv_rhs => rw [← hpq x, map_add (f := _), LinearMap.add_apply, horth', add_zero]) L hL
  obtain ⟨iW, dW⟩ := dual_latIn h hs hp W hsW hpW q (Submodule.projectionOnto_surjective hc.symm)
    (fun x a => by conv_rhs => rw [← hpq x, map_add (f := _), LinearMap.add_apply, horth, zero_add]) L hL
  have hLd : L ≤ dual h L := by rw [ht]; exact le_sup_left
  have nL := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K V h hK hs (nondeg h hp) L hL).1
  have nU := (GlobalTheory.T.hermitianLatticeDiscriminantOrder_ne_zero_unimodular K U _ hK hsU (nondeg _ hpU) _ iU).1
  have mU := idx_mul _ _ _ (latIn_le U p hp1 L) (Submodule.map_mono hLd)
  have mW := idx_mul _ _ _ (latIn_le W q hq1 L) (Submodule.map_mono hLd)
  have sw := idx_swap U W p q hpq L
  have dvU : idxN (L.map (q.restrictScalars (𝓞 K))) (latIn W L) ∣ discN (hRes h U) (latIn U L) := by
    rw [discN, dU, ← mU, sw]
    exact dvd_mul_right _ _
  refine ⟨iU, iW, ?_, ?_⟩
  · rw [discN, dW, ← mW]
    exact Nat.mul_le_mul (Nat.le_of_dvd (Nat.pos_of_ne_zero nU) dvU)
      (Nat.le_of_dvd (Nat.pos_of_ne_zero nL) (idx_map_dvd W q L _))
  · obtain ⟨s, hs1, hs2⟩ := (_root_.GlobalTheory.Mass.LatticeGens.gens_and_count K W _ _ (latIn_le W q hq1 L)
      (ne_zero_of_dvd_ne_zero nU dvU)).1 (hL.1.fg.map _)
    obtain ⟨s', h1, h2⟩ := gens_swap U W p q hp1 hpq L s hs2
    refine ⟨s' ∪ t.image p, (Finset.card_union_le _ _).trans
      (Nat.add_le_add (h1.trans hs1) (Finset.card_image_le.trans hte)), ?_⟩
    rw [dU, ht, Submodule.map_sup, h2, Submodule.map_span, Finset.coe_union, Submodule.span_union,
      sup_assoc, Finset.coe_image]
    rfl

end GlobalTheory.Mass.PrimDisc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsCorrespondStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTerm_and_om_eq_of_coord_isTermOver : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), (∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → S.IsTerm (c.dat d) (c.lat t.abelian₂) ∧ LocNG.om P t = S.om (c.dat d) (c.lat t.abelian₂) ∧ (LocNG.BBne (H := H) t ↔ ¬ S.BBzero (c.dat d) (c.lat t.abelian₂))) ∧ (∀ (d : LocNG.Datum P) Λ, S.IsTerm (c.dat d) Λ → ∃ t, LocNG.IsTermOver P d t ∧ c.lat t.abelian₂ = Λ) ∧ ∀ δ Λ, S.IsTerm δ Λ → ∃ d : LocNG.Datum P, δ = c.dat d := by
  first | exact @GlobalTheory.HL.CoordTermWt.terms_correspond | exact GlobalTheory.HL.CoordTermWt.terms_correspond | (intros; apply GlobalTheory.HL.CoordTermWt.terms_correspond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryComplement_moves_hermitianTerms : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ g ∈ P.UW0, ∀ d d' : LocNG.Datum P, LocNG.Datum.Moves g d d' → (∀ b, g (f b) = f b ∧ g (f' b) = f' b) ∧ LocNG.img g '' {Λ | LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} = {Λ | LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} := by
  first | exact @GlobalTheory.HL.ComplMove.main | exact GlobalTheory.HL.ComplMove.main | (intros; apply GlobalTheory.HL.ComplMove.main <;> assumption)
end

