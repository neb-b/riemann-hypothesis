module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.HermitianLattices.HermitianLatticesProofs.IndexBasic
public import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AdelstabL
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DiscOrder

section General

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem idxN_eq_card (A B : Submodule R W) : idxN A B = Nat.card (A ⧸ B.comap A.subtype) := rfl

theorem idxN_mul {A B C : Submodule R W} (h1 : A ≤ B) (h2 : B ≤ C) :
    idxN B A * idxN C B = idxN C A :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ ((Submodule.toAddSubgroup_le _ _).mpr h1)
    ((Submodule.toAddSubgroup_le _ _).mpr h2)

theorem idxN_eq_one {A B : Submodule R W} : idxN A B = 1 ↔ A ≤ B :=
  AddSubgroup.relIndex_eq_one.trans (Submodule.toAddSubgroup_le _ _)

theorem exists_max_of_covBy {X Y : Submodule R W} (h : X ⋖ Y) :
    ∃ P : Ideal R, P.IsMaximal ∧ (∀ r : R, r ∈ P ↔ ∀ y ∈ Y, r • y ∈ X) ∧ idxN Y X = Nat.card (R ⧸ P) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 ((covBy_iff_quot_is_simple h.le).1 h)
  refine ⟨P, hP, fun r => ⟨fun hr y hy => ?_, fun hr => ?_⟩, by rw [idxN_eq_card]; exact Nat.card_congr e.toEquiv⟩
  · have : r • (Submodule.Quotient.mk ⟨y, hy⟩ : Y ⧸ X.comap Y.subtype) = 0 := by
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective P (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact P.mul_mem_right a hr
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this
  · obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have h0 : r • e.symm (Submodule.Quotient.mk 1) = 0 := by
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hr y y.2
    rw [← map_smul, EmbeddingLike.map_eq_zero_iff, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero] at h0
    simpa using h0

theorem exists_covBy {X Y : Submodule R W} (hY : Y.FG) (h : X < Y) : ∃ Z, X ≤ Z ∧ Z ⋖ Y := by
  have := CompleteLattice.Iic_coatomic_of_compact_element ((Submodule.fg_iff_compact Y).1 hY)
  rcases eq_top_or_exists_le_coatom (⟨X, h.le⟩ : Set.Iic Y) with e | ⟨Z, hZ, hle⟩
  · exact absurd (congrArg Subtype.val e) h.ne
  · exact ⟨Z.1, hle, (covBy_iff_coatom_Iic Z.2).2 hZ⟩

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]


omit [StarRing K] [FiniteDimensional K V] in
theorem idxN_ne_zero {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X) (hY : Y.FG) :
    idxN Y X ≠ 0 := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors (𝓞 K)) Y X hY
    (by rw [indexBasic_locS_top (K := K) X (Submodule.IsFullLattice.span_eq_top (A := K) (M := X))]; exact le_top)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : Ideal.absNorm (Ideal.span {d}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hd0
  have : Module.Finite (𝓞 K) Y := Module.Finite.iff_fg.mpr hY
  have : Module.Finite ℤ (Y ⧸ X.comap Y.subtype) := Module.Finite.trans (𝓞 K) _
  have : Finite (Y ⧸ X.comap Y.subtype) := by
    apply Module.finite_of_fg_torsion
    intro q
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (X.comap Y.subtype) q
    refine ⟨⟨(Ideal.absNorm (Ideal.span {d}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn)⟩, ?_⟩
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • Submodule.mkQ (X.comap Y.subtype) y = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change (Ideal.absNorm (Ideal.span {d}) : ℤ) • (y : V) ∈ X
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc, mul_smul]
    exact X.smul_mem c (hdY y y.2)
  rw [idxN_eq_card]
  exact Nat.card_pos.ne'

omit [StarRing K] [FiniteDimensional K V] in
theorem lattice_between {X Y Z : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (h1 : X ≤ Z) (h2 : Z ≤ Y) : Submodule.IsFullLattice K Z :=
  Submodule.IsFullLattice.of_le_of_fg K h1 (hY.fg.of_le h2)

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem dual_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (hc : X ⋖ Y) : dual h Y ⋖ dual h X := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  refine ⟨lt_of_le_of_ne (an _ _ hc.le) fun e => hc.ne ?_, fun Z h1 h2 => ?_⟩
  · rw [← (dl X hX).2.1, ← e, (dl Y hY).2.1]
  · have hZ := lattice_between (dl Y hY).1 (dl X hX).1 h1.le h2.le
    have a1 := an _ _ h1.le
    have a2 := an _ _ h2.le
    rw [(dl Y hY).2.1] at a1
    rw [(dl X hX).2.1] at a2
    rcases hc.eq_or_eq a2 a1 with e | e
    · exact h2.ne (by rw [← e, (dl Z hZ).2.1])
    · exact h1.ne (by rw [← e, (dl Z hZ).2.1])

theorem idxN_dual_of_covBy {X Y : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X)
    (hY : Submodule.IsFullLattice K Y) (hc : X ⋖ Y) : idxN (dual h X) (dual h Y) = idxN Y X := by
  obtain ⟨P, hP, hPm, hPi⟩ := exists_max_of_covBy hc
  obtain ⟨Q, hQ, hQm, hQi⟩ := exists_max_of_covBy (dual_covBy h hs hn hX hY hc)
  set σ := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range with hσ
  have hσσ : ∀ r, σ (σ r) = r := fun r => genusCovol_hinj (by
    rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
  let e : 𝓞 K ≃+* 𝓞 K := RingEquiv.ofBijective σ (Function.Involutive.bijective hσσ)
  have hle : P ≤ Q.comap σ := by
    intro r hr
    rw [Ideal.mem_comap, hQm]
    intro x hx
    rw [dualBasic_mem_dual] at hx ⊢
    intro y hy
    have := hx _ ((hPm r).1 hr y hy)
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range] at this
    rw [genusBasic_hsmul_right]
    exact this
  have hPQ : P = Q.comap σ := hP.eq_of_le (Ideal.comap_ne_top σ hQ.ne_top) hle
  have hm : Q = P.map (e : 𝓞 K →+* 𝓞 K) := by
    rw [hPQ]
    exact (Ideal.map_comap_of_surjective σ e.surjective Q).symm
  rw [hPi, hQi]
  exact (Nat.card_congr (Ideal.quotientEquiv P Q e hm).toEquiv).symm

theorem idxN_dual {X : Submodule (𝓞 K) V} (hX : Submodule.IsFullLattice K X) : ∀ (n : ℕ)
    (Y : Submodule (𝓞 K) V), Submodule.IsFullLattice K Y → X ≤ Y → idxN Y X = n →
    idxN (dual h X) (dual h Y) = n := by
  have an := (dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).1
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hY hle hi
  rcases hle.eq_or_lt with rfl | hlt
  · rw [← hi, idxN_eq_one.2 le_rfl, idxN_eq_one.2 le_rfl]
  obtain ⟨Z, hXZ, hc⟩ := exists_covBy hY.fg hlt
  have hZ := lattice_between hX hY hXZ hc.le
  have m1 := idxN_mul hXZ hc.le
  have n1 := idxN_ne_zero hX hZ.fg
  have n2 := idxN_ne_zero hZ hY.fg
  have n3 : idxN Y Z ≠ 1 := fun e => hc.lt.not_ge (idxN_eq_one.1 e)
  have hlt' : idxN Z X < n := by
    rw [← hi, ← m1]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero n1) (by omega)
  rw [← idxN_mul (an _ _ hc.le) (an _ _ hXZ), ih _ hlt' Z hZ hXZ rfl, idxN_dual_of_covBy h hs hn hZ hY hc,
    ← hi, ← m1, mul_comm]

end GlobalTheory.Mass.DiscOrder

namespace GlobalTheory.Mass.DiscOrder

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → discN h M ≠ 0 ∧ (discN h M = 1 ↔ IsUnimodular h M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → idxN M' M ≠ 0 ∧ discN h M = discN h M' * idxN M' M ^ 2) ∧ (∀ N ∈ genus h M, IsIntLat h N ∧ discN h N = discN h M) ∧ (∀ P : Ideal (𝓞 K), P.IsMaximal → ((discN h M : ℕ) : 𝓞 K) ∉ P → IsUnimodularAt h P M) ∧ (∀ M' : Submodule (𝓞 K) V, IsIntLat h M' → M ≤ M' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P M → loc (K := K) P M = loc (K := K) P M') := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn M hM
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have ld := locDual (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  have hMd := (hint M).1 hM.2
  have h0 : ∀ N, IsIntLat h N → discN h N ≠ 0 := fun N hN => idxN_ne_zero hN.1 (dl N hN.1).1.fg
  refine ⟨h0 M hM, ?_, fun M' hM' hle => ⟨idxN_ne_zero hM.1 hM'.1.fg, ?_⟩, fun N hN => ?_,
    fun P hP hd => ?_, fun M' hM' hle P hP hu => ?_⟩
  · rw [huni, discN, idxN_eq_one]
    exact ⟨fun e => ⟨hM.2, e⟩, fun e => e.2⟩
  · have hMd' := (hint M').1 hM'.2
    rw [discN, discN, ← idxN_mul (hle.trans hMd') (an _ _ hle), ← idxN_mul hle hMd',
      idxN_dual h hs hn hM.1 _ M' hM'.1 hle rfl]
    ring
  · have hNi : IsIntLat h N := ⟨hN.1,
      (((genusBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range).2.2 M N hM.1.fg hN.1.fg hN.2).2).1 hM.2⟩
    refine ⟨hNi, genusCovol_lemmaS _ M (dual h M) N (dual h N) hMd ((hint N).1 hNi.2) rfl (h0 M hM)
      (h0 N hNi) fun P hP => ?_⟩
    obtain ⟨g, hg, hgL⟩ := hN.2 P hP
    have hle := locBasic_hcompl_le (K := K) P
    have key : ∀ A B : Submodule (𝓞 K) V, gmap g (loc (K := K) P A) = loc (K := K) P B →
        gmap g (locS P.primeCompl A) = locS P.primeCompl B := by
      intro A B e
      rw [← genusCovol_locS_locS hle A, gmap_locS_comm]
      change locS P.primeCompl (gmap g (loc (K := K) P A)) = _
      rw [e]
      exact genusCovol_locS_locS hle B
    obtain ⟨a1, a2, -, -, -⟩ := isomAct (𝓞 K) K V h g hg M
    have hgM : (gmap g M).FG := hM.1.fg.map ((g : V →ₗ[K] V).restrictScalars (𝓞 K))
    have b1 := (ld (gmap g M) hgM).1 P hP.isPrime
    have b2 := (ld N hN.1.fg).1 P hP.isPrime
    refine ⟨_, g.injective, genusCovol_addData g _ _ (key _ _ hgL), genusCovol_addData g _ _ (key _ _ ?_)⟩
    rw [b2.1, ← b2.2, ← hgL, ← a2 P, b1.2, ← b1.1, a1, (isomAct (𝓞 K) K V h g hg (dual h M)).2.1 P]
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1]
    refine le_antisymm ((locBasic_locS_mono _ fun x hx => ?_).trans (locBasic_locS_idem _ M).le)
      (locBasic_locS_mono _ hMd)
    refine ⟨(discN h M : 𝓞 K), Submonoid.subset_closure ⟨hd, fun t ht => ?_⟩, ?_⟩
    · have : t = (discN h M : 𝓞 K) := genusCovol_hinj (by rw [ht]; simp)
      rwa [this]
    · rw [Nat.cast_smul_eq_nsmul]
      have := AddSubgroup.nsmul_index_mem (H := M.toAddSubgroup.addSubgroupOf (dual h M).toAddSubgroup) ⟨x, hx⟩
      exact this
  · have b := (ld M hM.1.fg).1 P hP.isPrime
    rw [IsUnimodularAt, b.2, ← b.1] at hu
    refine le_antisymm (locBasic_locS_mono _ hle) ?_
    rw [← hu]
    exact locBasic_locS_mono _ (((hint M').1 hM'.2).trans (an _ _ hle))

end GlobalTheory.Mass.DiscOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InclEIntMem
section
open NumberField
open scoped TensorProduct

noncomputable section
open Classical

namespace GlobalTheory.VectorInclusion

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def vecIncl (x : Fin n → E) : Fin n → E ⊗[F] Formalism.MainNotions.S.Af F :=
  fun i => Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (x i)

theorem inclE_int_mem (c : 𝓞 E) :
    Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E) ∈ Formalism.MainNotions.S.IntAf F E := by
  unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt
  apply Subring.subset_closure
  left
  refine ⟨⟨(c : E), ⟨c, rfl⟩⟩, ?_⟩
  rfl

theorem vecIncl_add (x y : Fin n → E) :
    vecIncl (F := F) (x + y) = vecIncl (F := F) x + vecIncl (F := F) y := by
  funext i; simp [vecIncl, map_add (f := _)]

theorem vecIncl_zero : vecIncl (F := F) (0 : Fin n → E) = 0 := by
  funext i; simp [vecIncl]

theorem vecIncl_smul (c : 𝓞 E) (x : Fin n → E) :
    vecIncl (F := F) (c • x) =
      (⟨Formalism.UG.inclE (F := F) (Formalism.MainNotions.S.Af F) (c : E), inclE_int_mem c⟩ : Formalism.MainNotions.S.IntAf F E) •
        vecIncl (F := F) x := by
  funext i
  simp only [vecIncl, Pi.smul_apply]
  rw [Algebra.smul_def, map_mul]
  rfl

theorem lamAf_fg (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) := by
  obtain ⟨s, hs⟩ := hL
  refine ⟨s.image (vecIncl (F := F)), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_image, Set.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    apply Submodule.subset_span
    have hxL : x ∈ L := hs ▸ Submodule.subset_span hx
    exact ⟨⟨x, hxL⟩, rfl⟩
  · unfold Formalism.MainNotions.S.lamAf
    rw [Submodule.span_le]
    rintro y ⟨⟨x, hx⟩, rfl⟩
    have key : ∀ z ∈ Submodule.span (𝓞 E) (s : Set (Fin n → E)),
        vecIncl (F := F) z ∈ Submodule.span (Formalism.MainNotions.S.IntAf F E)
          ((s.image (vecIncl (F := F)) : Finset _) : Set (Fin n → E ⊗[F] Formalism.MainNotions.S.Af F)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        apply Submodule.subset_span
        simp only [Finset.coe_image]
        exact ⟨z, hz, rfl⟩
      | zero => rw [vecIncl_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [vecIncl_add]; exact Submodule.add_mem _ ha hb
      | smul c a _ ha => rw [vecIncl_smul]; exact Submodule.smul_mem _ _ ha
    rw [← hs] at hx
    exact key x hx

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E] [inst_4 : Algebra F E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), Submodule.FG L → Submodule.FG (R := ↥(Formalism.MainNotions.S.IntAf F E)) (Formalism.MainNotions.S.lamAf L) :=
  fun L hL => lamAf_fg L hL

end GlobalTheory.VectorInclusion

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfStabilizerSmulEqConj
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem inf_stabilizer_smul_eq_conj {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)
    {h : G} (hh : h ∈ H) (x : X) :
    H ⊓ MulAction.stabilizer G (h • x) = MulAut.conj h • (H ⊓ MulAction.stabilizer G x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) h1) hh, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := H.mul_mem (H.mul_mem hh h1) (H.inv_mem hh)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_conj_of_invVol_conj {G : Type} [Group G] (K A B : Subgroup G) (g : G)
    (hA : K.relIndex A ≠ 0) (hA' : A.relIndex K ≠ 0) (hB : K.relIndex B ≠ 0) (hB' : B.relIndex K ≠ 0)
    (h : invVol K (MulAut.conj g • A) = invVol K A) :
    invVol K (MulAut.conj g • B) = invVol K B := by
  have e : ∀ A B : Subgroup G,
      (MulAut.conj g • A).relIndex (MulAut.conj g • B) = A.relIndex B := fun A B =>
    Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) A B
      (MulAut.conj g).injective
  have hpos : 0 < invVol K (MulAut.conj g • A) := by
    rw [h]; exact (invVol_mul_pos_le_conj K A A hA hA' hA hA').2.1
  have hAB : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero_trans hA' hB
  have hBA : B.relIndex A ≠ 0 := Subgroup.relIndex_ne_zero_trans hB' hA
  have c1 : K.relIndex (MulAut.conj g • A) ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c2 : (MulAut.conj g • A).relIndex K ≠ 0 := by
    intro h0
    simp [invVol, h0] at hpos
  have c3 : K.relIndex (MulAut.conj g • B) ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans c1 (by rw [e]; exact hAB)
  have c4 : (MulAut.conj g • B).relIndex K ≠ 0 :=
    Subgroup.relIndex_ne_zero_trans (by rw [e]; exact hBA) c2
  rw [(invVol_mul_pos_le_conj K _ _ c1 c2 c3 c4).1, (invVol_mul_pos_le_conj K A B hA hA' hB hB').1, h]
  congr 1
  rw [invVol, invVol, e, e]

theorem Frames.nu_pos_and_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 < S.nu d ∧ ∀ h ∈ S.H0, S.nu (h • d) = S.nu d := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  obtain ⟨hv, hd⟩ := _root_.GlobalTheory.HL.Frames.stab_commensurable_invVol_smul L r k S
  obtain ⟨d1, d2⟩ := hd d Λ hT
  have hSD := (_root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT).1
  obtain ⟨l1, l2, l3⟩ := hv Λ hSD.1
  refine ⟨(invVol_mul_pos_le_conj _ _ _ d1 d2 d1 d2).2.1, fun h hh => ?_⟩
  have := l3 h hh
  rw [inf_stabilizer_smul_eq_conj _ hh] at this
  unfold Frames.nu
  rw [inf_stabilizer_smul_eq_conj _ hh]
  exact invVol_conj_of_invVol_conj _ _ _ h l1 l2 d1 d2 this

end GlobalTheory.HL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLocDIffSpan
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.Mass.SemiBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain in
private theorem natCast_not_isUnit_lemma_3 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N) :
    ¬ IsUnit (N : 𝓞 F) := by
  intro h
  have h1 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 F) (N : ℤ))) := by
    have : algebraMap ℤ (𝓞 F) (N : ℤ) = (N : 𝓞 F) := by simp
    rw [this]; exact h.map _
  rw [Algebra.norm_algebraMap, Int.isUnit_iff] at h1
  have hk : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h2 : (2 : ℤ) ≤ (N : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    calc (2 : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
      _ = (N : ℤ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by omega) hk
  omega

open NumberField IsDedekindDomain in
private theorem mem_primeTo_ne_zero_lemma_2 {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : 2 ≤ N)
    {x : 𝓞 F} (hx : x ∈ _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F)) : x ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(N : 𝓞 F)})
    (by rw [Ne, Ideal.span_singleton_eq_top]; exact natCast_not_isUnit_lemma_3 hN)
  exact hx Q hQ (hle (Ideal.mem_span_singleton_self _)) Q.zero_mem

open NumberField IsDedekindDomain in
private theorem primeTo_le_nonZeroDivisors__lemma {F : Type} [Field F] [NumberField F] {N : ℕ}
    (hN : 2 ≤ N) : _root_.GlobalTheory.Mass.primeTo (N : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) :=
  fun _ hx => mem_nonZeroDivisors_of_ne_zero (mem_primeTo_ne_zero_lemma_2 hN hx)

open NumberField Matrix in
open scoped ENNReal Classical in
variable {K : Type} [Field K] [NumberField K] in
theorem _root_.GlobalTheory.Mass.SemiBasis.primeTo_le {d : ℕ} (hd : 2 ≤ d) :
    _root_.GlobalTheory.Mass.primeTo (d : 𝓞 K) ≤ nonZeroDivisors (𝓞 K) :=
  primeTo_le_nonZeroDivisors__lemma hd

abbrev A (K : Type) [Field K] [NumberField K] {d : ℕ} (hd : 2 ≤ d) : Subalgebra (𝓞 K) K :=
  Localization.subalgebra.ofField K (primeTo (d : 𝓞 K)) (primeTo_le hd)

theorem primes_finite {d : ℕ} (hd : 2 ≤ d) : {P : Ideal (A K hd) | P.IsPrime}.Finite := by
  have hd0 : (d : 𝓞 K) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hfin : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (d : 𝓞 K) ∈ P}.Finite := by
    have h0 : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hd0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hdP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hd0 (by simpa using hdP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hdP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap (𝓞 K) (A K hd)))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeTo (d : 𝓞 K)) (A K hd) P).mp hP'
  refine ⟨P.comap (algebraMap (𝓞 K) (A K hd)), ?_,
    IsLocalization.map_under (primeTo (d : 𝓞 K)) (A K hd) P⟩
  set Q := P.comap (algebraMap (𝓞 K) (A K hd))
  have hsub : (Q : Set (𝓞 K)) ⊆ ⋃ i ∈ (hfin.toFinset : Set (Ideal (𝓞 K))), ((id i : Ideal (𝓞 K)) : Set (𝓞 K)) := by
    intro x hx
    by_contra hn
    refine Set.disjoint_left.mp hdisj (?_ : x ∈ primeTo (d : 𝓞 K)) hx
    intro I hI hdI hxI
    apply hn
    simp only [Set.mem_iUnion]
    exact ⟨I, by simpa using ⟨hI, hdI⟩, hxI⟩
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  obtain ⟨I, hI, hle⟩ := (Ideal.subset_union_prime ⊥ ⊥ (fun i hi _ _ => by
    have : i.IsMaximal ∧ (d : 𝓞 K) ∈ i := by simpa using hi
    exact this.1.isPrime)).1 hsub
  have hI' : I.IsMaximal ∧ (d : 𝓞 K) ∈ I := by simpa using hI
  have : Q = I := hmax.eq_of_le hI'.1.ne_top hle
  right
  rw [this]
  exact hI'

theorem isPID {d : ℕ} (hd : 2 ≤ d) : IsPrincipalIdealRing (A K hd) := by
  have : IsDedekindDomain (A K hd) :=
    IsLocalization.isDedekindDomain (𝓞 K) (primeTo_le hd) (A K hd)
  exact IsPrincipalIdealRing.of_finite_primes (primes_finite hd)

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

end GlobalTheory.Mass.SemiBasis
end
end

