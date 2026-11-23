module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0086
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegers
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi

open GlobalTheory.CompanionTheory.SW.RealCoord

section Domain

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)

theorem infToMixed_add (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add (f := _), toMixed_add]

theorem infToMixed_algebraMap (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x

theorem infToMixed_sub (x y : Ainf F) : infToMixed F (x - y) = infToMixed F x - infToMixed F y := by
  rw [eq_sub_iff_add_eq, ← infToMixed_add, sub_add_cancel]

theorem measurable_infToMixed : Measurable (infToMixed F) := (measurePreserving_toMixed F).measurable.comp (coord_measurable F)

def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem measurableSet_infDomain : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))

theorem exists_mem_lattice {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

theorem mem_lattice (a : 𝓞 F) :
    mixedEmbedding F (a : F) ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := (mixedEmbedding.mem_span_latticeBasis F).2 ⟨a, rfl⟩

theorem existsUnique_sub_mem_infDomain (y : Ainf F) :
    ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ infDomain F := by
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F)
    (infToMixed F y)
  obtain ⟨a, ha⟩ := exists_mem_lattice F (Submodule.neg_mem _ v.2)
  have key : ∀ b : 𝓞 F, infToMixed F (y - algebraMap F (Ainf F) (b : F)) =
      -mixedEmbedding F (b : F) + infToMixed F y := fun b => by
    rw [infToMixed_sub, infToMixed_algebraMap]
    abel
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show infToMixed F (y - algebraMap F (Ainf F) (a : F)) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [key, ha, neg_neg]
    exact hv
  · have hw := huniq ⟨-mixedEmbedding F (b : F), neg_mem (mem_lattice F b)⟩ (by
      show -mixedEmbedding F (b : F) + infToMixed F y ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
      rw [← key]
      exact hb)
    have hb' : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      have := congrArg Subtype.val hw
      simp only at this
      rw [← this, neg_neg]
    exact RingOfIntegers.ext (mixedEmbedding_injective F hb')

theorem exists_isCompact_superset_infDomain :
    ∃ K₀ : Set (Ainf F), IsCompact K₀ ∧ infDomain F ⊆ K₀ := by
  let g : mixedEmbedding.mixedSpace F → (InfinitePlace F → ℝ) := fun x w => x.1 ⟨w, IsTotallyReal.isReal w⟩
  have hg : Continuous g := continuous_pi fun w => (continuous_apply _).comp continuous_fst
  have hC : IsCompact (closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  refine ⟨coord F ⁻¹' (g '' closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))), ?_, ?_⟩
  · rw [← coordHomeo_coe]
    exact (coordHomeo F).isCompact_preimage.2 (hC.image hg)
  · intro y hy
    exact ⟨infToMixed F y, subset_closure hy, rfl⟩

theorem measure_infDomain (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]

end Domain

theorem exists_bounded_infDomain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧
      li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  intro F _ _ hTR li hl
  have := hTR
  obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_superset_infDomain F
  exact ⟨infDomain F, K₀, measurableSet_infDomain F, hK₀, hsub, measure_infDomain F li hl,
    existsUnique_sub_mem_infDomain F⟩

end GlobalTheory.CompanionTheory.Equi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardOrthonormalFramesHermitianSpace
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens


open OrthCount in
theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (_root_.GlobalTheory.CompanionTheory.UnrDens.Sphere.count E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentAction
section
open ReciprocityTheory.Ty.Fin

namespace GlobalTheory.CompanionTheory.TyFin

theorem asAlgebraHom_centralIdem {Γ V W : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) :
    σ.asAlgebraHom (centralIdem ρ) =
      ∑ g, ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) • σ g := by
  unfold centralIdem
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun g _ => Representation.asAlgebraHom_single _ _ _

theorem centralIdemAct : ReciprocityTheory.Ty.Fin.St.CentralIdemAct := by
  intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ
  obtain ⟨hVn, hρ'⟩ := hρ
  obtain ⟨hWn, hσ'⟩ := hσ
  haveI := hVn
  haveI := hWn
  haveI hirrρ : ρ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of ρ hρ'
  haveI hirrσ : σ.IsIrreducible := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.isIrreducible_of σ hσ'
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  haveI : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hV0 : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hW0 : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  obtain ⟨μ, hμ⟩ := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.schur_scalar σ hσ'
    (fun g => (Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ g⁻¹)) (by
      intro g k
      have e : (k * g * k⁻¹)⁻¹ = k * g⁻¹ * k⁻¹ := by group
      have := Representation.char_conj ρ g⁻¹ k
      simp only [Representation.character] at this
      simp only [e, this])
  have hT : σ.asAlgebraHom (centralIdem ρ) = μ • (1 : Module.End ℂ W) := by
    rw [asAlgebraHom_centralIdem]; exact hμ
  have htr : μ * (Module.finrank ℂ W : ℂ) = (Module.finrank ℂ V : ℂ) *
      ((Nat.card Γ : ℂ)⁻¹ * ∑ g, σ.character g * ρ.character g⁻¹) := by
    have h1 := congrArg (LinearMap.trace ℂ W) hμ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, LinearMap.trace_one] at h1
    rw [← h1, Finset.mul_sum, Finset.mul_sum, Nat.card_eq_fintype_card]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [Representation.character]
    field_simp
  rw [Representation.char_orthonormal σ ρ] at htr
  rw [hT]
  by_cases h : Nonempty (Representation.Equiv ρ σ)
  · rw [if_pos h] at htr ⊢
    obtain ⟨φ⟩ := h
    have hd : Module.finrank ℂ V = Module.finrank ℂ W := φ.toLinearEquiv.finrank_eq
    rw [hd] at htr
    have : μ = 1 := by
      apply mul_right_cancel₀ hW0
      simpa using htr
    rw [this, one_smul]
  · rw [if_neg h] at htr ⊢
    have : μ = 0 := by
      have h0 : μ * (Module.finrank ℂ W : ℂ) = 0 := by simpa using htr
      exact (mul_eq_zero.mp h0).resolve_right hW0
    rw [this, zero_smul]

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

def colGe (d j : ℕ) (i l : Fin d) : Prop := i < l ∧ j ≤ (l : ℕ)

variable (K : Type) [Field K]

def colGeE (d j : ℕ) (i l : Fin d) : K := if (l : ℕ) = i + 1 ∧ j ≤ (l : ℕ) then 1 else 0

def colGeR (d j : ℕ) (r : Fin j → K) (i l : Fin d) : K :=
  colGeE K d (j + 1) i l + if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0

def blkEmb (d j : ℕ) (A : Matrix (Fin j) (Fin j) K) : Matrix (Fin d) (Fin d) K := fun i l =>
  if h : (i : ℕ) < j ∧ (l : ℕ) < j then A ⟨i, h.1⟩ ⟨l, h.2⟩ else if i = l then 1 else 0

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetEmptyPlacesLattice
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

namespace GlobalTheory.CompanionTheory.Equi

private theorem forall_locMem_iff_exists_mem_ideal {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (z : F) :
    (∀ v : HeightOneSpectrum (𝓞 F), GlobalTheory.CompanionTheory.Equi.LocMem I v z) ↔ ∃ y ∈ I, (y : F) = z := by
  constructor
  · intro h
    let J : Ideal (𝓞 F) :=
      { carrier := {s | ∃ y ∈ I, (s : F) * z = y}
        add_mem' := by
          rintro a b ⟨y₁, hy₁, h₁⟩ ⟨y₂, hy₂, h₂⟩
          exact ⟨y₁ + y₂, I.add_mem hy₁ hy₂, by push_cast; rw [add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, I.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨y, hy, h₁⟩
          exact ⟨c * y, I.mul_mem_left c hy, by rw [smul_eq_mul]; push_cast; rw [mul_assoc, h₁]⟩ }
    have hJ : J = ⊤ := by
      by_contra hne
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
      have hM0 : M ≠ ⊥ :=
        Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField F)
      have hv := h ⟨M, hM.isPrime, hM0⟩
      unfold GlobalTheory.CompanionTheory.Equi.LocMem at hv
      obtain ⟨s, hs, y, hy, hsy⟩ := hv
      exact hs (hJM ⟨y, hy, hsy⟩)
    have h1 : (1 : 𝓞 F) ∈ J := hJ ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := h1
    exact ⟨y, hy, by simpa using hy1.symm⟩
  · rintro ⟨y, hy, rfl⟩ v
    unfold GlobalTheory.CompanionTheory.Equi.LocMem
    exact ⟨1, fun h1 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1), y, hy, by simp⟩

theorem cosetOff_empty_eq_latCoset (F : Type) [Field F] [NumberField F] (ι : Type)
    (I : Ideal (𝓞 F)) (x0 : ι → F) :
    cosetOff (∅ : Finset (HeightOneSpectrum (𝓞 F))) I x0 = latCoset I x0 := by
  ext x
  simp only [GlobalTheory.CompanionTheory.Equi.cosetOff, GlobalTheory.CompanionTheory.Equi.latCoset, Set.mem_setOf_eq]
  constructor
  · intro h i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mp fun v => h v (by simp) i
  · intro h v _ i
    exact (forall_locMem_iff_exists_mem_ideal I (x i - x0 i)).mpr (h i) v

end GlobalTheory.CompanionTheory.Equi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetUnitIdealIntegral
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Equi.CosetTop

variable {F : Type} [Field F] [NumberField F]

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    Valued.v (algebraMap F (Fv F v) z) = v.valuation F z := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v z

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    algebraMap F (Fv F v) z ∈ v.adicCompletionIntegers F ↔ v.valuation F z ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap]

theorem locMem_top_iff (v : HeightOneSpectrum (𝓞 F)) (z : F) :
    LocMem (⊤ : Ideal (𝓞 F)) v z ↔ v.valuation F z ≤ 1 := by
  constructor
  · rintro ⟨s, hs, y, -, h⟩
    have h1 : v.valuation F (s : F) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      exact hs
    have h2 : v.valuation F (s : F) * v.valuation F z = v.valuation F (y : F) := by
      rw [← map_mul, h]
    rw [h1, one_mul] at h2
    rw [h2]
    exact HeightOneSpectrum.valuation_le_one v y
  · intro hz
    have hmem : z ∈ HeightOneSpectrum.valuationSubringAtPrime F v := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact hz
    obtain ⟨a, s, hs, h⟩ := hmem
    refine ⟨s, hs, a, Submodule.mem_top, ?_⟩
    have hs0 : (s : F) ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := RingOfIntegers.coe_injective (by simpa using h0)
      rw [this]
      exact v.asIdeal.zero_mem
    rw [h]
    change (s : F) * ((a : F) * (s : F)⁻¹) = a
    field_simp

theorem cosetOff_top : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))), cosetOff S (⊤ : Ideal (𝓞 F)) (0 : ι → F) = {x : ι → F | ∀ v, v ∉ S → ∀ i, algebraMap F (Fv F v) (x i) ∈ v.adicCompletionIntegers F} := by
  intro F _ _ ι S
  ext x
  simp only [cosetOff, Set.mem_setOf_eq, Pi.zero_apply, sub_zero, locMem_top_iff, algebraMap_mem_iff]

end GlobalTheory.CompanionTheory.Equi.CosetTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyActMemLatVIff
section
open PositivityTheory.Rg.Mass HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LatFix

section Gen

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]

theorem repr_mul {d : ℕ} (b : Module.Basis (Fin d) F E) (x y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis R b).repr x i *
        (Algebra.TensorProduct.basis R b).repr y j * algebraMap F R (b.repr (b i * b j) k) := by
  classical
  set B := Algebra.TensorProduct.basis R b with hB
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.basis_repr_tmul]
  simp

end Gen

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem eventually_integral (c : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
      algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  exact (algebraMap F (FiniteAdeleRing (𝓞 F) F) c).2

theorem eventually_mul_closed {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ x y : Fv F v ⊗[F] E,
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr x k ∈ v.adicCompletionIntegers F) →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) →
      ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x * y) k ∈
        v.adicCompletionIntegers F := by
  classical
  have h : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ i j k : Fin d,
      algebraMap F (Fv F v) (b.repr (b i * b j) k) ∈ v.adicCompletionIntegers F := by
    simp only [Filter.eventually_all]
    exact fun i j k => eventually_integral _
  filter_upwards [h] with v hv x y hx hy k
  rw [repr_mul]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (hx i) (hy j)) (hv i j k)

end Adelic

end GlobalTheory.CompanionTheory.SW.LatFix
end
end

