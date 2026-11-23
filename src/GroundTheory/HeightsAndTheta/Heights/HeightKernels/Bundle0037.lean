module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0035

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.DualStdModelField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

abbrev dualStdModelField (K : Type) [Field K] (i : ℕ) : Type :=
  FractionRing (MvPolynomial Unit (MvPolynomial Unit (ProjField K i)))

def dualStdModelS (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (C (X ()))

def dualStdModelT (K : Type) [Field K] (i : ℕ) : dualStdModelField K i :=
  algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _ (X ())

def dualStdModelEmb (K : Type) [Field K] (i : ℕ) : ProjField K i →+* dualStdModelField K i :=
  (algebraMap (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))) _).comp
    ((C : MvPolynomial Unit (ProjField K i) →+* _).comp C)

def dualStdModelPt {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) :
    (Σ k, Sum.elim (dualBlocks T) (PBlk i) k) → dualStdModelField K i
  | ⟨Sum.inl (), t⟩ => dualStdModelEmb K i (dualLatticeCoord b ⟨(), t⟩) * dualStdModelS K i
  | ⟨Sum.inr (), j⟩ =>
    dualStdModelEmb K i (algebraMap (MvPolynomial (Fin i) K) (ProjField K i) (X j)) * dualStdModelS K i *
      dualStdModelT K i

def GenFibreModelTransport.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type)
    [∀ k, Fintype (ι' k)] (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (G : GenFibre v P')
    (Ω : Type) [Field Ω] (z : (Σ k', ι' k') → Ω), RingHom.ker (eval₂Hom (Int.castRingHom Ω) z : MRing ι' →+* Ω) = P' →
    ∀ (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ Ω], (algebraMap Φ₀ Ω).fieldRange = Subfield.closure (Set.range (z ∘ v)) →
    ∀ (τ : Type) (w : τ → Σ k', ι' k') (q : Σ k', ι' k'),
      (G.x' q = 0 ↔ z q = 0) ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) =
        Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) ∧
      (Transcendental (Algebra.adjoin G.Φ (Set.range fun t => G.x' (w t) / G.x' q)) (G.x' q) ↔
        Transcendental (Algebra.adjoin Φ₀ (Set.range fun t => z (w t) / z q)) (z q))

def DualStdGraphModel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i))),
    RingHom.ker (eval₂Hom (Int.castRingHom (dualStdModelField K i)) (dualStdModelPt b) :
        MRing (Sum.elim (dualBlocks T) (PBlk i)) →+* dualStdModelField K i) =
      graphIdeal (dualIdeal b) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι₂ := PBlk i) (dualStdCoordMat b))

def DualStdModelRank.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank Φ₀ (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K

def DualStdModelTransc.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (Φ₀ : Type) [Field Φ₀] [Algebra Φ₀ (dualStdModelField K i)],
    (algebraMap Φ₀ (dualStdModelField K i)).fieldRange =
      Subfield.closure (Set.range (dualStdModelPt b ∘ inrV (ι := dualBlocks T) (ι₂ := PBlk i))) →
    1 ≤ i → ∀ c : T,
      Transcendental (Algebra.adjoin Φ₀ (Set.range fun t : T =>
        dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (dualStdModelPt b (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcGeoSecond
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 MvPolynomial

noncomputable section

namespace StackedExceptionalSecondGeometric

variable {T : Type} [Fintype T] {k : Type} [Field k]

theorem comap_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) :
    (linPrime α M).comap (C : ℤ →+* MRing (stackedBlocks T)) = RingHom.ker (Int.castRingHom k) := by
  ext z
  rw [Ideal.mem_comap, linPrime, RingHom.mem_ker, RingHom.mem_ker, linPointMap, coe_eval₂Hom, eval₂_C, eq_intCast,
    ← map_intCast (C : k →+* MvPolynomial (Option (Fin n)) k), C_eq_zero, eq_intCast]

theorem charOf_linPrime {n : ℕ} (α : T → k) (M : T → Fin n → k) : charOf (linPrime α M) = ringChar k := by
  have hker : RingHom.ker (Int.castRingHom k) = Ideal.span {((ringChar k : ℕ) : ℤ)} := by
    ext z
    rw [RingHom.mem_ker, Ideal.mem_span_singleton, eq_intCast, CharP.intCast_eq_zero_iff k (ringChar k)]
  have key : ∀ I : Ideal ℤ, I = Ideal.span {((ringChar k : ℕ) : ℤ)} →
      (Submodule.IsPrincipal.generator I).natAbs = ringChar k := fun I hI => by
    have h := Ideal.span_singleton_eq_span_singleton.mp ((Ideal.span_singleton_generator I).trans hI)
    rw [Int.associated_iff_natAbs] at h
    rw [h, Int.natAbs_natCast]
  exact key _ ((comap_linPrime α M).trans hker)


omit [Fintype T] in
theorem exists_alpha_ne {α : T → k} (hα : Submodule.span ℤ (Set.range α) = ⊤) : ∃ s, α s ≠ 0 := by
  by_contra h
  push Not at h
  have hle : Submodule.span ℤ (Set.range α) ≤ ⊥ := Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; simp [h t])
  rw [hα, top_le_iff] at hle
  exact one_ne_zero ((Submodule.mem_bot ℤ).mp (hle ▸ Submodule.mem_top : (1 : k) ∈ (⊥ : Submodule ℤ k)))

theorem isRelevant_linPrime {n : ℕ} {α : T → k} {M : T → Fin (n + 1) → k}
    (hα : Submodule.span ℤ (Set.range α) = ⊤) (hM : LinFormsIndep M) : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (linPrime α M) := by
  rintro (⟨⟩ | ⟨⟩)
  · obtain ⟨s, hs⟩ := exists_alpha_ne hα
    refine ⟨s, fun h => hs ?_⟩
    have h1 := LinPrimeExample.linPointMap_first α M s
    rw [graphFirst] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg (MvPolynomial.eval fun _ => (1 : k)) h
    simpa using h2
  · have hw : (Pi.single 0 1 : Fin (n + 1) → k) ≠ 0 := fun h0 => by
      simpa using congrFun h0 0
    obtain ⟨t, ht⟩ : ∃ t, ∑ j, M t j * (Pi.single 0 1 : Fin (n + 1) → k) j ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (hM _ h)
    refine ⟨t, fun h => ht ?_⟩
    have h1 := LinPrimeExample.linPointMap_second α M t
    rw [graphSecond] at h1
    rw [linPrime, RingHom.mem_ker, h1] at h
    have h2 := congrArg
      (MvPolynomial.eval fun o : Option (Fin (n + 1)) => o.elim (0 : k) fun j => (Pi.single 0 1 : Fin (n + 1) → k) j) h
    simpa using h2

theorem degSecond_inl : degSecond (Sum.inl ()) = 0 := by
  rw [degSecond, pullDeg, Function.extend_apply' _ _ _ (by rintro ⟨u, hu⟩; exact Sum.inr_ne_inl hu)]
  rfl

theorem length_mul_log [Finite k] :
    ((Module.length ℤ k).toNat : ℝ) * Real.log (ringChar k) = Real.log (Nat.card k) := by
  set p := ringChar k with hp
  have : CharP k p := ringChar.charP k
  have := Fact.mk (CharP.char_is_prime k p)
  let : Algebra (ZMod p) k := ZMod.algebra k p
  have : Fintype k := Fintype.ofFinite k
  have hlen : Module.length ℤ k = Module.finrank (ZMod p) k := by
    rw [Module.length_eq_of_surjective (R := ZMod p) ZMod.intCast_surjective, Module.length_eq_finrank]
  rw [hlen, ENat.toNat_natCast, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
    Nat.cast_pow, Real.log_pow]

theorem geoNum_linPrime (hCut : LinPrimeCut.Statement) (hBase : LinPrimeBase.Statement) :
    ∀ (n : ℕ) (α : T → k) (M : T → Fin (n + 1) → k), Submodule.span ℤ (Set.range α) = ⊤ → LinFormsIndep M →
      geoNum n (linPrime α M) (fun _ => degSecond) = ((Module.length ℤ k).toNat : ℤ) := by
  intro n
  induction n with
  | zero =>
    intro α M hα hM
    have hrel := isRelevant_linPrime hα hM
    rw [geoNum, dite_eq_left hrel]
    unfold LinPrimeBase.Statement at hBase
    obtain ⟨e⟩ := hBase T k α M hα hM (fun κ => (hrel κ).choose) (fun κ => (hrel κ).choose_spec)
    rw [e.toAddEquiv.toIntLinearEquiv.length_eq]
  | succ n ih =>
    intro α M hα hM
    have hrel : ∀ κ, ∃ j, (X ⟨κ, j⟩ : MRing (stackedBlocks T)) ∉ linPrime α M := isRelevant_linPrime hα hM
    rw [geoNum]
    unfold ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant
    rw [dite_eq_left hrel, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique]
    rw [show degSecond (Sum.inl default) = 0 from degSecond_inl, show degSecond (Sum.inr default) = 1 from degSecond_inr,
      zero_mul, zero_add, one_mul]
    obtain ⟨M', hM', hsupp, hmult⟩ := hCut T k n α M hα hM ((hrel (Sum.inr ())).choose)
      (hrel (Sum.inr ())).choose_spec
    have hsupp' : divSupp (linPrime α M) (X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩) =
        {linPrime α M'} := hsupp
    rw [hsupp', finsum_mem_singleton]
    have hmult' : multAt (linPrime α M ⊔ Ideal.span {(X ⟨Sum.inr default, (hrel (Sum.inr default)).choose⟩ :
        MRing (stackedBlocks T))}) (linPrime α M') = 1 := hmult
    rw [hmult', Nat.cast_one, one_mul]
    exact ih α M' hα hM'

end StackedExceptionalSecondGeometric


open StackedExceptionalSecondGeometric in
theorem DualStackedExcGeoSecond.proof (hLin : DualStackedExcLinear.Statement) (hCut : LinPrimeCut.Statement)
    (hBase : LinPrimeBase.Statement) : DualStackedExcGeoSecond.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, _, _, α, M, hα, hM, rfl, hcard⟩ := hLin K i F F' T b b' a hi hlt hcov hab E hE
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rw [Nat.add_sub_cancel, geoNum_linPrime hCut hBase n α M hα hM, charOf_linPrime, ← hcard,
    ← Nat.card_eq_fintype_card, ← length_mul_log]
  push_cast
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinPrimeBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace LinearPrimeBase

variable {T : Type} [Fintype T] {k : Type} [Field k]

def firstLin (n : T → ℤ) : MRing (stackedBlocks T) := ∑ t, n t • graphFirst t

theorem linPointMap_firstLin (α : T → k) (M : T → Fin 1 → k) (n : T → ℤ) :
    linPointMap α M (firstLin n) = C (∑ t, n t • α t) * X none := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [firstLin, map_sum, map_zsmul, LinPrimeExample.linPointMap_first, Finset.sum_mul, smul_mul_assoc]

theorem exists_comb {α : T → k} (hα : Submodule.span ℤ (Set.range α) = ⊤) (y : k) :
    ∃ n : T → ℤ, ∑ t, n t • α t = y := by
  have hy : y ∈ Submodule.span ℤ (Set.range α) := hα ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hy

def chartPt (a b : k) : Option (Fin 1) → k := fun o => o.elim a⁻¹ fun _ => b⁻¹

def chartEval (α : T → k) (M : T → Fin 1 → k) (a b : k) : MRing (stackedBlocks T) →+* k :=
  (eval (chartPt a b)).comp (linPointMap α M)

theorem chartEval_firstLin (α : T → k) (M : T → Fin 1 → k) (a b : k) (n : T → ℤ) :
    chartEval α M a b (firstLin n) = (∑ t, n t • α t) * a⁻¹ := by
  simp [chartEval, linPointMap_firstLin, chartPt]

theorem chartEval_first (α : T → k) (M : T → Fin 1 → k) (a b : k) (t : T) :
    chartEval α M a b (graphFirst t) = α t * a⁻¹ := by
  simp [chartEval, LinPrimeExample.linPointMap_first, chartPt]

theorem chartEval_second (α : T → k) (M : T → Fin 1 → k) (a b : k) (t : T) :
    chartEval α M a b (graphSecond t) = M t 0 * b⁻¹ := by
  simp [chartEval, LinPrimeExample.linPointMap_second, chartPt]

theorem chart_equiv (α : T → k) (M : T → Fin 1 → k) (hα : Submodule.span ℤ (Set.range α) = ⊤)
    (c₁ c₂ : T) (h₁ : α c₁ ≠ 0) (h₂ : M c₂ 0 ≠ 0) (J : Ideal (MRing (stackedBlocks T)))
    (hJ₁ : graphFirst c₁ - 1 ∈ J) (hJ₂ : graphSecond c₂ - 1 ∈ J)
    (hJ : J ≤ Ideal.span {graphFirst c₁ - 1, graphSecond c₂ - 1}) :
    Nonempty ((MRing (stackedBlocks T) ⧸ (linPrime α M ⊔ J)) ≃+* k) := by
  classical
  set I := linPrime α M ⊔ J with hI
  set φ := chartEval α M (α c₁) (M c₂ 0) with hφ
  set mk := Ideal.Quotient.mk I with hmk

  have hV : ∀ h, linPointMap α M h = 0 → mk h = 0 := fun h hh =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (RingHom.mem_ker.mpr hh))
  have hB₁ : mk (graphFirst c₁) = 1 := by
    rw [← map_one mk]; exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right hJ₁)
  have hB₂ : mk (graphSecond c₂) = 1 := by
    rw [← map_one mk]; exact Ideal.Quotient.eq.mpr (Ideal.mem_sup_right hJ₂)
  set N : Submodule ℤ (MRing (stackedBlocks T) ⧸ I) :=
    Submodule.span ℤ (Set.range fun t => mk (graphFirst t)) with hN
  have hLin : ∀ n : T → ℤ, mk (firstLin n) ∈ N := fun n => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [firstLin, map_sum]
    refine Submodule.sum_mem _ fun t _ => ?_
    rw [map_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

  have hD : ∀ s t, mk (graphFirst s) * mk (graphFirst t) ∈ N := fun s t => by
    obtain ⟨n, hn⟩ := exists_comb hα (α s * α t / α c₁)
    have key : α c₁ * (α s * α t / α c₁) = α s * α t := by field_simp
    have h0 := hV (graphFirst s * graphFirst t - graphFirst c₁ * firstLin n) (by
      rw [map_sub, map_mul, map_mul, LinPrimeExample.linPointMap_first, LinPrimeExample.linPointMap_first,
        LinPrimeExample.linPointMap_first, linPointMap_firstLin, hn]
      calc C (α s) * X none * (C (α t) * X none) - C (α c₁) * X none * (C (α s * α t / α c₁) * X none)
          = C (α s * α t - α c₁ * (α s * α t / α c₁)) * X none ^ 2 := by
            simp only [map_sub, map_mul]; ring
        _ = 0 := by rw [key, sub_self, map_zero, zero_mul])
    rw [map_sub, map_mul, map_mul, sub_eq_zero, hB₁, one_mul] at h0
    rw [h0]; exact hLin n

  have hE : ∀ t, mk (graphSecond t) ∈ N := fun t => by
    obtain ⟨n, hn⟩ := exists_comb hα (α c₁ * M t 0 / M c₂ 0)
    have key : M c₂ 0 * (α c₁ * M t 0 / M c₂ 0) = M t 0 * α c₁ := by field_simp
    have h0 := hV (graphSecond t * graphFirst c₁ - graphSecond c₂ * firstLin n) (by
      rw [map_sub, map_mul, map_mul, LinPrimeExample.linPointMap_first, LinPrimeExample.linPointMap_second,
        LinPrimeExample.linPointMap_second, linPointMap_firstLin, hn, Fin.sum_univ_one, Fin.sum_univ_one]
      calc C (M t 0) * (X (some (0 : Fin 1)) : MvPolynomial (Option (Fin 1)) k) * (C (α c₁) * X none) -
            C (M c₂ 0) * X (some (0 : Fin 1)) * (C (α c₁ * M t 0 / M c₂ 0) * X none)
          = C (M t 0 * α c₁ - M c₂ 0 * (α c₁ * M t 0 / M c₂ 0)) * (X (some (0 : Fin 1)) * X none) := by
            simp only [map_sub, map_mul]; ring
        _ = 0 := by rw [key, sub_self, map_zero, zero_mul])
    rw [map_sub, map_mul, map_mul, sub_eq_zero, hB₁, mul_one, hB₂, one_mul] at h0
    rw [h0]; exact hLin n
  have hMul : ∀ x y, x ∈ N → y ∈ N → x * y ∈ N := fun x y hx hy => by
    have hxy : x * y ∈ N * N := Submodule.mul_mem_mul hx hy
    rw [hN, Submodule.span_mul_span] at hxy
    refine (Submodule.span_le.mpr ?_) hxy
    rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact hD s t
  have hOne : (1 : MRing (stackedBlocks T) ⧸ I) ∈ N := hB₁ ▸ Submodule.subset_span ⟨c₁, rfl⟩

  have hAll : ∀ g, mk g ∈ N := fun g => by
    refine MvPolynomial.induction_on (motive := fun g => mk g ∈ N) g (fun a => ?_) (fun p q hp hq => ?_) (fun p v hp => ?_)
    · have hC : (C a : MRing (stackedBlocks T)) = (a : MRing (stackedBlocks T)) := eq_intCast C a
      rw [hC, map_intCast, ← zsmul_one]
      exact Submodule.smul_mem _ _ hOne
    · rw [map_add (f := _)]; exact Submodule.add_mem _ hp hq
    · rw [map_mul]
      refine hMul _ _ hp ?_
      rcases v with ⟨⟨⟨⟩⟩ | ⟨⟨⟩⟩, t⟩
      · exact Submodule.subset_span ⟨t, rfl⟩
      · exact hE t

  have hIle : I ≤ RingHom.ker φ := by
    refine sup_le (fun x hx => ?_) (hJ.trans (Ideal.span_le.mpr ?_))
    · rw [linPrime, RingHom.mem_ker] at hx
      rw [RingHom.mem_ker]
      simp [hφ, chartEval, hx]
    · rintro x (rfl | rfl)
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφ, chartEval_first, mul_inv_cancel₀ h₁,
          sub_self]
      · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, hφ, chartEval_second, mul_inv_cancel₀ h₂,
          sub_self]
  have hker : I = RingHom.ker φ := by
    apply le_antisymm hIle
    intro g hg
    rw [RingHom.mem_ker] at hg
    obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp (hAll g)
    have hn' : mk (firstLin n) = mk g := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hn, firstLin, map_sum]
      simp only [map_zsmul]
    have hd : g - firstLin n ∈ I := Ideal.Quotient.eq.mp hn'.symm
    have hd' : φ (g - firstLin n) = 0 := RingHom.mem_ker.mp (hIle hd)
    rw [map_sub, hg, zero_sub, neg_eq_zero, hφ, chartEval_firstLin] at hd'
    have hs : ∑ t, n t • α t = 0 := by
      rcases mul_eq_zero.mp hd' with h | h
      · exact h
      · exact absurd h (inv_ne_zero h₁)
    have hl : firstLin n ∈ I :=
      Ideal.mem_sup_left (RingHom.mem_ker.mpr (by rw [linPointMap_firstLin, hs, map_zero, zero_mul]))
    have := I.add_mem hd hl
    rwa [sub_add_cancel] at this
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨n, hn⟩ := exists_comb hα (y * α c₁)
    exact ⟨firstLin n, by rw [hφ, chartEval_firstLin, hn, mul_inv_cancel_right₀ h₁]⟩
  exact ⟨(Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)⟩

end LinearPrimeBase


open LinearPrimeBase in
theorem LinPrimeBase.proof : LinPrimeBase.Statement := by
  intro T _ k _ α M hα _hM c hc
  have h₁ : α (c (Sum.inl ())) ≠ 0 := fun h => hc (Sum.inl ()) (by
    rw [linPrime, RingHom.mem_ker]
    exact (LinPrimeExample.linPointMap_first α M _).trans (by rw [h, map_zero, zero_mul]))
  have h₂ : M (c (Sum.inr ())) 0 ≠ 0 := fun h => hc (Sum.inr ()) (by
    rw [linPrime, RingHom.mem_ker]
    exact (LinPrimeExample.linPointMap_second α M _).trans (by rw [Fin.sum_univ_one, h, map_zero, zero_mul]))
  refine chart_equiv α M hα (c (Sum.inl ())) (c (Sum.inr ())) h₁ h₂ _
    (Ideal.subset_span ⟨Sum.inl (), rfl⟩) (Ideal.subset_span ⟨Sum.inr (), rfl⟩) (Ideal.span_mono ?_)
  rintro _ ⟨κ, rfl⟩
  rcases κ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def IsExcCoords {K : Type} [Field K] [NumberField K] {i : ℕ} (F F' : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) {m : ℕ} (g : Fin m → Fin i → K) (α : T → k)
    (M : T → Fin (m + 1) → k) : Prop :=
  Function.Surjective ρ ∧ ρ π = 0 ∧ y₀ ∈ F.lattice ∧ (∀ j, g j ∈ F'.lattice) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b' t : Fin i → K) ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) ∧
      ρ c = α t) ∧
    (∀ t, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ y₀ ∧ ρ c = M t 0) ∧
    (∀ t j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = (b t : Fin i → K) ⬝ᵥ g j ∧ ρ c = M t j.succ) ∧
    (∃ t, α t ≠ 0) ∧ (∃ t, M t 0 ≠ 0) ∧
    (∀ c : 𝓞 K, ρ c = 0 → ∀ φ ∈ dualLattice F', algebraMap (𝓞 K) K c • φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F', ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ (algebraMap (𝓞 K) K π • y₀) →
      ρ c = 0 → φ ∈ dualLattice F) ∧
    (∀ φ ∈ dualLattice F, (∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ y₀ → ρ c = 0) →
      (∀ j, ∀ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ g j → ρ c = 0) →
      φ ∈ Submodule.span ℤ {ψ | ∃ c : 𝓞 K, ρ c = 0 ∧ ∃ χ ∈ dualLattice F, ψ = algebraMap (𝓞 K) K c • χ})

def DualStackedExcCoords.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M

def DualStackedExcBase.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcChart.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ N : ℕ, ∀ e ∈ linPrime α M,
        (graphFirst v * graphSecond u) ^ N * e ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

namespace DualStackedExcChartExample

open DualTopSimpleSubExample

end DualStackedExcChartExample

end

end GroundTheory.Heights₂.Heights
end

