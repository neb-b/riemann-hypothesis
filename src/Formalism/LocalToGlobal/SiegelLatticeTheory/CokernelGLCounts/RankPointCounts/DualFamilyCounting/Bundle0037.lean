module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0010

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.CovB

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

def sigI : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex} :=
  X.pl.trans (Formalism.MainNotions.BlockEstimateWords.l2Pl D)

theorem embS_sig (v : InfinitePlace X.B.I.F) :
    embS D (X.pl v) = (sigI X v).1.embedding ∨
      embS D (X.pl v) = ComplexEmbedding.conjugate (sigI X v).1.embedding := by
  have h : (sigI X v).1 = InfinitePlace.mk (embS D (X.pl v)) := rfl
  rcases InfinitePlace.embedding_mk_eq (embS D (X.pl v)) with h1 | h1
  · left; rw [h, h1]
  · right; rw [h, h1]
    ext x; simp

theorem discrE_eq : discr D.host.E = discr D.host.F ^ 2 := D.host.der.discr_sq

theorem finrank_O : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 D.host.F) D.host.F (𝓞 D.host.E) D.host.E]; exact D.sp.cm.deg2

theorem absNorm_ddS_ideal :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) =
      (discr D.host.F).natAbs ^ 2 := by
  rw [Ideal.absNorm_algebraMap, NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F), finrank_O]

theorem absNorm_ddS : FractionalIdeal.absNorm (ddS D) = (((discr D.host.F).natAbs ^ 2 : ℕ) : ℚ) := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_absNorm, absNorm_ddS_ideal]

def fHom : X.B.I.F →+* D.host.F where
  toFun := fun a => ⟨X.ιE (algebraMap X.B.I.F X.B.I.E a), (X.ιE_F _).2 ⟨a, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp
  map_zero' := by ext; simp
  map_add' := fun a b => by ext; simp

def fIso : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective (fHom X)
    ⟨fun a b h => by
        have h1 := congrArg Subtype.val h
        exact (algebraMap X.B.I.F X.B.I.E).injective (X.ιE.injective h1),
     fun y => by
        obtain ⟨a, ha⟩ := (X.ιE_F y.1).1 y.2
        exact ⟨a, Subtype.ext ha⟩⟩

theorem discrF_eq : discr X.B.I.F = discr D.host.F := discr_eq_discr_of_ringEquiv X.B.I.F (fIso X)

theorem absDiscrE : |(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| ^ 2 := by
  rw [discrE_eq, discrF_eq]; push_cast; rw [abs_pow]

theorem sqrtDiscrE : √|(discr D.host.E : ℝ)| = |(discr X.B.I.F : ℝ)| := by
  rw [absDiscrE, Real.sqrt_sq (abs_nonneg _)]

theorem dF_pos : 0 < |(discr X.B.I.F : ℝ)| :=
  abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero X.B.I.F)

def embVHom : D.host.E →+ (InfinitePlace X.B.I.F → ℂ) where
  toFun := embV X
  map_zero' := by funext v; simp [embV]
  map_add' := fun a b => by funext v; simp [embV]

theorem embVHom_apply (t : D.host.E) : embVHom X t = fun v => embS D (X.pl v) t := rfl

theorem embVHom_injective : Function.Injective (embVHom X) := by
  intro a b h
  obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
  exact (embS D (X.pl v)).injective (congrFun h v)

theorem closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
    AddSubgroup.closure (embV X '' (I : Set D.host.E)) =
      ((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup).map (embVHom X) := by
  have e : embV X '' (I : Set D.host.E) =
      embVHom X '' (((I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup : AddSubgroup D.host.E) : Set D.host.E) := rfl
  rw [e]
  rw [← AddMonoidHom.map_closure, AddSubgroup.closure_eq]

theorem mem_closure_embV (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)
    (a : InfinitePlace X.B.I.F → ℂ) :
    a ∈ AddSubgroup.closure (embV X '' (I : Set D.host.E)) ↔ ∃ t ∈ I, embVHom X t = a := by
  rw [closure_embV, AddSubgroup.mem_map]
  rfl

theorem idealBlock (I : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (hI : I ≠ 0) :
    Countable (AddSubgroup.closure (embV X '' (I : Set D.host.E))) ∧
    (∃ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) ∧
    ∀ F : Set (InfinitePlace X.B.I.F → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (embV X '' (I : Set D.host.E)), (a : InfinitePlace X.B.I.F → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal ((FractionalIdeal.absNorm I : ℝ) * 2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
          |(discr X.B.I.F : ℝ)|) := by
  classical
  set C := AddSubgroup.closure (embV X '' (I : Set D.host.E)) with hC
  set ΛE : AddSubgroup D.host.E := (I : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup with hΛE
  set Iu : (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ := Units.mk0 I hI with hIu
  have hIu' : ((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) = I := rfl
  set φ : InfinitePlace X.B.I.F → (D.host.E →+* ℂ) := fun v => embS D (X.pl v) with hφ
  have hsig : ∀ v, φ v = (sigI X v).1.embedding ∨ φ v = ComplexEmbedding.conjugate (sigI X v).1.embedding :=
    fun v => embS_sig X v
  have hΛ : ∀ a ∈ ΛE, a ∈ (Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := fun a ha => ha
  have hk : ΛE.relIndex
      (((Iu : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup)
      = 1 := by
    rw [hIu']; exact AddSubgroup.relIndex_self ΛE
  have hmemC : ∀ a, a ∈ C ↔ ∃ t ∈ I, embVHom X t = a := mem_closure_embV X I

  have hto : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F) → ∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F := by
    intro F v ⟨a, ha, hu⟩
    refine ⟨⟨embVHom X a, (hmemC _).2 ⟨a, a.2, rfl⟩⟩, ?_, ?_⟩
    · simpa [embVHom_apply, hφ] using ha
    · rintro ⟨b, hb⟩ hbF
      obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
      have := hu ⟨t, ht⟩ (by simpa [embVHom_apply, hφ] using hbF)
      subst this
      rfl
  have hfrom : ∀ F : Set (InfinitePlace X.B.I.F → ℂ), ∀ v,
      (∃! b : C, (b : InfinitePlace X.B.I.F → ℂ) + v ∈ F) → ∃! a : ΛE, (fun i => (1 : ℂ) * φ i a) + v ∈ F := by
    intro F v ⟨⟨b, hb⟩, hbF, hu⟩
    obtain ⟨t, ht, rfl⟩ := (hmemC b).1 hb
    refine ⟨⟨t, ht⟩, by simpa [embVHom_apply, hφ] using hbF, ?_⟩
    rintro ⟨a, ha⟩ haF
    have := hu ⟨embVHom X a, (hmemC _).2 ⟨a, ha, rfl⟩⟩ (by simpa [embVHom_apply, hφ] using haF)
    have h2 : embVHom X a = embVHom X t := congrArg Subtype.val this
    exact Subtype.ext (embVHom_injective X h2)
  refine ⟨?_, ?_, ?_⟩
  · have : Countable D.host.E := by
      let b := Module.finBasis ℚ D.host.E
      exact Function.Injective.countable b.equivFun.injective
    rw [hC, closure_embV]
    exact Function.Surjective.countable
      (f := fun a : ΛE => (⟨embVHom X a, AddSubgroup.mem_map_of_mem _ a.2⟩ : ΛE.map (embVHom X)))
      (fun ⟨y, hy⟩ => by obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy; exact ⟨⟨a, ha⟩, rfl⟩)
  · obtain ⟨F, hF, hFd⟩ := Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ
      (by rw [hk]; exact one_ne_zero) 1 one_ne_zero
    exact ⟨F, hF, fun v => hto F v (hFd v)⟩
  · intro F hF hFd
    have h := Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC D.host.E (InfinitePlace X.B.I.F) φ (sigI X) hsig Iu ΛE hΛ 1 hk
      one_ne_zero 1 one_ne_zero F hF (fun v => hfrom F v (hFd v))
    rw [h, hIu', sqrtDiscrE X]
    congr 1
    simp

theorem dF_natAbs : |(discr X.B.I.F : ℝ)| = ((discr D.host.F).natAbs : ℝ) := by
  rw [discrF_eq, Nat.cast_natAbs, Int.cast_abs]

theorem absNorm_aaD (a : Fin D.R.rS) :
    ((FractionalIdeal.absNorm (aaD D a) : ℚ) : ℝ) = |(discr X.B.I.F : ℝ)| ^ (-(2 * ((D.R.rS : ℝ) - (a : ℕ)))) := by
  unfold aaD
  rw [map_zpow₀, absNorm_ddS, Rat.cast_zpow, dF_natAbs X]
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
  congr 1; push_cast; ring

theorem aaD_ne_zero (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := by
  intro h
  have h1 := absNorm_aaD Y a
  rw [h, map_zero, Rat.cast_zero] at h1
  have := Real.rpow_pos_of_pos (dF_pos Y) (-(2 * ((D.R.rS : ℝ) - (a : ℕ))))
  linarith

theorem rpow_combine {d : ℝ} (hd : 0 < d) {x y z : ℝ} (h : x + y + 1 = z) : d ^ x * d ^ y * d = d ^ z := by
  rw [← h, Real.rpow_add hd, Real.rpow_add hd, Real.rpow_one]

theorem blockCovol_X (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inl (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inl (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inl (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inl (Sum.inl p))) := by
  have hI : aaD D p.1.1 * (aaD D p.1.2)⁻¹ ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (inv_ne_zero (aaD_ne_zero X _))
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, absNorm_aaD X, absNorm_aaD X, ← Real.rpow_neg (abs_nonneg _)]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

theorem blockCovol_K (u : D.what₂.Word) (p : LsNc5.LtPair D.R.rS) :
    Countable (cLat X u (Sum.inr (Sum.inl p))) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)), MeasurableSet F →
      (∀ v, ∃! a : cLat X u (Sum.inr (Sum.inl p)),
        (a : CSpc (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p) : CBlk D.R.rS)) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k (Sum.inr (Sum.inl p)) F = ENNReal.ofReal (cVal X u (Sum.inr (Sum.inl p))) := by
  have hI : aaD D p.1.1 * aaD D p.1.2 ≠ 0 := mul_ne_zero (aaD_ne_zero X _) (aaD_ne_zero X _)
  obtain ⟨h1, h2, h3⟩ := idealBlock X _ hI
  refine ⟨h1, h2, fun F hF hFd => (h3 F hF hFd).trans ?_⟩
  congr 1
  show _ = (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  rw [map_mul, Rat.cast_mul, absNorm_aaD X, absNorm_aaD X]
  rw [show ∀ a b c e : ℝ, a * b * c * e = (a * b * e) * c by intros; ring, rpow_combine (dF_pos X)]
  · ring
  · ring

end Formalism.L2.SG.Pf.NcReal.JX.CovB
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingVectorsExist
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem gluing_vectors_exist : GlueVecsPre := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc hpos hΛ₀ M hM hMi 𝔭 h𝔭 b a hba hc
  have := h𝔭.isPrime
  have hne : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (RingOfIntegers.not_isField F)
  set W := orthK h U with hW
  set m := finrank K W with hm
  set P : Finset (Fin (finrank K U)) := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0) with hP
  have hPc : P.card < m := hc
  have hPm : ∀ i, (P.filter (· < i)).card < m := fun i =>
    lt_of_le_of_lt (Finset.card_filter_le _ _) hPc
  let τ : Fin (finrank K U) → Fin m := fun i => ⟨(P.filter (· < i)).card, hPm i⟩
  have hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k := by
    intro i k hi hk e
    exact card_filter_lt_inj P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩) (congrArg Fin.val e)
  have hτl : ∀ i, vF 𝔭 (a i) ≠ 0 → (τ i : ℕ) + 1 < m := by
    intro i hi
    have := card_filter_lt_lt P (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
    show (P.filter (· < i)).card + 1 < m
    omega
  choose nF hnpos hncong using fun i => exists_totPos_congr (K := K) h𝔭 hne (a i) (2 * vF 𝔭 (a i))
  let t : Fin m → K := fun j =>
    if hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j then algebraMap F K (nF hj.choose) else 1
  have hts : ∀ j, star (t j) = t j := by
    intro j; simp only [t]; split_ifs
    · exact star_fix hF _
    · exact star_one K
  have htp : ∀ j, TotPos (t j) := by
    intro j; simp only [t]; split_ifs
    · exact hnpos _
    · intro φ; rw [map_one]; simp
  have htpart : ∀ i, vF 𝔭 (a i) ≠ 0 → t (τ i) = algebraMap F K (nF i) := by
    intro i hi
    have hj : ∃ i', vF 𝔭 (a i') ≠ 0 ∧ τ i' = τ i := ⟨i, hi, rfl⟩
    simp only [t, dif_pos hj]
    rw [hτ _ _ hj.choose_spec.1 hi hj.choose_spec.2]
  have htnp : ∀ j, (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ j) → t j = 1 := by
    intro j hj
    have : ¬ ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j := fun ⟨i, hi, e⟩ => hj i hi e
    simp only [t, dif_neg this]
  let h' : W →ₗ⋆[K] W →ₗ[K] K := (LinearMap.lcomp K K W.subtype).comp (h.comp W.subtype)
  have h'a : ∀ x y : W, h' x y = h x y := fun x y => rfl
  have hsym' : ∀ x y : W, star (h' x y) = h' y x := by
    intro x y; rw [h'a, h'a, ← starRingEnd_apply]; exact hs.eq _ _
  have hpos' : ∀ x : W, x ≠ 0 → TotPos (h' x x) := by
    intro x hx φ; rw [h'a]; exact hpos x x.2 (fun e => hx (Subtype.ext e)) φ
  have hm1 : m - 1 + 1 = m := by omega
  obtain ⟨v, ho, hv1, hvl⟩ := exists_presc_family hK h' hsym' hpos' (m - 1) (by omega)
    (fun j => t (Fin.cast hm1 j)) (fun j => hts _) (fun j => htp _)
  let w : Fin m → V := fun j => (v (Fin.cast hm1.symm j) : V)
  have hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0 := by
    intro j k hjk
    exact ho _ _ (fun e => hjk (Fin.ext (by have := congrArg Fin.val e; simpa using this)))
  have hwn : ∀ j : Fin m, (j : ℕ) + 1 < m → h (w j) (w j) = t j := by
    intro j hj
    have hne' : Fin.cast hm1.symm j ≠ Fin.last (m - 1) := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    have := hv1 _ hne'
    simpa [w, h'a] using this
  have hwn0 : ∀ j, h (w j) (w j) ≠ 0 := by
    intro j
    by_cases hj : (j : ℕ) + 1 < m
    · rw [hwn j hj]; exact TotPos.ne_zero' (htp j)
    · have hjl := j.isLt
      have hl : Fin.cast hm1.symm j = Fin.last (m - 1) := by
        ext; simp; omega
      have : v (Fin.cast hm1.symm j) ≠ 0 := by rw [hl]; exact hvl
      exact TotPos.ne_zero' (hpos' _ this)
  have hfix : ∀ j, ∃ x : F, h (w j) (w j) = algebraMap F K x := fun j => by
    obtain ⟨x, hx⟩ := (hF _).1 (by rw [← starRingEnd_apply]; exact hs.eq (w j) (w j))
    exact ⟨x, hx.symm⟩
  choose c hcw using hfix
  obtain ⟨π, s₀, hu⟩ := exists_isUnif0 h𝔭
  refine ⟨π, w, c, τ, fun j => (v _).2, hwo,
    fun j => ⟨hcw j, fun h0 => hwn0 j (by rw [hcw j, h0, map_zero])⟩, hτ, ⟨s₀, hu⟩, ?_, hτl, ?_⟩
  · intro i hi
    have e : algebraMap F K (c (τ i)) = algebraMap F K (nF i) := by
      rw [← hcw, hwn _ (hτl i hi), htpart i hi]
    rw [(algebraMap F K).injective e]
    exact hncong i
  · intro j hj hnp
    have e : c j = 1 := by
      apply (algebraMap F K).injective
      rw [← hcw, hwn j hj, htnp j hnp, map_one]
    rw [e, inv_one, map_one]
    exact ⟨(SP K 𝔭).one_mem, (SP K 𝔭).one_mem⟩

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemWOfPrOZero
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6 Formalism.L2.SG.Pf.ProjectionDiscriminantModule

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

def InFib (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (𝔭 : Ideal (𝓞 F)) (M T Λ : Submodule (𝓞 K) V) :
    Prop :=
  (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Λ) ∧
    dualF h 𝔭 Λ = Λ ∧
    Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T

theorem mem_W_of_prO_zero {x : V} (hx : prO hc x = 0) : x ∈ orthK h U ∧ prO hc.symm x = x := by
  have e := prO_add hc x
  rw [hx, zero_add] at e
  refine ⟨?_, e⟩
  rw [← e]
  rw [prO_apply]
  first
  | exact Submodule.projection_apply_mem ..
  | exact Submodule.projection_apply_mem _ _
  | exact Submodule.projection_apply_mem _ _ _
  | exact Submodule.projection_apply_mem _
  | simp

theorem prO_symm_locF (hp : 𝔭.IsPrime) {N : Submodule (𝓞 K) V} {y : V} (hy : y ∈ locF 𝔭 N) :
    prO hc.symm y ∈ locF 𝔭 (N.map (prO hc.symm)) := by
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp N y).mp hy
  refine (LocF.mem_locF_iff hp _ _).mpr ⟨t, ht, ?_⟩
  have hs := (prO hc.symm).map_smul (algebraMap (𝓞 F) (𝓞 K) t) y
  rw [← hs]
  exact Submodule.mem_map_of_mem hty

theorem glue_mem [FiniteDimensional K V] (hs : h.IsSymm) (h𝔭 : 𝔭.IsMaximal) (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hG₀ : Good hc M T 𝔭 Λ₀) (h0 : InFib h U 𝔭 M T Λ₀)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) (hsurj : Function.Surjective P) :
    InFib h U 𝔭 M T (glue hc T 𝔭 Λ₀ P) := by
  have hp := h𝔭.isPrime
  obtain ⟨⟨N₀, hN₀, hΛ₀⟩, hd₀, -, -⟩ := h0
  have hd : dualF h 𝔭 (glue hc T 𝔭 Λ₀ P) = glue hc T 𝔭 Λ₀ P :=
    le_antisymm (dual_le_glue hs hG₀ hd₀ hM hT hP hsurj) (glue_le_dual hs hd₀ hP)
  have hIU := glue_inf_U hG₀ hd₀ hP
  have hIW := glue_inf_orthK_eq_locF (P := P) hG₀
  refine ⟨?_, hd, hIU, hIW⟩
  have hspan : Submodule.span K (↑(M ⊔ T) : Set V) = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top, ← hT.2, ← hM.2]
    exact sup_le (Submodule.span_mono (show M ≤ M ⊔ T from le_sup_left))
      (Submodule.span_mono (show T ≤ M ⊔ T from le_sup_right))
  have hMT : Submodule.IsFullLattice K (M ⊔ T) :=
    { toIsLattice := Submodule.IsLattice.of_fg K (hM.1.sup hT.1)
      span_eq_top := hspan }
  refine exists_lattice_locF h𝔭 hMT (L₂ := N₀ ⊔ N₀.map (prO hc.symm))
    (hN₀.fg.sup (hN₀.fg.map _)) ?_ ?_ ?_
  · conv_lhs => rw [← hd]
    rw [locF_dualF h𝔭, hd]
  · refine sup_le ?_ ?_
    · intro m hm
      have : m ∈ locF 𝔭 M := LocF.le_locF 𝔭 M hm
      rw [← hIU] at this
      exact this.1
    · intro m hm
      have : m ∈ locF 𝔭 T := LocF.le_locF 𝔭 T hm
      rw [← hIW] at this
      exact this.1
  · rintro x ⟨b, hb, y, hy, c, hcy, hU, hPc⟩
    obtain ⟨z, hz, hzb⟩ := hG₀.oW b b.2
    have hyN : y ∈ locF 𝔭 N₀ := hΛ₀ ▸ hy
    have hzN : z ∈ locF 𝔭 N₀ := hΛ₀ ▸ hz
    have ex : x = y - prO hc.symm y + prO hc.symm z := by
      have e3 : prO hc y = y - prO hc.symm y := eq_sub_of_add_eq (prO_add hc y)
      calc x = prO hc x + prO hc.symm x := (prO_add hc x).symm
        _ = prO hc y + prO hc.symm z := by rw [hU, hzb, hb]
        _ = _ := by rw [e3]
    rw [ex]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
    · exact LocF.locF_mono 𝔭 le_sup_left hyN
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hyN)
    · exact LocF.locF_mono 𝔭 le_sup_right (prO_symm_locF (hc := hc) hp hzN)

def isoOf (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) :
    Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭) :=
  ((gam hG₀).symm.trans (gam hG)).toLinearMap

theorem isoOf_mk (hG₀ : Good hc M T 𝔭 Λ₀) (hG : Good hc M T 𝔭 Λ) {y w : V} (hy : y ∈ Λ₀) (hw : w ∈ Λ)
    (hwU : prO hc w = prO hc y) :
    isoOf hG₀ hG (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩) =
      Submodule.Quotient.mk ⟨prO hc.symm w, hG.iW w hw⟩ := by
  have key : ∀ {Λ' : Submodule (𝓞 K) V} (hG' : Good hc M T 𝔭 Λ') (b : Λ'),
      gam hG' (toDisc h hc M Λ' 𝔭 hG'.iU b) = toDisc h hc.symm T Λ' 𝔭 hG'.iW b := by
    intro Λ' hG' b
    unfold gam
    simp only [LinearEquiv.trans_apply]
    rw [← LinearMap.quotKerEquivOfSurjective_apply_mk (toDisc h hc M Λ' 𝔭 hG'.iU)
        (toDisc_surj h hc M Λ' 𝔭 hG'.iU hG'.oU) b, LinearEquiv.symm_apply_apply,
      Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  have h1 : (Submodule.Quotient.mk ⟨prO hc.symm y, hG₀.iW y hy⟩ : DiscMod h (orthK h U) T 𝔭) =
      gam hG₀ (toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩) := (key hG₀ ⟨y, hy⟩).symm
  have h2 : toDisc h hc M Λ₀ 𝔭 hG₀.iU ⟨y, hy⟩ = toDisc h hc M Λ 𝔭 hG.iU ⟨w, hw⟩ :=
    congrArg Submodule.Quotient.mk (Subtype.ext hwU.symm)
  unfold isoOf
  rw [h1]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [h2]
  exact key hG ⟨w, hw⟩

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

