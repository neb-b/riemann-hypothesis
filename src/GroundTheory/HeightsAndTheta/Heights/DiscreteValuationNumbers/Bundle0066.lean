module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0064
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosurePullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0006
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocMaxPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem prime_eq_of_isLocalization_atPrime' {F : Type*} [Field F] {B R : Subring F} (h : B ≤ R)
    (𝔭₁ 𝔭₂ : Ideal B) [𝔭₁.IsPrime] [𝔭₂.IsPrime]
    (hl₁ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₁)
    (hl₂ : letI := (Subring.inclusion h).toAlgebra; IsLocalization.AtPrime R 𝔭₂) : 𝔭₁ = 𝔭₂ := by
  let _ := (Subring.inclusion h).toAlgebra
  have := hl₁
  have := hl₂
  have : IsLocalRing R := IsLocalization.AtPrime.isLocalRing R 𝔭₁
  rw [← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₁ inferInstance,
    ← IsLocalization.AtPrime.under_maximalIdeal R 𝔭₂ inferInstance]

theorem BlowUpOverLocMaxPoint.proof (h₁ : BlowUpOverLocMaxCentre.Statement.{u})
    (h₂ : BlowUpOverLocFibreMinimal.Statement.{u}) (h₃ : BlowUpOverLocPointDeg.Statement.{u}) :
    BlowUpOverLocMaxPoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro 𝔫 h𝔫
  obtain ⟨W', hW'p, hW'h, hW'r, hW'le, hW'c, h, hl⟩ :=
    h₁ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel 𝔫 h𝔫
  have hmin := h₂ O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel W' hW'p hW'h hW'r hW'le hW'c
  obtain ⟨h', 𝔫', h𝔫', hl', hdeg⟩ :=
    h₃ O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hmin hW'r hW'c
  have := h𝔫.isPrime
  have := h𝔫'.isPrime
  have heq : 𝔫 = 𝔫' := prime_eq_of_isLocalization_atPrime' h 𝔫 𝔫' hl hl'
  subst heq
  exact ⟨W', ⟨hmin, hW'r, hW'c⟩, ⟨h, hl⟩, hdeg⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpOverLocPointMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem BlowUpOverLocPointMax.proof (hfin : BlowUpOverLocFinite.Statement.{u})
    (hiso : BlowUpLocRingIso.Statement.{u}) (hfrac : BlowUpLocRingFrac.Statement.{u}) : BlowUpOverLocPointMax.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel
  have := hP.multiProj.isPrime
  intro W' hW' hW'rel hW'W
  have hW'p : W'.IsPrime := hW'.1.1
  have hbl : blowUpOf P u ≤ W' := le_trans le_sup_left hW'.1.2
  have hmh : IsMultiHomogIdeal W' :=
    MinimalPrimeMultiHomog.full O (Option K) (extIdx ι J) _ W'
      (SupSpanMultiHomog.full O (Option K) (extIdx ι J) _ _ (liftMDeg c)
        (isMultiHomogIdeal_blowUpOf hP.multiProj.multiHomog N u hu) (isMultiHomog_liftForm hx)) hW'
  have hBR : blowUpOverLoc P W u ≤ blowUpLocRing P u W' :=
    iInf₂_le W' ⟨hW'p, hmh, hW'rel, hbl, hW'W.le⟩
  have : (blowUpOf P u).IsPrime := RingHom.ker_isPrime _
  obtain ⟨φ, hφ⟩ := hiso O K ι J P u W' hbl
  obtain ⟨hlocT, hunitT⟩ :=
    HomLocRingIsLocal.proof HomLocRingMem.proof O (Option K) (extIdx ι J) (blowUpOf P u) W' hW'p hbl
  have : IsLocalRing (blowUpLocRing P u W') := φ.isLocalRing
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hWp : W.IsPrime := hWmin.1.1
  obtain ⟨hlocA, hunitA⟩ := HomLocRingIsLocal.proof HomLocRingMem.proof O K ι P W hWp hPW
  let 𝔫 : Ideal (blowUpOverLoc P W u) :=
    (IsLocalRing.maximalIdeal (blowUpLocRing P u W')).comap (Subring.inclusion hBR)

  have hcomapA : (𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (homLocRing P W) ≤
        𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) := by
      rintro ⟨z, hz⟩ ha
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha
      obtain ⟨b, f, g, hf, hg, hgW, rfl⟩ := (HomLocRingMem.proof O K ι P W hWp hPW z).mp hz
      have hfW : f ∈ W := by
        by_contra hfW
        exact ha ((hunitA b f g hf hg hgW hz).mpr hfW)
      have hgW' : liftForm (J := J) g ∉ W' := fun h => hgW (by rw [← hW'W]; exact h)
      have hfW' : liftForm (J := J) f ∈ W' := by rw [← hW'W] at hfW; exact hfW
      have hlf := isMultiHomog_liftForm (J := J) hf
      have hlg := isMultiHomog_liftForm (J := J) hg
      have hz' : algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm f)) /
          algebraMap (MRing (extIdx ι J) O ⧸ blowUpOf P u)
            (FractionRing (MRing (extIdx ι J) O ⧸ blowUpOf P u)) (Ideal.Quotient.mk _ (liftForm g)) ∈
          homLocRing (blowUpOf P u) W' :=
        Subring.subset_closure ⟨liftMDeg b, _, _, hlf, hlg, hgW', rfl⟩
      have hnu : ¬ IsUnit (⟨_, hz'⟩ : homLocRing (blowUpOf P u) W') :=
        fun h => (hunitT _ _ _ hlf hlg hgW' hz').mp h hfW'
      have hφz : Subring.inclusion hBR (algebraMap (homLocRing P W) (blowUpOverLoc P W u) ⟨_, hz⟩) =
          φ ⟨_, hz'⟩ := by
        apply Subtype.ext
        rw [hφ _ _ _ hlf hlg hgW', blowUpEval_liftForm, blowUpEval_liftForm]
        rfl
      rw [Ideal.mem_comap, Ideal.mem_comap, hφz, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_map_iff]
      exact hnu
    have hne : 𝔫.comap (algebraMap (homLocRing P W) (blowUpOverLoc P W u)) ≠ ⊤ :=
      Ideal.comap_ne_top _ (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top)
    rw [le_antisymm (IsLocalRing.le_maximalIdeal hne) hle]
    infer_instance
  obtain ⟨hfinite, -⟩ := hfin O K ι J P n hP N u hu hu' c x hx hxP W hWmin hWrel
  have : 𝔫.IsPrime := Ideal.comap_isPrime (Subring.inclusion hBR) (IsLocalRing.maximalIdeal _)
  have h𝔫 : 𝔫.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔫 hcomapA
  refine ⟨hBR, 𝔫, h𝔫, ?_⟩
  letI := (Subring.inclusion hBR).toAlgebra
  have := h𝔫.isPrime
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)
  · rintro ⟨z, hz⟩
    obtain ⟨b, hb, s, hs, ⟨t, ht, hst⟩, hzs⟩ :=
      hfrac O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP W hϖW hWmin hWrel W' hW' hW'rel hW'W z hz
    refine ⟨(⟨b, hb⟩, ⟨⟨s, hs⟩, ?_⟩), Subtype.ext hzs⟩
    intro hm
    have hm' := (IsLocalRing.mem_maximalIdeal _).mp hm
    exact hm' (IsUnit.of_mul_eq_one (⟨t, ht⟩ : blowUpLocRing P u W') (Subtype.ext hst))
  · intro a a' h
    exact ⟨1, by rw [Subring.inclusion_injective hBR h]⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagProjTrdegLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagProjTrdegLe

theorem trdeg_quot_ker_eq_range {R A B C : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [Algebra R A]
    [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) (hg : Function.Injective g) :
    Algebra.trdeg R (A ⧸ RingHom.ker f) = Algebra.trdeg R (g.comp f).range := by
  have hker : RingHom.ker (g.comp f) = RingHom.ker f := by
    ext a
    simp only [RingHom.mem_ker, AlgHom.comp_apply]
    exact ⟨fun h => hg (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  rw [← hker]
  exact (Ideal.quotientKerEquivRange (g.comp f)).trdeg_eq

theorem rename_comp_pointConeMap {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O).comp
        (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p))) =
      (pointConeMap O pt).comp (rename (FieldNumbers.blockIncl j ι')) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp [pointConeMap, FieldNumbers.blockIncl]

theorem trdeg_blocks_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ] {Λ K' : Type} (ι' : Λ → Type)
    (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  have hren : Function.Injective ((rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O) :=
    rename_injective _ j.injective
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), rename_comp_pointConeMap,
    AlgHom.id_comp]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

theorem trdeg_blocks_add_one_le {O Φ : Type} [CommRing O] [Field Φ] [Algebra O Φ]
    (hO : Function.Injective (algebraMap O Φ)) {Λ K' : Type} (ι' : Λ → Type) (j : K' ↪ Λ) (pt : (Σ o, ι' o) → Φ)
    (b : Λ) (hjb : ∀ o, j o ≠ b) (l : ι' b) (hc : pt ⟨b, l⟩ ≠ 0) :
    Algebra.trdeg O (MvPolynomial (Σ o, ι' (j o)) O ⧸ pointIdeal O (fun p => pt (FieldNumbers.blockIncl j ι' p))) + 1 ≤
      Algebra.trdeg O (MvPolynomial (Σ o, ι' o) O ⧸ pointIdeal O pt) := by
  classical
  let ren : MvPolynomial K' Φ →ₐ[O] MvPolynomial Λ Φ :=
    (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).restrictScalars O
  have hren : Function.Injective ren := rename_injective _ j.injective
  let F := ren.comp (pointConeMap O (fun p => pt (FieldNumbers.blockIncl j ι' p)))
  let z : MvPolynomial Λ Φ := C (pt ⟨b, l⟩) * X b
  have hLO : Function.Injective (algebraMap O (MvPolynomial Λ Φ)) := by
    rw [IsScalarTower.algebraMap_eq O Φ (MvPolynomial Λ Φ)]
    exact (C_injective Λ Φ).comp hO

  let ψ : MvPolynomial Λ Φ →+* Polynomial (MvPolynomial Λ Φ) :=
    eval₂Hom (Polynomial.C.comp C)
      (fun o => if o = b then Polynomial.C (C (pt ⟨b, l⟩)⁻¹) * Polynomial.X else Polynomial.C (X o))
  have hψren : ψ.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom =
      Polynomial.C.comp (rename j : MvPolynomial K' Φ →ₐ[Φ] MvPolynomial Λ Φ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [ψ]
    · intro o
      simp [ψ, hjb o]
  have hψz : ψ z = Polynomial.X := by
    simp only [ψ, z, map_mul, eval₂Hom_C, eval₂Hom_X', if_true, RingHom.comp_apply]
    rw [← mul_assoc, ← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one, one_mul]
  have hadj : Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ)) = F.range := Algebra.adjoin_eq _
  have htr : Transcendental (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) z := by
    rw [transcendental_iff]
    intro p hp
    have hψA : ψ.comp (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ)) =
        Polynomial.C.comp (algebraMap _ (MvPolynomial Λ Φ)) := by
      ext ⟨a, ha⟩ : 1
      obtain ⟨q, rfl⟩ : a ∈ F.range := hadj ▸ ha
      exact RingHom.congr_fun hψren _
    have h := congrArg ψ hp
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hψA, hψz, map_zero] at h
    exact Polynomial.map_injective (algebraMap (Algebra.adjoin O (F.range : Set (MvPolynomial Λ Φ))) (MvPolynomial Λ Φ))
      Subtype.val_injective (by rw [Polynomial.map_zero]; exact h)
  have hadd := AdjoinTrdegAdd.proof O (MvPolynomial Λ Φ) hLO (F.range : Set (MvPolynomial Λ Φ)) {z} Unit
    (fun _ => z) (by rintro _ ⟨_, rfl⟩; rfl) ((algebraicIndependent_unique_type_iff).2 htr)
    (fun a ha => by
      rw [Set.mem_singleton_iff.1 ha]
      exact isAlgebraic_algebraMap
        (⟨z, Algebra.subset_adjoin (Set.mem_union_right _ ⟨(), rfl⟩)⟩ :
          Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ Set.range fun _ : Unit => z)))
  rw [hadj, Fintype.card_unit, Nat.cast_one] at hadd
  have hle : Algebra.adjoin O ((F.range : Set (MvPolynomial Λ Φ)) ∪ {z}) ≤ (pointConeMap O pt).range := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (⟨q, rfl⟩ | hz)
    · exact ⟨rename (FieldNumbers.blockIncl j ι') q,
        (AlgHom.congr_fun (rename_comp_pointConeMap (O := O) ι' j pt) q).symm⟩
    · rw [Set.mem_singleton_iff.1 hz]
      exact ⟨X ⟨b, l⟩, by simp [pointConeMap, z]⟩
  rw [pointIdeal, pointIdeal, trdeg_quot_ker_eq_range _ _ hren,
    trdeg_quot_ker_eq_range (pointConeMap O pt) (AlgHom.id O _) (fun _ _ h => h), AlgHom.id_comp]
  change Algebra.trdeg O F.range + 1 ≤ _
  rw [← hadd]
  exact trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective _)

def zeroNewBlocks {O K : Type} [CommRing O] {ι : K → Type} {M M' : ℕ} :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → MRing ι O
  | ⟨some (some k), i⟩ => X ⟨k, i⟩
  | ⟨some none, _⟩ => 0
  | ⟨none, _⟩ => 0

theorem trdeg_flag_zero_le {O Ω K : Type} [CommRing O] [Field Ω] [Algebra O Ω] {ι : K → Type} {N M M' : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
    (y : (Σ k, ι k) → Ω) (w e : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    Algebra.trdeg O (MRing (bundleIdx (bundleIdx ι M) M') O ⧸ pointIdeal O (flagClosurePt y w e φ φ' t 0)) ≤
      Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) := by
  let ren : MvPolynomial K Φ →ₐ[O] MvPolynomial (Option (Option K)) Φ :=
    (rename (fun k : K => some (some k)) : MvPolynomial K Φ →ₐ[Φ] _).restrictScalars O
  have hren : Function.Injective ren :=
    rename_injective _ ((Option.some_injective _).comp (Option.some_injective _))
  have hG : pointConeMap O (flagClosurePt y w e φ φ' t 0) =
      (ren.comp (pointConeMap O (fun p => algebraMap Ω Φ (y p)))).comp (aeval (zeroNewBlocks (O := O))) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨(_ | _ | k), i⟩ <;>
      simp [ren, pointConeMap, flagClosurePt, pairProjCoord, projCoord, flagCoord, zeroNewBlocks]
  rw [← pointIdeal_algebraMap (O := O) (Φ := Φ) y]
  unfold pointIdeal
  rw [trdeg_quot_ker_eq_range (pointConeMap O (flagClosurePt y w e φ φ' t 0)) (AlgHom.id O _) (fun _ _ h => h),
    trdeg_quot_ker_eq_range (pointConeMap O (fun p => algebraMap Ω Φ (y p))) ren hren, AlgHom.id_comp, hG]
  exact trdeg_le_of_injective (Subalgebra.inclusion (AlgHom.range_comp_le_range _ _))
    (Subalgebra.inclusion_injective _)

end FlagProjTrdegLe


open FlagProjTrdegLe in
theorem FlagProjTrdegLe.proof (hTr : SegreFlagClosureTrdeg.Statement) : FlagProjTrdegLe.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ'
    Φ _ _ _ _ e t ht k hkN

  have hO : Function.Injective (algebraMap O Φ) := by
    rw [IsScalarTower.algebraMap_eq O Ω Φ]
    refine (FaithfulSMul.algebraMap_injective Ω Φ).comp ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have hy : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := by
      rw [Ideal.mem_comap, pointIdeal, RingHom.mem_ker, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, ha,
        map_zero]
    rw [hV.noTorsion] at hy
    simpa using hy
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 := trdeg_flag_zero_le (O := O) y w e φ φ' t
    simp only [Nat.cast_zero, add_zero]
    exact ⟨(trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t 0)).trans h0,
      (trdeg_blocks_le (O := O) (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t 0)).trans h0⟩
  · have hH := hTr O ϖ hϖ Ω K ι y d hV N E B B' hB w w' x x' f g hfl M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k hk hkN.le

    have hne : ∀ kk, ∃ i, y ⟨kk, i⟩ ≠ 0 := fun kk => by
      obtain ⟨i, hi⟩ := hV.multiProj.relevant kk
      refine ⟨i, fun h0 => hi ?_⟩
      rw [pointIdeal, RingHom.mem_ker]
      simp [pointConeMap, h0]
    choose c hc using hne
    have hyc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun kk _ => hc kk
    have hli := ht.linearIndependent
    obtain ⟨l', hl'⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ'
      (TwistedDualGensSpan.proof O Ω K ι y N E B' a₀' M' φ' hφ' c hyc) hk hkN.le
    obtain ⟨l, hl⟩ := SegreFlagClosureModel.exists_flag_ne_zero w e hli φ
      (TwistedDualGensSpan.proof O Ω K ι y N E B a₀ M φ hφ c hyc) hk hkN.le
    have key : ∀ a : Cardinal, a + 1 ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + ((k + 1 : ℕ) : Cardinal) →
        a ≤ Algebra.trdeg O (MRing ι O ⧸ pointIdeal O y) + (k : Cardinal) := by
      intro a ha
      rw [Nat.cast_add, Nat.cast_one, ← add_assoc] at ha
      exact Cardinal.add_one_le_add_one_iff.1 ha
    refine ⟨key _ ?_, key _ ?_⟩
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') Function.Embedding.some
        (flagClosurePt y w e φ φ' t k) none (fun o => Option.some_ne_none o) l' hl'
    · rw [← hH]
      exact trdeg_blocks_add_one_le hO (bundleIdx (bundleIdx ι M) M') secondFactorBlocks
        (flagClosurePt y w e φ φ' t k) (some none) (by rintro (_ | _) h <;> cases h) l hl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPrimeDimLeTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace PrimeDimLeTrdeg

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem proof : Statement := by
  intro O _ _ _ K _ _ ι _ P hPp hPC
  classical
  let F := FractionRing O

  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C : O →+* MRing ι O)
  have : IsLocalization M (MRing ι F) := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hdisj : Disjoint (M : Set (MRing ι O)) (P : Set (MRing ι O)) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hPC] at this
    exact nonZeroDivisors.ne_zero ha ((Submodule.mem_bot _).1 this)
  have hG : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M (MRing ι F) P hPp hdisj
  have hle : ringKrullDim (MRing ι O ⧸ P) ≤ ringKrullDim (MRing ι F ⧸ genFib P) + 1 :=
    GenericDimGe.proof.{0} O K ι P hPp hPC

  have hB : ringKrullDim (MRing ι F ⧸ genFib P) =
      (Algebra.trdeg F (MRing ι F ⧸ genFib P)).toENat :=
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F
  have hcomap : (genFib P).comap (algebraMap (MRing ι O) (MRing ι F)) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι F) hPp hdisj
  let φ : (MRing ι O ⧸ P) →+* (MRing ι F ⧸ genFib P) :=
    Ideal.quotientMap (genFib P) (algebraMap (MRing ι O) (MRing ι F)) hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let _ : Algebra (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := φ.toAlgebra
  have : IsScalarTower O (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change _ = φ (Ideal.Quotient.mk P (C a))
      simp [φ, Ideal.quotientMap_mk]
      rfl
  have : FaithfulSMul (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul O (MRing ι O ⧸ P) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).2 ((injective_iff_map_eq_zero (algebraMap O (MRing ι O ⧸ P))).2 fun a ha => ?_)
    have h : (C a : MRing ι O) ∈ P :=
      Ideal.Quotient.eq_zero_iff_mem.1 (show Ideal.Quotient.mk P (C a) = 0 from ha)
    have : a ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hPC] at this
    exact (Submodule.mem_bot _).1 this
  have : FaithfulSMul O F :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective O F)
  have : FaithfulSMul F (MRing ι F ⧸ genFib P) :=
    (faithfulSMul_iff_algebraMap_injective F (MRing ι F ⧸ genFib P)).2 (algebraMap F _).injective
  have : Algebra.IsAlgebraic O F := IsLocalization.isAlgebraic F (nonZeroDivisors O)
  have : Algebra.IsAlgebraic (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) := by
    refine ⟨fun b => ?_⟩
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M g
    have hspec := IsLocalization.mk'_spec (MRing ι F) s m
    let y := algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P (m : MRing ι O))
    have hy0 : y ≠ 0 := by
      refine (map_ne_zero_iff _ hφ).2 fun h => ?_
      exact Set.disjoint_left.1 hdisj m.2 (Ideal.Quotient.eq_zero_iff_mem.1 h)
    refine IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hy0) (isAlgebraic_algebraMap _) ?_
    have : y * Ideal.Quotient.mk (genFib P) (IsLocalization.mk' (MRing ι F) s m) =
        algebraMap (MRing ι O ⧸ P) (MRing ι F ⧸ genFib P) (Ideal.Quotient.mk P s) := by
      change φ _ * _ = φ _
      simp only [φ, Ideal.quotientMap_mk, ← map_mul]
      rw [mul_comm, hspec]
    rw [this]
    exact isAlgebraic_algebraMap _
  have h1 := trdeg_add_eq O F (A := MRing ι F ⧸ genFib P)
  have h2 := trdeg_add_eq O (MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P)
  rw [trdeg_eq_zero (R := O) (A := F), zero_add] at h1
  rw [trdeg_eq_zero (R := MRing ι O ⧸ P) (A := MRing ι F ⧸ genFib P), add_zero] at h2
  rw [hB, h1, ← h2] at hle
  exact hle

end PrimeDimLeTrdeg

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpLocRingFracCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def BlowUpOverLocFamilyFinite.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (J : Type) [Fintype J] (P : Ideal (MRing ι O)) (n : ℕ), IsModelOver P n →
    ∀ (N : K → ℕ) (u : J → MRing ι O), (∀ j, IsMultiHomog (u j) N) → (∃ j, u j ∉ P) →
    ∀ (c : K → ℕ) (x : MRing ι O), IsMultiHomog x c → x ∉ P →
    ∀ W : Ideal (MRing ι O), W ∈ (P ⊔ Ideal.span {x}).minimalPrimes → IsRelevant W →
      {Q : Ideal (MRing (extIdx ι J) O) | Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q ∧
        blowUpOf P u ≤ Q ∧ Q.comap (liftForm (ι := ι) (J := J) (R := O)) ≤ W}.Finite

def MultiHomogPrimeAvoid.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (S : Set (Ideal (MRing ι R))), S.Finite →
    (∀ Q ∈ S, Q.IsPrime ∧ IsMultiHomogIdeal Q ∧ IsRelevant Q) →
    ∃ (e : K → ℕ) (L : MRing ι R), IsMultiHomog L e ∧ (∀ k, 1 ≤ e k) ∧ ∀ Q ∈ S, L ∉ Q

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

