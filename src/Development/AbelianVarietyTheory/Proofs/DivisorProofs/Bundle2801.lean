module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldDoubleCosetClassSumToSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1331
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2778
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClasses
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.Regroup

theorem finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H),
      ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) :=
  GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets a ha

theorem unfold {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (T : Subgroup H) (Γ' : Subgroup G) (hΓ' : ∀ g, g ∈ Γ' ↔ ∃ t ∈ T, ι t = g)
    (K : Subgroup G) (u : G → ℂ) (hu : ∀ t ∈ T, ∀ k ∈ K, ∀ g, u (ι t * g * k) = u g)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h3 : ∀ x : G, {δ : H ⧸ T | u ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ δ : H ⧸ T, u ((ι (Quotient.out δ))⁻¹ * Quotient.out q) =
    ∑ᶠ q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G),
      ((Nat.card ↥(Γ' ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ * u (Quotient.out q) :=
  _root_.GlobalTheory.ClassSumUnfold.unfold_classSum ι hι Γ hΓ T Γ' hΓ' K u hu h1 h2 h3

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x :=
  GlobalTheory.T.definiteUnitaryFinitePart_mul_injective_range

theorem finite_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → Finite (DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n)))) :=
  GlobalTheory.T.finite_doubleCoset_rational_productOfLocalLevels

theorem finite_stab : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU (E := E) (n := n), Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) :=
  GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level

theorem finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ x : finU (E := E) (n := n), {γ : UE E n | globFn S f (x⁻¹ * finPt γ * x) ≠ 0}.Finite :=
  GlobalTheory.T.finite_rationalPoints_support_definiteUnitary_testFunction

theorem separable_of_globFn_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → ∀ (x : finU (E := E) (n := n)) (γ : UE E n), globFn S f (x⁻¹ * finPt γ * x) ≠ 0 → γ.1.val.charpoly.Separable :=
  GlobalTheory.T.separable_charpoly_of_testFunction_ne_zero_regularPlace

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

theorem support_conj_finite {G H : Type} [Group G] [Group H] (ι : H →* G) (Φ : G → ℂ) (x : G)
    (h4 : {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) (c : H) :
    {δ : H ⧸ twCent (MonoidHom.id H) c | (fun g : G => Φ (g⁻¹ * ι c * g)) ((ι (Quotient.out δ))⁻¹ * x) ≠ 0}.Finite := by
  refine Set.Finite.of_finite_image (f := fun δ : H ⧸ twCent (MonoidHom.id H) c => Quotient.out δ * c * (Quotient.out δ)⁻¹)
    (h4.subset ?_) ?_
  · rintro _ ⟨δ, hδ, rfl⟩
    show Φ (x⁻¹ * ι (Quotient.out δ * c * (Quotient.out δ)⁻¹) * x) ≠ 0
    have hδ' : Φ (((ι (Quotient.out δ))⁻¹ * x)⁻¹ * ι c * ((ι (Quotient.out δ))⁻¹ * x)) ≠ 0 := hδ
    convert hδ' using 2
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro δ₁ _ δ₂ _ e
    simp only at e
    rw [← Quotient.out_eq δ₁, ← Quotient.out_eq δ₂]
    apply QuotientGroup.eq.2
    change (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂)
    calc (Quotient.out δ₁)⁻¹ * Quotient.out δ₂ * c
        = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₂ * c * (Quotient.out δ₂)⁻¹) * Quotient.out δ₂ := by group
      _ = (Quotient.out δ₁)⁻¹ * (Quotient.out δ₁ * c * (Quotient.out δ₁)⁻¹) * Quotient.out δ₂ := by rw [e]
      _ = c * ((Quotient.out δ₁)⁻¹ * Quotient.out δ₂) := by group

theorem regroup_abstract {G H : Type} [Group G] [Group H] (ι : H →* G) (hι : Function.Injective ι) (Γ : Subgroup G)
    (hΓ : ∀ g, g ∈ Γ ↔ ∃ h, ι h = g) (K : Subgroup G) (Φ : G → ℂ) (ψ : H → ℂ)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (k⁻¹ * g * k) = Φ g) (hψ : ∀ a b, ψ (b⁻¹ * a * b) = ψ a)
    (h1 : Finite (DoubleCoset.Quotient (Γ : Set G) (K : Set G)))
    (h2 : ∀ x : G, Finite ↥(Γ ⊓ K.map (MulAut.conj x).toMonoidHom))
    (h4 : ∀ x : G, {γ : H | Φ (x⁻¹ * ι γ * x) ≠ 0}.Finite) :
    ∑ᶠ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ((Nat.card ↥(Γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
        ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ =
    ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep *
      ∑ᶠ q : DoubleCoset.Quotient ((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep) : Subgroup G) : Set G) (K : Set G),
        ((Nat.card ↥((Γ ⊓ twCent (MonoidHom.id G) (ι c.rep)) ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom) : ℂ))⁻¹ *
          Φ ((Quotient.out q)⁻¹ * ι c.rep * Quotient.out q) := by
  classical
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (Γ : Set G) (K : Set G))
  set D : DoubleCoset.Quotient (Γ : Set G) (K : Set G) → TwCl (MonoidHom.id H) → ℂ := fun q c =>
    ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) with hD

  have s1 : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      ∑ᶠ γ : H, Φ ((Quotient.out q)⁻¹ * ι γ * Quotient.out q) * ψ γ = ∑ᶠ c : TwCl (MonoidHom.id H), ψ c.rep * D q c := by
    intro q
    rw [finsum_classes _ ((h4 (Quotient.out q)).subset fun γ hγ => left_ne_zero_of_mul hγ)]
    refine finsum_congr fun c => ?_
    rw [hD, mul_finsum]
    refine finsum_congr fun δ => ?_
    have : ψ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = ψ c.rep := by
      simpa using hψ c.rep (Quotient.out δ)⁻¹
    rw [this, mul_comm]

  have hsupp : ∀ q : DoubleCoset.Quotient (Γ : Set G) (K : Set G),
      (Function.support fun c : TwCl (MonoidHom.id H) => ψ c.rep * D q c).Finite := by
    intro q
    refine ((h4 (Quotient.out q)).image (fun γ => (Quot.mk _ γ : TwCl (MonoidHom.id H)))).subset ?_
    intro (c : TwCl (MonoidHom.id H)) hc
    have hc' : D q c ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨δ, hδ⟩ : ∃ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
        Φ ((Quotient.out q)⁻¹ * ι (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) * Quotient.out q) ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hc' (by rw [hD]; simp only; rw [finsum_congr hn]; simp)
    refine ⟨_, hδ, ?_⟩
    change Quot.mk _ (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) = c
    exact (Quot.sound ⟨Quotient.out δ, by simp [mul_assoc]; rfl⟩).trans (Quot.out_eq c)
  simp_rw [s1]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [mul_finsum]
  rw [← finsum_sum_comm]
  · refine finsum_congr fun c => ?_
    have e2 := unfold ι hι Γ hΓ (twCent (MonoidHom.id H) c.rep) (Γ ⊓ twCent (MonoidHom.id G) (ι c.rep))
      (fun g => by
        constructor
        · rintro ⟨hg, hc⟩
          obtain ⟨h, rfl⟩ := (hΓ g).1 hg
          refine ⟨h, hι ?_, rfl⟩
          change ι h * ι c.rep = ι c.rep * ι h at hc
          change ι (h * c.rep) = ι (c.rep * h)
          rw [map_mul, map_mul, hc]
        · rintro ⟨t, ht, rfl⟩
          refine ⟨(hΓ _).2 ⟨t, rfl⟩, ?_⟩
          change ι t * ι c.rep = ι c.rep * ι t
          have ht' : t * c.rep = c.rep * t := ht
          rw [← map_mul, ht', map_mul])
      K (fun g => Φ (g⁻¹ * ι c.rep * g))
      (fun t ht k hk g => by
        have ht' : t * c.rep = c.rep * t := ht
        simp only [_root_.mul_inv_rev]
        have : (k⁻¹ * (g⁻¹ * (ι t)⁻¹) * ι c.rep * (ι t * g * k)) = k⁻¹ * (g⁻¹ * ι c.rep * g) * k := by
          have : (ι t)⁻¹ * ι c.rep * ι t = ι c.rep := by
            rw [← map_inv, ← map_mul, ← map_mul, mul_assoc, ← ht', inv_mul_cancel_left]
          calc _ = k⁻¹ * (g⁻¹ * ((ι t)⁻¹ * ι c.rep * ι t) * g) * k := by group
            _ = _ := by rw [this]
        rw [this, hΦ k hk])
      h1 h2 (fun x => support_conj_finite ι Φ x (h4 x) c.rep)
    rw [← mul_finsum, ← e2, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hD]
    simp only
    rw [mul_left_comm]
    congr 2
    refine finsum_congr fun δ => ?_
    congr 1
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    group
  · intro q _
    exact (hsupp q).subset fun c hc => right_ne_zero_of_mul hc

end GlobalTheory.BCT.Regroup

namespace GlobalTheory.BCT.Regroup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem toSub_conj {G : Type} [Group G] (U : Subgroup G) (k : U) (y : G) :
    toSub U ((k : G)⁻¹ * y * k) = k⁻¹ * toSub U y * k := by
  unfold toSub
  by_cases hy : y ∈ U
  · rw [dite_eq_left hy, dite_eq_left (mul_mem (mul_mem (inv_mem k.2) hy) k.2)]
    ext
    simp
  · rw [dite_eq_right hy, dite_eq_right]
    · simp
    · intro h
      apply hy
      have := mul_mem (mul_mem k.2 h) (inv_mem k.2)
      simpa [mul_assoc] using this

theorem globFn_conj (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
    (hf : ∀ w, IsHecke (K' w) (f w)) (k : finU (E := E) (n := n)) (hk : k ∈ globLev S K') (g : finU (E := E) (n := n)) :
    globFn S f (k⁻¹ * g * k) = globFn S f g := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  have hkw : cLoc w k.1 ∈ (K' w).map (UL n w).subtype := by
    have h1 := Subgroup.mem_iInf.1 hk w
    exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 hw)
  obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hkw
  have e2 : cLoc w (k⁻¹ * g * k).1 = ((k' : UL n w) : GLw n w)⁻¹ * cLoc w g.1 * (k' : GLw n w) := by
    have e' : (k' : GLw n w) = cLoc w k.1 := e
    rw [e']
    simp
  rw [e2, toSub_conj, ((hf w).2 k' hk' _).2, ((hf w).2 k'⁻¹ (inv_mem hk') _).1]

theorem chW_conj (lam : InfinitePlace E → DomWeight n) (a b : UE E n) :
    chW lam (b⁻¹ * a * b).1.val.charpoly = chW lam a.1.val.charpoly := by
  congr 1
  have : (b⁻¹ * a * b).1.val = (b.1.val)⁻¹ * a.1.val * b.1.val := by
    simp [Matrix.coe_units_inv]
  rw [this]
  have h := Matrix.charpoly_units_conj (b.1)⁻¹ a.1.val
  simpa [Matrix.coe_units_inv] using h

theorem kernSum_eq_finsum_classes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → kernSum S lam K' f = ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then chW lam c.rep.1.val.charpoly * clsSum S K' f c.rep else 0 := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  obtain ⟨hmul, hinj, hmem⟩ := finPt_props E n
  let ι : UE E n →* finU (E := E) (n := n) := MonoidHom.mk' finPt hmul
  have key : ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly =
    ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), chW lam c.rep.1.val.charpoly *
      ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU (E := E) (n := n))) : Set (finU (E := E) (n := n)))
        (globLev S K' : Set (finU (E := E) (n := n))),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) :=
    regroup_abstract ι hinj (ratFinU E n) hmem (globLev S K') (globFn S f) (fun γ => chW lam γ.1.val.charpoly)
      (globFn_conj S K' f hf.1) (chW_conj lam) (finite_classes E hU n hn S hS K' hK) (finite_stab E hU n hn S hS K' hK)
      (finite_supp E hU n hn S hS K' hK f hf)
  obtain ⟨w, hw, hsep⟩ := hreg
  unfold kernSum
  rw [key, mul_finsum]
  refine finsum_congr fun c => ?_
  split_ifs with hc
  · rw [clsSum]
    ring
  · have h0 : ∀ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt c.rep) : Subgroup (finU (E := E) (n := n))) :
        Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))),
        globFn S f ((Quotient.out q)⁻¹ * finPt c.rep * Quotient.out q) = 0 := fun q => by
      by_contra h
      exact hc (separable_of_globFn_ne_zero E n S K' f hf w hw hsep _ _ h)
    simp [h0]

end GlobalTheory.BCT.Regroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirst
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.ShortSpanUnitCover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem abs_kap_le (Dw : Datum H) (τ : Psi H) (k : Fin (Dw.p + Dw.q)) :
    |(FlagTan.kap Dw τ k : ℝ)| ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
  have hk := k.2
  have h : |FlagTan.kap Dw τ k| ≤ ((Dw.p + Dw.q : ℕ) : ℤ) := by
    simp only [FlagTan.kap]
    rw [abs_le]
    split_ifs <;> push_cast <;> constructor <;> omega
  rw [← Int.cast_abs]; exact_mod_cast h

theorem sum_abs_kap_le (Dw : Datum H) :
    ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ (Fintype.card (Psi H) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) ^ 2 := by
  calc ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| ≤ ∑ _τ : Psi H, ∑ _k : Fin (Dw.p + Dw.q), ((Dw.p + Dw.q : ℕ) : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => abs_kap_le Dw τ k
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sum_abs_weightZero_le_components (Dw : Datum H) (P : WtPar Dw) :
    ∑ τ, ∑ k, |(P.wt 0 τ k : ℝ)| ≤ ∑ τ, ∑ k, |(FlagTan.kap Dw τ k : ℝ)| + ∑ τ, ∑ k, |(P.u₂ τ k : ℝ)| +
      (FlagTan.dimFlag Dw : ℝ) * ∑ τ, ∑ k, |(P.u₁ τ k : ℝ)| := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => ?_
  have e : (P.wt 0 τ k : ℝ) = (FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ) + (FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ) := by
    simp only [WtPar.wt, WtPar.uc, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply]
    simp only [nsmul_eq_mul]
    push_cast; ring
  rw [e]
  calc _ ≤ |(FlagTan.kap Dw τ k : ℝ) + (P.u₂ τ k : ℝ)| + |(FlagTan.dimFlag Dw : ℝ) * (P.u₁ τ k : ℝ)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, Nat.abs_cast]
      linarith [abs_add_le (FlagTan.kap Dw τ k : ℝ) (P.u₂ τ k : ℝ)]

theorem consecutiveGap_weightZero_ge (Dw : Datum H) (P : WtPar Dw) (τ : Psi H) {k : ℕ} (h : k + 1 < Dw.p + Dw.q) (g : ℤ)
    (hg : g ≤ gap (P.u₁ τ) k) : ((FlagTan.dimFlag Dw : ℤ) + 1) * g - 2 ≤ gap (P.wt 0 τ) k := by
  have hr := (P.gap_rem τ k).1
  have hk : -2 ≤ FlagTan.kap Dw τ ⟨k, by omega⟩ - FlagTan.kap Dw τ ⟨k + 1, h⟩ := by
    simp only [FlagTan.kap, Fin.val_mk]
    split_ifs <;> push_cast <;> omega
  rw [gap, dite_eq_left h] at hr hg ⊢
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, zero_smul, add_zero, Pi.zero_apply] at hr ⊢
  simp only [nsmul_eq_mul] at hr ⊢
  have hD : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hg hD]

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover

theorem final_le {C Zr S Dc PP X abelian₂ L : ℝ} (hC : 0 ≤ C) (hL : 4 * C + 1 ≤ L) (hZL : L ≤ Zr) (hPP : Zr ^ 12 ≤ PP)
    (hDc : 1 ≤ Dc) (hX : 1 ≤ X) (hS : S ≤ 3 * Dc * Zr ^ 2 * X) (hLam : Real.log abelian₂ ≤ C * (Zr ^ 3 * S + Zr ^ 5)) :
    Real.log abelian₂ ≤ Dc * PP * X := by
  have hZ1 : 1 ≤ Zr := by linarith
  have hZ0 : 0 ≤ Zr := by linarith
  have hZ5 : 0 ≤ Zr ^ 5 := by positivity
  have hDX : 1 ≤ Dc * X := by nlinarith
  have h1 : Zr ^ 3 * S ≤ 3 * (Dc * X) * Zr ^ 5 := by
    have := mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ Zr ^ 3)
    nlinarith
  have h2 : Zr ^ 5 ≤ (Dc * X) * Zr ^ 5 := by nlinarith
  have h3 : C * (Zr ^ 3 * S + Zr ^ 5) ≤ (Dc * X) * (4 * C * Zr ^ 5) := by
    have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC
    nlinarith
  have h4 : 4 * C * Zr ^ 5 ≤ PP := by
    have a : Zr ≤ Zr ^ 7 := by
      calc Zr = Zr ^ 1 := (pow_one _).symm
        _ ≤ Zr ^ 7 := pow_le_pow_right₀ hZ1 (by norm_num)
    have b : 4 * C ≤ Zr ^ 7 := by linarith
    have c : 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := mul_le_mul_of_nonneg_right b hZ5
    calc 4 * C * Zr ^ 5 ≤ Zr ^ 7 * Zr ^ 5 := c
      _ = Zr ^ 12 := by ring
      _ ≤ PP := hPP
  have h5 : (Dc * X) * (4 * C * Zr ^ 5) ≤ (Dc * X) * PP := mul_le_mul_of_nonneg_left h4 (by linarith)
  calc Real.log abelian₂ ≤ _ := hLam
    _ ≤ _ := h3
    _ ≤ _ := h5
    _ = Dc * PP * X := by ring

theorem sum_le {S K A1 A2 Dc W : ℝ} (hSle : S ≤ K + A2 + Dc * A1) (hK : K ≤ W) (h1 : A1 ≤ W) (h2 : A2 ≤ W)
    (hDc : 1 ≤ Dc) (hW : 0 ≤ W) : S ≤ 3 * Dc * W := by
  have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ Dc)
  nlinarith

theorem log_sum_le {S k fr L : ℝ} (hS0 : 0 ≤ S) (hSk : S ≤ (fr * L) ^ 2 * k) (hk : Real.log k ≤ 2 * L)
    (hfr : Real.log fr ≤ L) (hL1 : 1 ≤ L) (hfr1 : 1 ≤ fr) : Real.log S ≤ 10 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hZ : 0 < fr * L := by positivity
  have hk0 : 0 < k := by
    by_contra hk0
    push_neg at hk0
    have : (fr * L) ^ 2 * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk0
    linarith
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  calc Real.log S ≤ Real.log ((fr * L) ^ 2 * k) := Real.log_le_log h hSk
    _ = 2 * (Real.log fr + Real.log L) + Real.log k := by
      rw [Real.log_mul (by positivity) hk0.ne', Real.log_pow, Real.log_mul (by linarith) (by linarith)]; push_cast; ring
    _ ≤ 10 * L := by linarith

end GlobalTheory.CovTop.ShortSpanUnitCover

namespace GlobalTheory.CovTop.ShortSpanUnitCover


end GlobalTheory.CovTop.ShortSpanUnitCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTMulConjLe
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section
namespace GlobalTheory.BotPairSmallTw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem modT_ne_bot (G : GridData L sc) (t : T) : modT G t ≠ ⊥ := by
  unfold modT
  exact mul_ne_zero (condE_ne_bot G.pl) (Finset.prod_ne_zero_iff.2 fun w _ => w.ne_bot)

theorem absNorm_modT (G : GridData L sc) (t : T) : Ideal.absNorm (modT G t) = levQ G.pl * Qn G t := by
  rw [modT, map_mul, map_prod, GlobalTheory.ModulusNorm.absNorm_condE, Qn]

theorem hatId_mono {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : hatId D I ≤ hatId D J :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, s, hs, e⟩ => ⟨b, h hb, s, hs, e⟩

theorem modT_mul_conj_le (G : GridData L sc) (t : T) :
    modT G t * D.host.conj • modT G t ≤ condE G.pl * D.host.conj • condE G.pl := by
  have h : modT G t ≤ condE G.pl := by
    show condE G.pl * _ ≤ _
    exact Ideal.mul_le_inf.trans inf_le_left
  exact Ideal.mul_mono h (Ideal.map_mono h)

end GlobalTheory.BotPairSmallTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedDegenerationDataIsoOfMumfordBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedDegenerationData_iso_of_mumfordBundle_iso : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ [Module O D'.toPre.X] (o' : D'.toPre.OAct O) (oA' : A'.OAct O), U'.toUnifPre.OLinear O o' oA' oG → LBIso (abelian₂ G U'.LG.L) (abelian₂ G U.LG.L) → ∃ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom ∧ Over₀ U'.toUnifPre U.toUnifPre (𝟙 G) Φ.hom ∧ OnTorus U'.toUnifPre U.toUnifPre (𝟙 G) xe.symm ∧ (∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.SameLam.iso_of_lbIso_lam | exact GlobalTheory.Mum.SameLam.iso_of_lbIso_lam | (intros; apply GlobalTheory.Mum.SameLam.iso_of_lbIso_lam <;> assumption)
end

