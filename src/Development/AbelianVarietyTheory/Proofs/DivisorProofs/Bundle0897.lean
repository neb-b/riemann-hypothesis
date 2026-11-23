module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import GroundTheory.Brauer.TensorSimple
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0865
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackSpreadsToIntermediateSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegSpreadCore

theorem spMap_subtype_eq {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) :
    spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem spMap_inclusion_eq {S : Type} [CommRing S] {R₀ R₁ R₂ : Subring S} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) (h : R₀ ≤ R₂) :
    spMap (Subring.inclusion h) = spMap (Subring.inclusion h₂) ≫ spMap (Subring.inclusion h₁) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

theorem siegPB_spread_subring : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE), SiegPB e d₀ (spMap R₀.subtype) → SiegPB e u (spMap R₀.subtype ≫ h₀) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁), SiegPB d₁ d₀ (spMap (Subring.inclusion hle)) → SiegPB d₁ u (spMap (Subring.inclusion hle) ≫ h₀) := by
  intro g n B _ ζ S _ R₀ s₀ d₀ Y sY u h₀ sE e hd hu
  classical
  obtain ⟨φd, φd₂, hφd, hsd, hwd, hld⟩ := hd
  obtain ⟨φu, φu₂, hφu, hsu, hwu, hlu⟩ := hu
  haveI := d₀.ab.smooth; haveI := d₀.ab.proper; haveI := u.ab.smooth; haveI := u.ab.proper
  have hZ : IsPullback (pullback.lift φu (e.A.hom ≫ spMap R₀.subtype) (by rw [hφu.1.w, Category.assoc]))
      e.A.hom (pullback.snd u.A.hom h₀) (spMap R₀.subtype) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback u.A.hom h₀)
    rw [pullback.lift_fst]; exact hφu.1
  obtain ⟨F₁, hF₁⟩ := _root_.GlobalTheory.iso_spreads_to_subring S R₀ e.A.left d₀.A.left (pullback u.A.hom h₀) e.A.hom d₀.A.hom
    (pullback.snd u.A.hom h₀) φd _ hφd.1 hZ
  let R' : Subring S := Subring.closure ((R₀ : Set S) ∪ (F₁ : Set S))
  have hR0 : R₀ ≤ R' := fun x hx => Subring.subset_closure (Or.inl hx)
  have hF1 : (F₁ : Set S) ⊆ R' := fun x hx => Subring.subset_closure (Or.inr hx)
  obtain ⟨⟨d', hd'⟩, -⟩ := GlobalTheory.siegPre_pullback g n B ζ (Sp R₀) (Sp R') s₀
    (spMap (Subring.inclusion hR0) ≫ s₀) (spMap (Subring.inclusion hR0)) d₀ rfl
  have hd'c := hd'
  obtain ⟨φ', φ'₂, hφ', hs', hw', hl'⟩ := hd'
  have eR' := spMap_subtype_eq hR0
  let j : e.A.left ⟶ d'.A.left := hφ'.1.lift φd (e.A.hom ≫ spMap R'.subtype)
    (by rw [hφd.1.w, eR', Category.assoc])
  have hj1 : j ≫ φ' = φd := hφ'.1.lift_fst _ _ _
  have hj2 : j ≫ d'.A.hom = e.A.hom ≫ spMap R'.subtype := hφ'.1.lift_snd _ _ _
  obtain ⟨ψZ, hψZ1, hψZ2⟩ := hF₁ R' hR0 hF1 d'.A.left d'.A.hom φ' j hφ'.1 hj1 hj2
  let ψ := ψZ ≫ pullback.fst u.A.hom h₀
  have hψ : IsPullback ψ d'.A.hom u.A.hom (spMap (Subring.inclusion hR0) ≫ h₀) :=
    hψZ2.paste_horiz (IsPullback.of_hasPullback _ _)
  have hjψ : j ≫ ψ = φu := by
    show j ≫ ψZ ≫ pullback.fst u.A.hom h₀ = φu
    rw [reassoc_of% hψZ1, pullback.lift_fst]
  have eh : spMap R'.subtype ≫ spMap (Subring.inclusion hR0) ≫ h₀ = spMap R₀.subtype ≫ h₀ := by
    rw [← Category.assoc, ← eR']
  have gj : IsGrpPullback e.A d'.A (spMap R'.subtype) j :=
    IsGrpPullback.cancel hφ' (by rw [hj1, ← eR']; exact hφd) hj2
  obtain ⟨j₂, hsj⟩ := GlobalTheory.SiegDesc.exists_isSquare hj2
  have hj₂ : j₂ ≫ φ'₂ = φd₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst d₀.A d₀.A).left = _ ≫ (fst d₀.A d₀.A).left
      rw [Category.assoc, hs'.1, ← Category.assoc, hsj.1, Category.assoc, hj1, hsd.1]
    · show (_ ≫ _) ≫ (snd d₀.A d₀.A).left = _ ≫ (snd d₀.A d₀.A).left
      rw [Category.assoc, hs'.2, ← Category.assoc, hsj.2, Category.assoc, hj1, hsd.2]
  have hwj : LBIso e.P (d'.P.pull j₂) := by
    rw [← hj₂] at hwd
    exact (hwd.trans e.isLB (pull_isLB d₀.isLB _) (pull_isLB (pull_isLB d₀.isLB _) _)
      (GlobalTheory.SiegelPullComp.iso_pull_pull d₀.isLB φ'₂ j₂).symm).trans e.isLB
      (pull_isLB (pull_isLB d₀.isLB _) _) (pull_isLB d'.isLB _) (GlobalTheory.SiegelPullComp.iso_pull j₂ hw').symm
  have hlj : ∀ a, (e.lev a).left ≫ j = spMap R'.subtype ≫ (d'.lev a).left := by
    intro a
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hj1, hld a, Category.assoc, hl' a, ← Category.assoc, ← eR']
    · have a₁ : (e.lev a).left ≫ e.A.hom = 𝟙 _ := Over.w (e.lev a)
      have a₂ : (d'.lev a).left ≫ d'.A.hom = 𝟙 _ := Over.w (d'.lev a)
      rw [Category.assoc, hj2, reassoc_of% a₁, Category.assoc, a₂]
      simp
  obtain ⟨F₂, hF₂⟩ := _root_.GlobalTheory.GrpMulSpread.isGrpPullback_comp_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ gj (by rw [eh, hjψ]; exact hφu)
  obtain ⟨F₃, hF₃⟩ := _root_.GlobalTheory.SiegBundleSpread.lbIso_spread g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ j₂ φu₂ gj.1 hsj hwj
    (by rw [hjψ]; exact hsu) hwu
  obtain ⟨F₄, hF₄⟩ := _root_.GlobalTheory.siegel_levels_spread_to_subring g n B ζ S R' _ d' Y sY u _ ψ sE e j hψ hlj
    (fun a => by rw [eh, hjψ]; exact hlu a)
  refine ⟨F₁ ∪ F₂ ∪ F₃ ∪ F₄, fun R₁ hle hF s₁ d₁ hd₁ => ?_⟩
  have hsub : ∀ G : Finset S, G ⊆ F₁ ∪ F₂ ∪ F₃ ∪ F₄ → (G : Set S) ⊆ R₁ :=
    fun G h => (Finset.coe_subset.2 h).trans hF
  have hR'1 : R' ≤ R₁ := Subring.closure_le.2 (Set.union_subset hle
    (hsub F₁ (by intro x; simp only [Finset.mem_union]; tauto)))
  have eR1 := spMap_inclusion_eq hR0 hR'1 hle
  have hd₁' : SiegPB d₁ d' (spMap (Subring.inclusion hR'1)) :=
    GlobalTheory.SiegelPullComp.pb_cancel hd'c (by rw [← eR1]; exact hd₁)
  obtain ⟨φ₁, φ₁₂, hφ₁, hs₁, hw₁, hl₁⟩ := hd₁'
  have gm := hF₂ R₁ hR'1 (hsub F₂ (by intro x; simp only [Finset.mem_union]; tauto)) d₁.A φ₁ hφ₁
  have e2 : spMap (Subring.inclusion hR'1) ≫ spMap (Subring.inclusion hR0) ≫ h₀ =
      spMap (Subring.inclusion hle) ≫ h₀ := by rw [eR1, Category.assoc]
  rw [e2] at gm
  obtain ⟨χ₂, hχ⟩ := GlobalTheory.SiegDesc.exists_isSquare gm.1.w
  refine ⟨φ₁ ≫ ψ, χ₂, gm, hχ, hF₃ R₁ hR'1 (hsub F₃ (by intro x; simp only [Finset.mem_union]; tauto))
    s₁ d₁ φ₁ φ₁₂ χ₂ hφ₁.1 hs₁ hw₁ hχ, fun a => ?_⟩
  have := hF₄ R₁ hR'1 (hsub F₄ (by intro x; simp only [Finset.mem_union]; tauto)) s₁ d₁ φ₁
    (by rw [e2]; exact gm) hl₁ a
  rw [e2] at this
  exact this

end GlobalTheory.SiegSpreadCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairAdelicProdUnramifiedEmbeddingInjec
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem finiteAdeleRingAway_nontrivial (p : ℕ) [Fact p.Prime] : Nontrivial (AfP p) := by
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (p + 1)
  have hqi : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  let v0 : IsDedekindDomain.HeightOneSpectrum ℤ :=
    { asIdeal := Ideal.span {(q : ℤ)}
      isPrime := (Ideal.span_singleton_prime hqi.ne_zero).mpr hqi
      ne_bot := by simpa using hqi.ne_zero }
  have hne : v0.asIdeal ≠ Ideal.span {(p : ℤ)} := by
    intro h
    change Ideal.span {(q : ℤ)} = Ideal.span {(p : ℤ)} at h
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at h
    simp at h
    omega
  exact (AfP.eval (p := p) ⟨v0, hne⟩).toRingHom.domain_nontrivial

theorem pair_toAf_injective {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) : Function.Injective (P.toAf x t hx) := by
  haveI := finiteAdeleRingAway_nontrivial p
  intro a b h
  have h0 := congrArg Subtype.val h
  have h1 := congrArg Prod.fst h0
  have h2 := congrArg Prod.snd h0
  simp only [Pair.toAf, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, Prod.map_fst, Prod.map_snd,
    Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at h1 h2
  have e1 : (a : G.Cˣ × ℚˣ).1 = (b : G.Cˣ × ℚˣ).1 := by
    apply Units.ext
    have := congrArg Units.val h1
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap ℚ (AfP p)).injective this
  have e2 : (a : G.Cˣ × ℚˣ).2 = (b : G.Cˣ × ℚˣ).2 := by
    apply Units.ext
    have := congrArg Units.val h2
    simp only [Units.coe_map, MonoidHom.coe_coe] at this
    exact (algebraMap ℚ (AfP p)).injective this
  exact Subtype.ext (Prod.ext e1 e2)

theorem pair_embedding_injective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (r : ℕ) (z : Gr G r), Function.Injective ((P.toAf x t hx).prod (P.toQr r z)) := by
  intro p _ G P x t hx r z a b h
  exact pair_toAf_injective P x t hx (congrArg Prod.fst h)

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairGramInvCongruent
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem psiR_tmul (G : HTGroup p) (v : InfinitePlace G.F) (r : ℝ) (c : G.C) :
    G.psiR v (r ⊗ₜ c) = r • G.psi v c := by
  rw [Algebra.smul_def]
  first
    | (unfold HTGroup.psiR; erw [Algebra.TensorProduct.lift_tmul]; rfl)
    | exact Algebra.TensorProduct.lift_tmul _ _ _ r c

theorem psiR_starT (G : HTGroup p) (v : InfinitePlace G.F) (x : ℝ ⊗[ℚ] G.C) :
    G.psiR v (starT G.star ℝ x).unop = (G.gram v)⁻¹ * (G.psiR v x)ᴴ * G.gram v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    rw [starT_tmul, psiR_tmul, psiR_tmul]
    rw [G.psi_star, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul]
  | add x y hx hy =>
    simp only [map_add (f := _), MulOpposite.unop_add, hx, hy, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem Pair.gram_psi_inv_congr : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    ∃ Z : GL (Fin G.n) ℂ, (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) =
      (Z : Matrix (Fin G.n) (Fin G.n) ℂ)ᴴ * G.gram v * (Z : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  intro p _ G P v
  obtain ⟨z, hz⟩ := P.trivR
  refine ⟨Units.map (G.psiR v).toMonoidHom z, ?_⟩
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := G.psiR v (z : ℝ ⊗[ℚ] G.C) with hZm
  change G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) = Zmᴴ * G.gram v * Zm
  have hb : G.psiR v (inC G ℝ (P.β : G.C)) = G.psi v (P.β : G.C) := by
    change G.psiR v ((1 : ℝ) ⊗ₜ (P.β : G.C)) = _
    rw [psiR_tmul, one_smul]
  have h1 := congrArg (G.psiR v) hz
  rw [map_mul, map_mul, psiR_starT, hb] at h1
  simp only [Units.val_one, map_one] at h1
  rw [← hZm] at h1
  have hg : IsUnit (G.gram v).det := isUnit_iff_ne_zero.2 (G.gram_det v)
  set M := G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)
  have hMb : M * G.psi v (P.β : G.C) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm) = 1 := by
    have := mul_eq_one_comm.1 (by simpa [Matrix.mul_assoc] using h1 :
      Zm * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v)) = 1)
    simpa [Matrix.mul_assoc] using this
  have h3 : M = (G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm := by
    calc M = M * (G.psi v (P.β : G.C) * ((G.gram v)⁻¹ * Zmᴴ * G.gram v * Zm)) := by rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hMb, Matrix.one_mul]
  rw [h3]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hg, Matrix.one_mul]

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairHermitianFormInvertibleSimilitude
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem pair_form_laws : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F),
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).IsHermitian ∧
    (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)).det ≠ 0 ∧
    (G.psi v P.γ)ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v P.γ =
      ((P.c : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  intro p _ G P v
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu

  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]

  have hshb : sh G ((P.β⁻¹ : G.Cˣ) : G.C) = ((P.β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((P.β⁻¹ : G.Cˣ) : G.C) * sh G (P.β : G.C) = 1 := by
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    rw [P.sym] at h1
    calc sh G ((P.β⁻¹ : G.Cˣ) : G.C)
        = sh G ((P.β⁻¹ : G.Cˣ) : G.C) * (P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]

  have hu : sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ =
      algebraMap ℚ G.C (P.c : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (P.γ * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (P.γ : G.C) * P.β * (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ)
        = ((P.γ : G.C) * P.β * sh G (P.γ : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ := by
          simp only [mul_assoc]
      _ = (P.c : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [P.sim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (P.c : ℚ) • ((P.γ : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  ·
    change (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C))ᴴ = _
    rw [conjTranspose_mul, (G.gram_herm v).eq, hH, hshb, mul_assoc, hgg', mul_one]
  ·
    have hb : IsUnit (G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := (Units.isUnit _).map (G.psi v)
    rw [det_mul]
    exact mul_ne_zero (G.gram_det v) ((Matrix.isUnit_iff_isUnit_det _).mp hb).ne_zero
  ·
    rw [hH]
    calc G.gram v * G.psi v (sh G (P.γ : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
          G.psi v P.γ
        = G.gram v * (G.psi v (sh G (P.γ : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
            G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v P.γ) := by simp only [mul_assoc]
      _ = G.gram v * G.psi v (sh G (P.γ : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * P.γ) := by
          rw [hgg', mul_one, map_mul, map_mul]
      _ = G.gram v * ((P.c : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
      _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

theorem charpoly_rho_eq_map_pol (G : HTGroup p) (P : Pair G) (w : Fin G.m) :
    (G.rho w (P.γ : G.C)).charpoly = P.pol.map (G.embW w) := by
  letI : Algebra G.F (G.Fw w) := (G.embW w).toAlgebra
  have hg : ∀ a, G.rho w (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) (G.Fw w)) a :=
    fun a => by rw [G.rho_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) (G.Fw w) := { G.rho w with commutes' := hg }
  let L : G.Fw w ⊗[G.F] G.C →ₐ[G.Fw w] Matrix (Fin G.n) (Fin G.n) (G.Fw w) :=
    Algebra.TensorProduct.lift (Algebra.ofId (G.Fw w) _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : G.Fw w) ⊗ₜ x) = G.rho w x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : G.Fw w) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  set γ : G.C := (P.γ : G.C) with hγ
  have hdeg : (minpoly G.F γ).natDegree = G.n := P.reg.1
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent (G.Fw w) (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent (G.Fw w) (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.rho w γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : G.Fw w) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral (G.Fw w) (G.rho w γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly (G.Fw w) (G.rho w γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.rho w γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.rho w γ) (P.pol.map (G.embW w)) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.rho w γ) ((minpoly G.F γ).map (algebraMap G.F (G.Fw w))) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : (P.pol.map (G.embW w)).Monic := (minpoly.monic hFint).map _
  have hn1 : (P.pol.map (G.embW w)).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem atP_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G),
    (∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w)) ∧ regular₂ G P.atP ∧
      ∀ y : P.cent, locC G y.1 ∈ Subgroup.centralizer {P.atP} := by
  intro p _ G P
  have h1 : ∀ w, (P.atP.2 w).val.charpoly = P.pol.map (G.embW w) := fun w => charpoly_rho_eq_map_pol G P w
  refine ⟨h1, fun w => ?_, fun y => ?_⟩
  · show (P.atP.2 w).val.charpoly.Separable
    rw [h1]
    exact P.reg.2.map
  · rw [Subgroup.mem_centralizer_singleton_iff]
    show locC G y.1 * locC G (P.γ, P.c) = locC G (P.γ, P.c) * locC G y.1
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext y.2.1 (mul_comm _ _)

end GlobalTheory.LKMid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMapRootEqSumCount
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

theorem sum_map_root_eq_sum_count {n : ℕ} (l : List (Fin n × Fin n)) :
    (l.map fun p : Fin n × Fin n => root p.1 p.2).sum
      = ∑ a, ∑ b, (l.count (a, b) : ℝ) • root a b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.count_cons, Nat.cast_add, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨x, y⟩ := p
    simp only [beq_iff_eq, Prod.mk.injEq]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp

theorem root_word_count_letters : ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = false ∧ ε p.2 = true) → μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = Λ + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε μ Λ l hl hsum
  refine ⟨fun a b => l.count (b, a), ?_, ?_⟩
  · intro a b h
    have hm : (b, a) ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨(hl _ hm).2, (hl _ hm).1⟩
  · rw [sum_map_root_eq_sum_count] at hsum
    have key : ∑ a, ∑ b, ((l.count (b, a) : ℕ) : ℝ) • root a b
        = - ∑ a, ∑ b, ((l.count (a, b) : ℕ) : ℝ) • root a b := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have : root b a = - root a b := by
        unfold root; abel
      rw [this, smul_neg]
    rw [key, ← hsum]; abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThPBilinearHeis
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_bilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → ∀ a b : ℂ, thP X hq bas idx (a • φ + b • φ') P x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ' P x) ∧ (∀ (P' : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (a b : ℂ), thP X hq bas idx φ (a • P + b • P') x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ P' x) ∧ ∀ y : Matrix (Fin n) (Fin r) E, thP X hq bas idx (heisG X bas y φ) P x = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hq idx) (fun z => cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) 0 := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq x hd φ hφ P
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun ψ hψ a b => ?_, fun Q a b => ?_, fun y => ?_⟩
  · have h4 := (thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd ψ hψ).2.1
    have e1 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h2 a 0
    have e2 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h4 b 0
    have e3 := GlobalTheory.Jet.polyDeriv_add_fun P (letterDir X hq idx) (h2.const_smul a) (h4.const_smul b) 0
    unfold thP
    rw [((h3 ψ hψ).1 a b).2, ← e1, ← e2]
    exact e3
  · unfold thP
    rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  · unfold thP
    rw [funext fun z => (h1 y z).2]

end GlobalTheory.AdTh
end

