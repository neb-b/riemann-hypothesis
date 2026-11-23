module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralProductGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
section
noncomputable section

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.StTwTens

theorem finsum_prod_mul' {α β : Type} (u : α → ℂ) (v : β → ℂ) :
    ∑ᶠ z : α × β, u z.1 * v z.2 = (∑ᶠ a, u a) * ∑ᶠ b, v b := by
  have hsupp : Function.support (fun z : α × β => u z.1 * v z.2) =
      Function.support u ×ˢ Function.support v := by
    ext z
    simp only [Function.mem_support, Set.mem_prod, ne_eq, mul_eq_zero, not_or]
  by_cases hu : (Function.support u).Finite
  · by_cases hv : (Function.support v).Finite
    · exact GlobalTheory.BCT.OrbProd.finsum_prod_mul_of_finite u v hu hv
    · have hv' : (Function.support v).Infinite := hv
      rw [finsum_of_infinite_support hv', mul_zero]
      rcases (Function.support u).eq_empty_or_nonempty with h | h
      · have hu0 : u = 0 := Function.support_eq_empty_iff.mp h
        simp [hu0]
      · apply finsum_of_infinite_support
        rw [hsupp]
        exact Set.Infinite.prod_right hv' h
  · have hu' : (Function.support u).Infinite := hu
    rw [finsum_of_infinite_support hu', zero_mul]
    rcases (Function.support v).eq_empty_or_nonempty with h | h
    · have hv0 : v = 0 := Function.support_eq_empty_iff.mp h
      simp [hv0]
    · apply finsum_of_infinite_support
      rw [hsupp]
      exact Set.Infinite.prod_left hu' h

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G']

theorem twOrb_prod' (θ : G →* G) (θ' : G' →* G') (K : Subgroup G) (K' : Subgroup G') (δ : G) (δ' : G')
    (f : G → ℂ) (f' : G' → ℂ)
    (hf : ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0)
    (hf' : ∀ x : G', (rStab fun k : K' => f' ((x * k)⁻¹ * δ' * θ' (x * k))).index ≠ 0) :
    twOrb (θ.prodMap θ') (K.prod K') (δ, δ') (fun y => f y.1 * f' y.2) = twOrb θ K δ f * twOrb θ' K' δ' f' := by
  rw [GlobalTheory.BCT.OrbProd.twOrb_eq, GlobalTheory.BCT.OrbProd.twOrb_eq θ, GlobalTheory.BCT.OrbProd.twOrb_eq θ',
    GlobalTheory.BCT.OrbProd.twCent_prod θ θ' δ δ', ← finsum_prod_mul',
    ← finsum_comp_equiv (Equiv.ofBijective _ (GlobalTheory.BCT.OrbProd.dcPair_bij (twCent θ δ) K (twCent θ' δ') K'))]
  refine finsum_congr fun z => ?_
  obtain ⟨t, ht, k, hk, hq⟩ := DoubleCoset.mk_out_eq_mul ((twCent θ δ).prod (twCent θ' δ')) (K.prod K')
    (Quotient.out z.1, Quotient.out z.2)
  rw [Subgroup.mem_prod] at ht hk
  have hdc : GlobalTheory.BCT.OrbProd.dcPair (twCent θ δ) K (twCent θ' δ') K' z =
      DoubleCoset.mk ((twCent θ δ).prod (twCent θ' δ')) (K.prod K') (Quotient.out z.1, Quotient.out z.2) := rfl
  have hpt : t * (Quotient.out z.1, Quotient.out z.2) * k =
      (t.1 * Quotient.out z.1 * k.1, t.2 * Quotient.out z.2 * k.2) := rfl
  rw [Equiv.ofBijective_apply, hdc, hq, hpt,
    GlobalTheory.BCT.OrbProd.orbTerm_prod θ θ' K K' δ δ' f f' _ _ (hf _) (hf' _),
    GlobalTheory.BCT.OrbProd.orbTerm_inv θ K δ f hf ht.1 hk.1, GlobalTheory.BCT.OrbProd.orbTerm_inv θ' K' δ' f' hf' ht.2 hk.2]

end Gen

section Cl

variable {G G' : Type} [Group G] [Group G']

theorem twRel_equiv (θ : G →* G) : Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  · rintro x y z ⟨g, rfl⟩ ⟨g', rfl⟩
    exact ⟨g * g', by simp [mul_assoc]⟩

def mkC (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem rel_of_mkC_eq (θ : G →* G) {x y : G} (h : mkC θ x = mkC θ y) : ∃ g, y = g⁻¹ * x * θ g :=
  (twRel_equiv θ).eqvGen_iff.mp (Quot.eqvGen_exact h)

theorem mkC_eq (θ : G →* G) {x y : G} (g : G) (h : y = g⁻¹ * x * θ g) : mkC θ x = mkC θ y :=
  Quot.sound (r := fun a b : G => ∃ g, b = g⁻¹ * a * θ g) ⟨g, h⟩

theorem mkC_rep (θ : G →* G) (c : TwCl θ) : mkC θ c.rep = c := by
  exact Quot.out_eq c

def clPair (θ : G →* G) (θ' : G' →* G') (c : TwCl (θ.prodMap θ')) : TwCl θ × TwCl θ' :=
  (mkC θ c.rep.1, mkC θ' c.rep.2)

theorem clPair_bij (θ : G →* G) (θ' : G' →* G') : Function.Bijective (clPair θ θ') := by
  constructor
  · intro c d h
    have h1 : mkC θ c.rep.1 = mkC θ d.rep.1 := congrArg Prod.fst h
    have h2 : mkC θ' c.rep.2 = mkC θ' d.rep.2 := congrArg Prod.snd h
    obtain ⟨g, hg⟩ := rel_of_mkC_eq θ h1
    obtain ⟨g', hg'⟩ := rel_of_mkC_eq θ' h2
    calc c = mkC (θ.prodMap θ') c.rep := (mkC_rep _ c).symm
      _ = mkC (θ.prodMap θ') d.rep :=
        mkC_eq _ (g, g') (Prod.ext (by simpa using hg) (by simpa using hg'))
      _ = d := mkC_rep _ d
  · rintro ⟨a, b⟩
    refine ⟨mkC (θ.prodMap θ') (a.rep, b.rep), ?_⟩
    obtain ⟨g, hg⟩ := rel_of_mkC_eq (θ.prodMap θ')
      (mkC_rep (θ.prodMap θ') (mkC (θ.prodMap θ') (a.rep, b.rep)))
    have h1 : a.rep = g.1⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.1 * θ g.1 := by
      simpa using congrArg Prod.fst hg
    have h2 : b.rep = g.2⁻¹ * (mkC (θ.prodMap θ') (a.rep, b.rep)).rep.2 * θ' g.2 := by
      simpa using congrArg Prod.snd hg
    refine Prod.ext ?_ ?_
    · exact (mkC_eq θ g.1 h1).trans (mkC_rep θ a)
    · exact (mkC_eq θ' g.2 h2).trans (mkC_rep θ' b)

end Cl

theorem charpoly_conj {R m : Type} [CommRing R] [Fintype m] [DecidableEq m] (g X : GL m R) :
    (g⁻¹ * X * g : GL m R).val.charpoly = X.val.charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g X.val

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rStab_index_ne_zero {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K') (hφ : IsHecke K' φ) (δ x : GLw n w) :
    (rStab fun k : GlobalTheory.LFun.KGL w (n := n) => φ ((x * k)⁻¹ * δ * thL n w (x * k))).index ≠ 0 := by
  obtain ⟨hKo, -, hKθ⟩ := hK
  obtain ⟨-, hinv⟩ := hφ
  have hcpt : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2
  have hopen : IsOpen ((K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) : Subgroup (GlobalTheory.LFun.KGL w (n := n))) :
      Set (GlobalTheory.LFun.KGL w (n := n))) := Subgroup.subgroupOf_isOpen (GlobalTheory.LFun.KGL w (n := n)) K' hKo
  have hfin : Finite (GlobalTheory.LFun.KGL w (n := n) ⧸ K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hH : (K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n))).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) ≤
      rStab fun k : GlobalTheory.LFun.KGL w (n := n) => φ ((x * k)⁻¹ * δ * thL n w (x * k)) := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [GlobalTheory.TwOrbConj.mem_rStab]
    intro j
    have hk1 : (k : GLw n w)⁻¹ ∈ K' := K'.inv_mem hk
    have hk2 : thL n w (k : GLw n w) ∈ K' := hKθ _ hk
    calc φ ((x * ↑(j * k))⁻¹ * δ * thL n w (x * ↑(j * k)))
        = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) * thL n w ↑k) := by
          congr 1
          simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc]
      _ = φ ((↑k)⁻¹ * ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j))) := (hinv _ hk2 _).2
      _ = φ ((x * ↑j)⁻¹ * δ * thL n w (x * ↑j)) := (hinv _ hk1 _).1
  intro h0
  apply hH
  have hd := Subgroup.index_dvd_of_le hle
  rw [h0] at hd
  exact Nat.eq_zero_of_zero_dvd hd

theorem nrmL_charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  have hinv := GlobalTheory.BCT.TwistInvol.thL_involutive E n w g
  unfold nrmL
  unfold thL at hinv ⊢
  split_ifs at hinv ⊢ with hs
  · simp only [MonoidHom.id_apply]
    exact charpoly_conj g y
  · have key : g⁻¹ * y * thetaGL n (cj w) g * thetaGL n (cj w) (g⁻¹ * y * thetaGL n (cj w) g) =
        g⁻¹ * (y * thetaGL n (cj w) y) * g := by
      simp only [map_mul, map_inv, hinv]
      group
    rw [key]
    exact charpoly_conj g _

private theorem charpoly_nrmL_rep_eq_and_twOrb_rep_eq {n : ℕ} {w : Pl E} {K' : Subgroup (GLw n w)} {φ : GLw n w → ℂ}
    (hK : IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) K') (hφ : IsHecke K' φ) (x : GLw n w) :
    (nrmL n w (mkC (thL n w) x).rep).val.charpoly = (nrmL n w x).val.charpoly ∧
      twOrb (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (mkC (thL n w) x).rep φ =
        twOrb (thL n w) (GlobalTheory.LFun.KGL w (n := n)) x φ := by
  obtain ⟨g, hg⟩ := rel_of_mkC_eq (thL n w) (mkC_rep (thL n w) (mkC (thL n w) x))
  constructor
  · have h := nrmL_charpoly_twConj n w g (mkC (thL n w) x).rep
    rw [← hg] at h
    exact h.symm
  · have h := GlobalTheory.TwOrbConj.twOrb_twConj (GLw n w) (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (mkC (thL n w) x).rep g φ
      (fun y => rStab_index_ne_zero hK hφ _ y)
    rw [← hg] at h
    exact h.symm

theorem stTw2_tens : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E)
    (Q₁ Q₂ : (w.adicCompletion E)[X])
    (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw b w)) (φ₁ : GLw a w → ℂ) (φ₂ : GLw b w → ℂ),
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ → IsLevel (thL b w) (GlobalTheory.LFun.KGL w (n := b)) K₂ → IsHecke K₁ φ₁ →
    IsHecke K₂ φ₂ → stTw2 a b w Q₁ Q₂ (tens φ₁ φ₂) = stTw a w Q₁ φ₁ * stTw b w Q₂ φ₂ := by
  intro E _ _ _ a b w Q₁ Q₂ K₁ K₂ φ₁ φ₂ h₁ h₂ h₃ h₄
  unfold stTw2 stTw tens clSum
  rw [← finsum_prod_mul', ← finsum_comp_equiv (Equiv.ofBijective _ (clPair_bij (thL a w) (thL b w)))]
  refine finsum_congr fun c => ?_
  have hcl : clPair (thL a w) (thL b w) c = (mkC (thL a w) c.rep.1, mkC (thL b w) c.rep.2) := rfl
  obtain ⟨hc₁, ho₁⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₁ h₃ c.rep.1
  obtain ⟨hc₂, ho₂⟩ := charpoly_nrmL_rep_eq_and_twOrb_rep_eq h₂ h₄ c.rep.2
  have ho : twOrb ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) c.rep
      (fun y => φ₁ y.1 * φ₂ y.2) =
      twOrb (thL a w) (GlobalTheory.LFun.KGL w (n := a)) c.rep.1 φ₁ * twOrb (thL b w) (GlobalTheory.LFun.KGL w (n := b)) c.rep.2 φ₂ :=
    twOrb_prod' (thL a w) (thL b w) _ _ c.rep.1 c.rep.2 φ₁ φ₂ (fun x => rStab_index_ne_zero h₁ h₃ _ x)
      (fun x => rStab_index_ne_zero h₂ h₄ _ x)
  rw [Equiv.ofBijective_apply, hcl]
  simp only [Set.mem_ofPred_eq, Pi.one_apply, one_mul, hc₁, hc₂, ho₁, ho₂, ho]
  by_cases hA : (nrmL a w c.rep.1).val.charpoly = Q₁ <;>
    by_cases hB : (nrmL b w c.rep.2).val.charpoly = Q₂ <;> simp [hA, hB]

end GlobalTheory.BCT.StTwTens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrIdxProof2
section
section
open GlobalTheory.PsCo.PcEG

noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem StrIdx_proof2 : StrIdx := by
  intro n ε P
  choose Qm hQm using fun s s' : Finset (Fin (n * n)) => ffMat_poly (ε := ε) s s'
  set Q : Poly n := ∑ s ∈ Finset.univ.filter (IsPhysSet ε), ((-1 : ℂ) ^ s.card) • Qm s s with hQdef
  have hQ : ∀ m : Mat n, ev m Q = physDet ε m := by
    intro m
    show MvPolynomial.eval (entVar m) Q = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← strPhys_eq_physDet, strPhys, hQdef, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.smul_eval, hQm]
    rfl
  obtain ⟨d2, hd2⟩ : ∃ d2 : ℕ, ∀ s s' : Finset (Fin (n * n)), (P * Qm s s').totalDegree ≤ d2 :=
    ⟨∑ s, ∑ s', (P * Qm s s').totalDegree, fun s s' =>
      le_trans (Finset.single_le_sum (f := fun s' => (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s'))
      (Finset.single_le_sum (f := fun s => ∑ s', (P * Qm s s').totalDegree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ s))⟩
  refine ⟨max (P * Q).totalDegree d2, ?_⟩
  intro H _ _ _ σ D E hσ hD L _ hLK hLd Y _ hY0Y hYP hG hK B hB
  have hdeg1 : (P * Q).totalDegree ≤ max (P * Q).totalDegree d2 := le_max_left _ _
  have hdeg2 : ∀ s s', (P * Qm s s').totalDegree ≤ max (P * Q).totalDegree d2 := fun s s' =>
    (hd2 s s').trans (le_max_right _ _)
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
  have hφc : Continuous (fun k : KG ε => toMK k) := hemb.continuous
  have hφK : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hent : ∀ R : Poly n, Continuous fun k : KG ε => ev (toMK k) R := by
    intro R
    refine (MvPolynomial.continuous_eval R).comp (continuous_pi fun p => ?_)
    rcases p with p | p
    · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hφc))
  have hBL : ∀ w, B w ∈ L.map D.subtype := by
    intro w
    rw [hB]
    have := hLd (P * Q) hdeg1 w
    simpa only [map_mul, hQ] using this
  refine ⟨hBL, ?_⟩
  have hAL : ∀ k : KG ε, ∀ x ∈ L.map D.subtype, σ (toMK k) x ∈ L.map D.subtype := by
    rintro k _ ⟨y, hy, rfl⟩
    exact ⟨sigD hD (hφK k) y, hLK _ (hφK k) y hy, rfl⟩
  have hAc : ∀ v, Continuous fun k : KG ε => σ (toMK k) v := fun v =>
    (hσ.2.2 v).comp_continuous hφc fun g => kset_mem_UJset (hφK g)
  have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
    have := hent (P * Q)
    simpa only [map_mul, hQ] using this
  rw [trace_integral_restrict (μ := muK ε) (L.map D.subtype) hcont (fun k => σ (toMK k)) hAc hAL B hB
    (fun x _ => hBL x)]
  have hY0G : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε, gradT y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε :=
    fun y hy => ⟨tensFock_lTensor_stable _ hy.1, (physSub_stable ε E).2.2.2.2 y hy.2⟩
  have hY0K : ∀ (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε), ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε,
      wK hD hk y ∈ tensFock (n := n) L ⊓ physicalSubspace (N := D) ε := fun k hk y hy =>
    ⟨wK_tensFock hD hk (hLK k hk) hy.1, wK_physSub hD hk hy.2⟩
  have hpt : ∀ k : KG ε, ev (toMK k) P * physDet ε (toMK k) *
      LinearMap.trace ℂ (L.map D.subtype) (((σ (toMK k) : H →L[ℂ] H) : H →ₗ[ℂ] H).restrict (hAL k)) =
      ev (toMK k) P * LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) := by
    intro k
    rw [trace_map_subtype (sigD hD (hφK k)) (fun x hx => hLK _ (hφK k) x hx) _ _ (fun x => rfl)]
    have := str_tensFock_physSub hD (hφK k) (fun x hx => hLK _ (hφK k) x hx)
      (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))
    rw [show LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD (hφK k)).restrict (fun y hy => hY0G _ (hY0K _ (hφK k) y hy))) = _ from this]
    ring
  simp_rw [hpt]
  have hcP := hent P
  have hrange := fun y => btot_range (μ := muK ε) hσ hD hK (L := L) hφc hφK hcP
    (fun s s' u => by
      have h1 := hLd (P * Qm s s') (hdeg2 s s') u
      have h2 : ∫ k : KG ε, (ev (toMK k) P * ffMat ε (toMK k) s s') • σ (toMK k) u ∂(muK ε) =
          ∫ k : KG ε, ev (toMK k) (P * Qm s s') • σ (toMK k) u ∂(muK ε) := by
        congr 1
        funext k
        rw [map_mul, hQm]
        rfl
      rw [h2]
      exact h1) hYP y
  exact (int_str_eq (μ := muK ε) hσ hD hY0Y hK hY0K hG hY0G hφc hφK hcP hrange).symm

end GlobalTheory.PsCo.PcEF

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTmulNotMemPrimeOfGraphImageNeZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal

theorem sum_notMem_of_ne_zero : ∀ {K κ κ' : Type} [Field K] [Field κ] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ] [Algebra ℂ κ']
    (R : Subring K) (π : R →+* κ) (ρ : κ →ₐ[ℂ] κ') (E : Place (algebraMap ℂ K))
    (𝔭 : Ideal (tens (κ' := κ') (placeAlg E))) [𝔭.IsPrime],
  graphIdeal E R π ρ ≤ 𝔭 → E.Contains R →
  ∀ (l : ℕ) (a : Fin l → R) (b : Fin l → κ') (w : tens (κ' := κ') (placeAlg E)),
    (w : K ⊗[ℂ] κ') = ∑ i, (a i : K) ⊗ₜ b i → ∑ i, ρ (π (a i)) * b i ≠ 0 → w ∉ 𝔭 := by
  intro K κ κ' _ _ _ _ _ _ R π ρ E 𝔭 _ hle hR l a b w hw hc
  let g : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨(a i : K) ⊗ₜ 1 - 1 ⊗ₜ ρ (π (a i)),
      sub_mem (tmul_mem (hR _ (a i).2) 1) (tmul_mem (one_mem (placeAlg E)) _)⟩
  let bb : Fin l → tens (κ' := κ') (placeAlg E) := fun i =>
    ⟨1 ⊗ₜ b i, tmul_mem (one_mem (placeAlg E)) _⟩
  let u : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i), tmul_mem (one_mem (placeAlg E)) _⟩
  let v : tens (κ' := κ') (placeAlg E) :=
    ⟨1 ⊗ₜ (∑ i, ρ (π (a i)) * b i)⁻¹, tmul_mem (one_mem (placeAlg E)) _⟩
  have hg : ∀ i, g i ∈ graphIdeal E R π ρ := fun i => Ideal.subset_span (Or.inr ⟨a i, rfl⟩)
  have hsum : w - u = ∑ i, g i * bb i := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, hw, AddSubmonoidClass.coe_finsetSum]
    simp only [g, bb, u, Subalgebra.coe_mul, sub_mul, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one, Finset.sum_sub_distrib, TensorProduct.tmul_sum]
  have huv : u * v = 1 := by
    apply Subtype.ext
    simp only [u, v, Subalgebra.coe_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_inv_cancel₀ hc, Subalgebra.coe_one, Algebra.TensorProduct.one_def]
  have hu : u ∉ 𝔭 := fun h => one_notMem 𝔭 (huv ▸ 𝔭.mul_mem_right v h)
  intro hwp
  have hd : w - u ∈ 𝔭 :=
    hle (hsum ▸ Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hg i))
  exact hu (by simpa using 𝔭.sub_mem hwp hd)

end GlobalTheory.GraphLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupertraceCarriedByDiracKernel
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open GlobalTheory.PsCo.Pc1 (Mat)

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

set_option maxHeartbeats 1000000 in
theorem supertrace_carriedBy_diracKernel : StrKer := by
  intro n ε H _ _ σ D E hσ hD Y _ hY hG hK
  classical
  let Z : Submodule ℂ (TensorProduct ℂ D (Fock n)) := Y ⊓ LinearMap.ker (dD ε E)
  have hZY : Z ≤ Y := inf_le_left
  haveI hZf : FiniteDimensional ℂ Z := Submodule.finiteDimensional_of_le hZY
  have hZK : ∀ (k : Mat n) (hk : k ∈ Kset ε), ∀ y ∈ Z, wK hD hk y ∈ Z := by
    intro k hk y hy
    refine ⟨hK k hk y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (wK hD hk y) = 0
    rw [← wK_D hσ hD hk, h0, map_zero]
  have hZG : ∀ y ∈ Z, gradT y ∈ Z := by
    intro y hy
    refine ⟨hG y hy.1, ?_⟩
    have h0 : dD ε E y = 0 := hy.2
    show dD ε E (gradT y) = 0
    have := gradT_D (ε := ε) E y
    rw [h0, map_zero] at this
    exact neg_eq_zero.1 this.symm
  let Γ : TSub Z →ₗ[ℂ] TSub Z := ((gradT.restrict hZG : Z →ₗ[ℂ] Z) : TSub Z →ₗ[ℂ] TSub Z)
  refine ⟨Z, hZf, hZK, Γ, hZY, fun y hy => hy.2, fun k hk => ?_⟩
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  let Dl : TSub Y →ₗ[ℂ] TSub Y := (((dD ε E).restrict hY : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let Γy : TSub Y →ₗ[ℂ] TSub Y := ((gradT.restrict hG : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  let B : TSub Y →ₗ[ℂ] TSub Y := (((wK hD hk).restrict (hK k hk) : Y →ₗ[ℂ] Y) : TSub Y →ₗ[ℂ] TSub Y)
  obtain ⟨hker, htr⟩ := str_eq_str_ker Dl Γy B
    (fun x y => by rw [tsub_inner, tsub_inner]; exact tform_D hU _ _)
    (fun x => Subtype.ext (gradT_D E _)) (fun x => Subtype.ext (wK_D hσ hD hk _))
  have h1 : LinearMap.trace ℂ Y ((gradT ∘ₗ wK hD hk).restrict (fun y hy => hG _ (hK k hk y hy))) =
      LinearMap.trace ℂ (TSub Y) (Γy ∘ₗ B) := rfl
  rw [h1, htr]
  have hmemZ : ∀ x : LinearMap.ker Dl, tsubVal Y (x : TSub Y) ∈ Z := by
    intro x
    have hx : Dl (x : TSub Y) = 0 := x.2
    exact ⟨tsubVal_mem (x : TSub Y), congrArg (tsubVal Y) hx⟩
  let f : LinearMap.ker Dl →ₗ[ℂ] TSub Z :=
    { toFun := fun x => ((⟨tsubVal Y (x : TSub Y), hmemZ x⟩ : Z) : TSub Z)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have : tsubVal Y (x : TSub Y) = tsubVal Y (y : TSub Y) := congrArg (tsubVal Z) hxy
      exact Subtype.ext (tsubVal_injective this)
    · intro z
      have hzY : tsubVal Z z ∈ Y := hZY (tsubVal_mem z)
      let x : TSub Y := ((⟨tsubVal Z z, hzY⟩ : Y) : TSub Y)
      have hx : x ∈ LinearMap.ker Dl := by
        rw [LinearMap.mem_ker]
        apply tsubVal_injective
        rw [map_zero]
        exact (tsubVal_mem z).2
      exact ⟨⟨x, hx⟩, rfl⟩
  let e := LinearEquiv.ofBijective f hf
  rw [← LinearMap.trace_conj' _ e]
  congr 1
  apply LinearMap.ext
  intro z
  rw [LinearEquiv.conj_apply_apply]
  apply tsubVal_injective
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearEquiv.symm_apply_apply]
  show tsubVal Z (f ((Γy ∘ₗ B).restrict hker x)) = tsubVal Z (Γ (tOp hD hZK k (f x)))
  have hΓ : ∀ w : TSub Z, tsubVal Z (Γ w) = gradT (tsubVal Z w) := fun w => rfl
  rw [hΓ, tOp_apply hD hZK hk]
  rfl

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimClosureLeOfSpecializes
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem topologicalKrullDim_closure_le_of_specializes :
    ∀ (X : Scheme.{0}) (z w : X) (j : ℕ), z ⤳ w → w ≠ z →
      topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) →
      topologicalKrullDim (closure ({w} : Set X)) ≤ j := by
  first
  | exact @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes
  | (apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosureDimensionSpecialization.dim_closure_le_of_specializes ..)

end GlobalTheory.PairStep
end

