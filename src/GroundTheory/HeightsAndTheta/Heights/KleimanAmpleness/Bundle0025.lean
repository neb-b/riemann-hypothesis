module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechDoubleSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechDouble.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (N r : ℕ) (x : Fin (N + 1) → Ω) (h : Fin (r + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module S E]
    (A : Chart x → Submodule S E) (B : Chart h → Submodule S E) (M : Chart x → Chart h → Submodule S E),
    (∀ (I I' : Chart x) (J : Chart h), I.1 ⊆ I'.1 → M I J ≤ M I' J) →
    (∀ (I : Chart x) (J J' : Chart h), J.1 ⊆ J'.1 → M I J ≤ M I J') →
    (∀ I, Cech.AugExact S (M I) (A I)) → (∀ J, Cech.AugExact S (fun I => M I J) (B J)) →
    ∀ n : ℕ, Nonempty (Cech.Hdeg (fun _ : Chart x => E) A (Cech.idRes S E (support x)) n ≃ₗ[S]
      Cech.Hdeg (fun _ : Chart h => E) B (Cech.idRes S E (support h)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHdegOfSubSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechHdegOfSub.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (T : SubSystem S x E) (n : ℕ),
    Nonempty (T.H n ≃ₗ[S] Cech.Hdeg (fun _ : Chart x => E) (fun I => (T.sub I).restrictScalars S)
      (Cech.idRes S E (support x)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutNonemptySt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutNonempty.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp (n + 1) →
    IsVeryAmple L.toSubSystem → s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes, ∃ j, (X j : Poly k N) ∉ qq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutZeroNotLeSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def CutZeroNotLe.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω), IsSubvar x pp e →
    s ∈ L.secs → (∃ I, s ∉ (L.twist (idealSys x pp)).sub I) →
    ∃ f ∈ zeroIdeal L.toSubSystem s, f ∉ pp

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHCombContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k),
    i₀ ∉ J k → ∀ f : CombC S J n, combD S J n f = 0 →
      ∃ g : CombC S J n, f - g ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        (J k = ∅ ∧ (I.1.1 k).card = 1 →
          ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = f I') ∧
        (¬ (J k = ∅ ∧ (I.1.1 k).card = 1) → g I = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombCyclicSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHCombCyclic.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ),
    (∀ k, J k = ∅ ∨ J k = Finset.univ) →
      combD S J n (singOne S J n) = 0 ∧
        ∀ f : CombC S J n, combD S J n f = 0 → ∃ s : S, f - s • singOne S J n ∈ combB S J n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeBadFiniteSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeBadFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (e : K → ℤ),
    {a : (Σ k, ι k) → ℤ | blockSum a = e ∧ ∀ k, negSet a k = ∅ ∨ negSet a k = Finset.univ}.Finite

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeDecompSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeDecomp.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (c d : K → ℤ) (n : ℕ),
    ∀ φ ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n,
      ∃ (A : Finset ((Σ k, ι k) → ℤ)) (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
        (∀ a ∈ A, blockSum a = c + d) ∧ φ = ∑ a ∈ A, embed S a n (f a)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeEmbedSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeEmbed.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (a : (Σ k, ι k) → ℤ),
    (∀ (n : ℕ) (f : CombC S (negSet a) n),
      KH.cechD S ι (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) n (embed S a n f) =
        embed S a (n + 1) (combD S (negSet a) n f)) ∧
    (∀ (c d : K → ℤ), blockSum a = c + d → ∀ (n : ℕ) (f : CombC S (negSet a) n),
      embed S a n f ∈ KH.cechCc ι (fun c => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (c + d)) c n) ∧
    ((∀ p, 0 ≤ a p) → ∃ m ∈ KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (blockSum a),
      ∀ I : ∀ k, Finset (ι k), monoFrac S I a = LocalizedModule.mk m 1)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHFreeIndepSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHFreeIndep.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (n : ℕ) (A : Finset ((Σ k, ι k) → ℤ))
    (f : ∀ a : (Σ k, ι k) → ℤ, CombC S (negSet a) n),
    ∑ a ∈ A, embed S a n (f a) = 0 → ∀ a ∈ A, f a = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

universe u w

section Numbers

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} (hR : GenericPointSectionInput.Statement.{u, w})


include hR in
theorem interNum_nonneg_nef_veryAmple : ∀ (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin (n + 1) → LineBundle k x),
    IsSubvar x pp (n + 1) → Nef (L 0).toSubSystem → (∀ i, i ≠ 0 → IsVeryAmple (L i).toSubSystem) →
      0 ≤ interNum pp (fun i => (L i).toSubSystem) := by
  intro n
  induction n with
  | zero =>
    intro pp L hW hnef _
    have h1 : (fun i => (L i).toSubSystem) = ![(L 0).toSubSystem] := by
      funext i; fin_cases i; rfl
    rw [h1]
    exact hnef pp bot_le hW
  | succ n ih =>
    intro pp L hW hnef hL
    have hlast : Fin.last (n + 1) ≠ 0 := fun h => by simpa using congrArg Fin.val h
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last (n + 1))) (hL _ hlast) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin (n + 1) => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last (n + 1))).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 (n + 1) pp (fun i => L (Fin.castSucc i)) (L (Fin.last (n + 1))) s hW hs
      hsI]
    refine finsum_nonneg fun qq => ?_
    split_ifs with h
    · refine mul_nonneg (Nat.cast_nonneg _) (ih qq (fun i => L (Fin.castSucc i)) h.2 hnef fun i hi => ?_)
      exact hL _ fun h0 => hi (Fin.castSucc_injective _ (by rw [h0]; rfl))
    · exact le_rfl

end Numbers

theorem LeadingCoeffPos.proof_of_cut (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : LeadingCoeffPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M Nb q m b hZ hM hNb hva hb
  let L : Fin (d + 1) → LineBundle k x := fun _ => Nb
  have hV : ((M.tpow q).tensor (twistBundle k x m)).toSubSystem = Nb.toSubSystem := by
    rw [hNb, LineBundle.tensor_toSubSystem, LineBundle.tpow_toSubSystem]
    rfl
  have hm0 : 0 ≤ m := by
    have : (0 : ℤ) ≤ ((d + 1 : ℕ) : ℤ) * b := by positivity
    linarith
  obtain ⟨mn, hmn⟩ := Int.eq_ofNat_of_zero_le hm0

  have h1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      q * bundleNum (primeOf (S := k) x) (Function.update L 0 M) +
        m * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    have e1 : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
        bundleNum (primeOf (S := k) x) (Function.update L 0 ((M.tpow q).tensor (twistBundle k x m))) := by
      unfold bundleNum
      congr 1
      funext j
      by_cases hj : j = 0
      · subst hj
        simp only [Function.update_self, hV]
      · simp only [Function.update_of_ne hj, L]
    rw [e1, bundleNum_tensor hR hZ, bundleNum_tpow hR hZ, hmn, bundleNum_twist hR hZ]

  have h2 : interNum (primeOf (S := k) x)
      (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
        (fun _ : Fin d => Nb.toSubSystem)) =
      b * bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    rw [← bundleNum_twist hR hZ]
    unfold bundleNum
    congr 1
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cons_zero, Function.update_self, twistBundle_toSubSystem]
    · simp only [Fin.cons_succ, Function.update_of_ne (Fin.succ_ne_zero i), L]

  have hX : 0 ≤ bundleNum (primeOf (S := k) x) (Function.update L 0 M) := by
    refine interNum_nonneg_nef_veryAmple hR d _ _ hZ (by simpa only [Function.update_self] using hM)
      fun i hi => ?_
    simp only [Function.update_of_ne hi, L]
    exact hva

  have hY : 0 < bundleNum (primeOf (S := k) x) (Function.update L 0 (twistBundle k x 1)) := by
    refine hPos k Ω N x (d + 1) _ _ hZ fun i => ?_
    by_cases hi : i = 0
    · subst hi
      simpa only [Function.update_self, twistBundle_toSubSystem] using
        (isVeryAmple_twistSys_one (S := k) (x := x))
    · simp only [Function.update_of_ne hi, L]
      exact hva
  rw [h1, h2]
  have hc := mul_pos (sub_pos.mpr hb) hY
  have hq := mul_nonneg (Int.natCast_nonneg q) hX
  nlinarith

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace InterNumRestrict

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {K' : Type w} [Field K'] [Algebra k K'] {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}

theorem inr_foldl_restrict {n : ℕ} (L : Fin n → LineBundle k x) (L' : Fin n → LineBundle k y)
    (rr : Fin n → Ω → K') (hL : ∀ i, RestrictData (L i).toSubSystem hxy (L' i).toSubSystem (rr i)) :
    ∀ (l : List (Fin n)) (Q : LineBundle k x) (Q' : LineBundle k y) (r : Ω → K'),
      RestrictData Q.toSubSystem hxy Q'.toSubSystem r →
      ∃ (P : LineBundle k x) (P' : LineBundle k y) (s : Ω → K'),
        l.foldl (fun F i => F.twist (L i).toSubSystem) Q.toSubSystem = P.toSubSystem ∧
        l.foldl (fun F i => F.twist (L' i).toSubSystem) Q'.toSubSystem = P'.toSubSystem ∧
        RestrictData P.toSubSystem hxy P'.toSubSystem s := by
  intro l
  induction l with
  | nil =>
    intro Q Q' r h
    exact ⟨Q, Q', r, rfl, rfl, h⟩
  | cons i l ih =>
    intro Q Q' r h
    have htwist : ∃ s : Ω → K',
        RestrictData (Q.toSubSystem.twist (L i).toSubSystem) hxy
          (Q'.toSubSystem.twist (L' i).toSubSystem) s :=
      RestrictTwist.restrictData_twist (Q₁ := Q) (Q₂ := L i)
        (Q₁' := Q') (Q₂' := L' i) (hxy := hxy) (r₁ := r) (r₂ := rr i) h (hL i)
    obtain ⟨s, hs⟩ := htwist
    exact ih (Q.tensorProd (L i)) (Q'.tensorProd (L' i)) s hs

theorem proof (hRL : RestrLenRestrict.Statement.{u, w}) : InterNumRestrict.Statement.{u, w} := by
  intro k _ Ω _ _ N x K' _ _ y hxy hle pp n hsub L L' rr hL
  have hT : ∀ T : Finset (Fin n), ∀ᶠ c : ℕ in atTop,
      restrLen pp ((tensorSub (fun i => (L' i).toSubSystem) T).twist (twistSys k y (c : ℤ))) =
        restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) := by
    intro T
    obtain ⟨P, P', s, hP, hP', hs⟩ := inr_foldl_restrict L L' rr hL
      ((List.finRange n).filter (· ∈ T)) (twistBundle k x 0) (twistBundle k y 0)
      (RestrictTwist.twistRes k x y 0) (RestrictTwist.restrictData_twistSys hxy hle 0)
    have e1 : tensorSub (fun i => (L i).toSubSystem) T = P.toSubSystem := hP
    have e2 : tensorSub (fun i => (L' i).toSubSystem) T = P'.toSubSystem := hP'
    rw [e1, e2]
    exact hRL k Ω N x K' y hxy hle pp n hsub P P' s hs
  have hall : ∀ᶠ c : ℕ in atTop, interSum pp (fun i => (L' i).toSubSystem) c =
      interSum pp (fun i => (L i).toSubSystem) c := by
    filter_upwards [Filter.eventually_all.2 hT] with c hc
    unfold interSum
    exact Finset.sum_congr rfl fun T _ => by rw [hc T]
  unfold interNum limUnder
  rw [Filter.map_congr hall]

end InterNumRestrict

end

end GroundTheory.Heights₂.Heights.Kleiman
end

