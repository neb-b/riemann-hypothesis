module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0482

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlaces
section
namespace GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isoLoc_perm {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    {Pa Pa' : List (Part A.CG)} (h : Pa.Perm Pa') (w : PlE H) : isoLoc N A Pa w = isoLoc N A Pa' w := by
  unfold isoLoc
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [List.foldr_cons, ih]
  | swap x y l =>
    simp only [List.foldr_cons]
    rw [← A.lpSum_assoc, ← A.lpSum_assoc, A.lpSum_comm (spehLoc N A y w)]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end GlobalTheory.RowTie.RepDet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.RowTie.repDet_split : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i →
    ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  intro R H what₂ N A i hBC hSp hRep P P' hP
  obtain ⟨Pa, hPa⟩ := hBC P
  obtain ⟨Pa', hPa'⟩ := hBC P'
  have hperm := hSp P P' hP Pa Pa' hPa hPa'
  have hiso := GlobalTheory.RowTie.RepDet.isoLoc_perm N A hperm
  apply hRep P P'
  · intro w hw
    rw [← hPa.2.2.2.1 w hw, ← hPa'.2.2.2.1 w hw, hiso w]
  · intro w hw
    rw [← (hPa.2.2.2.2.1 w hw).2, ← (hPa'.2.2.2.2.1 w hw).2, hiso w]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

variable {R : Type} [CommRing R] {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace R N)

def fOpen (g : MvPolynomial (Fin (N + 1)) R) : X.Opens := ι ⁻¹ᵁ Proj.basicOpen (grading R N) g

def fRatio {n : ℕ} (f g : MvPolynomial (Fin (N + 1)) R) (hf : f ∈ grading R N n) (hg : g ∈ grading R N n) :
    Γ(X, fOpen ι g) :=
  (ι.app (Proj.basicOpen (grading R N) g)).hom (GlobalTheory.ProjFrac.frac (grading R N) _ f g hf hg le_rfl)

theorem fRatio_self {n : ℕ} (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ grading R N n) :
    fRatio ι g g hg hg = 1 := by
  unfold fRatio
  rw [GlobalTheory.ProjFrac.frac_self]
  exact map_one _

theorem mem_fOpen (g : MvPolynomial (Fin (N + 1)) R) (z : X) :
    z ∈ fOpen ι g ↔ g ∉ (ι.base z).asHomogeneousIdeal := Iff.rfl

end GlobalTheory.EtProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisAdmissibleIffRepPureAvatar
section
noncomputable section

namespace GlobalTheory.GaloisInputCompare

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := K)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

theorem exists_inducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) :
    ∃ w ∈ placesOver H.E (N.l i), InducesW N i τ w := by
  have hle : ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral (map_isIntegral_int τ (RingOfIntegers.isIntegral_coe x))
  let I : Ideal (𝓞 H.E) :=
    { carrier := {x | ‖τ (x : H.E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        change ‖τ ((x + y : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((x + y : 𝓞 H.E) : H.E) = x + y from rfl, map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      smul_mem' := fun c x hx => by
        change ‖τ ((c * x : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((c * x : 𝓞 H.E) : H.E) = c * x from rfl, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hle c)).trans_lt hx }
  have hI : ∀ x : 𝓞 H.E, x ∈ I ↔ ‖τ (x : H.E)‖ < 1 := fun x => Iff.rfl
  have hl : ((N.l i : ℕ) : 𝓞 H.E) ∈ I := by
    rw [hI, show (((N.l i : ℕ) : 𝓞 H.E) : H.E) = (N.l i : ℕ) by simp, map_natCast,
      ← map_natCast (algebraMap ℚ_[N.l i] (PadicAlgCl (N.l i))), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hP : I.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have := (hI 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hI, show ((x * y : 𝓞 H.E) : H.E) = x * y from rfl, map_mul, norm_mul] at h
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  refine ⟨⟨I, hP, fun h => ?_⟩, hl, fun x => (hI x).symm⟩
  rw [h, Ideal.mem_bot] at hl
  exact (N.lPrime i).out.ne_zero (by exact_mod_cast hl)


end GlobalTheory.GaloisInputCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowClose

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem isoLoc_eq_twSum_zero (P : List (Part A.CG)) (h : ∀ p ∈ P, p.d = 1) (w : PlE H) :
    isoLoc N A P w =
      GlobalTheory.RowTie.twSum N A (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))) w := by
  induction P with
  | nil => rfl
  | cons p P ih =>
    have hp : p.d = 1 := h p (by simp)
    have h1 : spehLoc N A p w = A.lpTw (A.locG p.π w) 0 := by
      simp [spehLoc, hp, A.lpSum_zero]
    change A.lpSum (spehLoc N A p w) (isoLoc N A P w) = A.lpSum (A.lpTw (A.locG p.π w) 0) _
    rw [h1, ih fun q hq => h q (by simp [hq])]
    rfl

theorem isobaricCuspidalMultiplicityOne_of_twisted : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricCuspidalStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' hw
  have key := hR (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (Pa'.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ)))
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h p hp).1)
    (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      exact (h' p hp).1)
    (hw.mono fun w e => by
      rw [← isoLoc_eq_twSum_zero N A Pa (fun p hp => (h p hp).2),
        ← isoLoc_eq_twSum_zero N A Pa' (fun p hp => (h' p hp).2), e])
  have back : ∀ P : List (Part A.CG), (∀ p ∈ P, p.d = 1) →
      (P.map fun p => ((⟨p.a, p.π⟩ : Σ a : ℕ, A.CG a), (0 : ℝ))).map
        (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG)) = P := by
    intro P hP
    rw [List.map_map]
    conv_rhs => rw [← List.map_id P]
    refine List.map_congr_left fun p hp => ?_
    have := hP p hp
    obtain ⟨a, π, d⟩ := p
    simp only at this
    subst this
    rfl
  have := key.map (fun q => (⟨q.1.1, q.1.2, 1⟩ : Part A.CG))
  rwa [back Pa (fun p hp => (h p hp).2), back Pa' (fun p hp => (h' p hp).2)] at this

end GlobalTheory.RowClose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.SpehRigid

def seg {C : Type} (p : C × ℕ) : Multiset (C × ℤ) :=
  (Multiset.range p.2).map fun a : ℕ => (p.1, (p.2 : ℤ) - 1 - 2 * (a : ℤ))

theorem seg_nodup {C : Type} (p : C × ℕ) : (seg p).Nodup := by
  refine (Multiset.nodup_range _).map ?_
  intro a b h
  have := congrArg Prod.snd h
  simp only at this
  omega

theorem mem_seg {C : Type} (p : C × ℕ) (c : C) (e : ℤ) :
    (c, e) ∈ seg p ↔ p.1 = c ∧ ∃ a : ℕ, a < p.2 ∧ (p.2 : ℤ) - 1 - 2 * (a : ℤ) = e := by
  simp only [seg, Multiset.mem_map, Multiset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨h1, a, ha, h2⟩
  · rintro ⟨h1, a, ha, h2⟩
    exact ⟨a, ha, h1, h2⟩

theorem count_seg {C : Type} [DecidableEq C] (p : C × ℕ) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (seg p).count (c, (d : ℤ) - 1) = (seg p).count (c, (d : ℤ) + 1) + if (c, d) = p then 1 else 0 := by
  rw [Multiset.count_eq_of_nodup (seg_nodup p), Multiset.count_eq_of_nodup (seg_nodup p)]
  obtain ⟨c', d'⟩ := p
  have e1 : (c, (d : ℤ) - 1) ∈ seg (c', d') ↔ c' = c ∧ d ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  have e2 : (c, (d : ℤ) + 1) ∈ seg (c', d') ↔ c' = c ∧ d + 2 ≤ d' ∧ (d' + d) % 2 = 0 := by
    rw [mem_seg]
    refine and_congr_right fun _ => ⟨?_, fun h => ⟨(d' - d - 2) / 2, ?_, ?_⟩⟩
    · rintro ⟨a, h1, h2⟩
      simp only at h1 h2
      omega
    · simp only; omega
    · simp only; omega
  simp only [e1, e2, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    simp only [true_and]
    split_ifs <;> omega
  · simp [hc, Ne.symm hc]

theorem count_bind_seg {C : Type} [DecidableEq C] (P : Multiset (C × ℕ)) (c : C) (d : ℕ) (hd : 1 ≤ d) :
    (P.bind seg).count (c, (d : ℤ) - 1) = (P.bind seg).count (c, (d : ℤ) + 1) + P.count (c, d) := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons p P ih =>
    rw [Multiset.cons_bind, Multiset.count_add, Multiset.count_add, ih, count_seg p c d hd, Multiset.count_cons]
    omega

theorem eq_of_bind_seg {C : Type} (P P' : Multiset (C × ℕ)) (h : ∀ p ∈ P, 1 ≤ p.2) (h' : ∀ p ∈ P', 1 ≤ p.2)
    (e : P.bind seg = P'.bind seg) : P = P' := by
  classical
  ext ⟨c, d⟩
  by_cases hd : 1 ≤ d
  · have h1 := count_bind_seg P c d hd
    have h2 := count_bind_seg P' c d hd
    rw [e] at h1
    omega
  · rw [Multiset.count_eq_zero_of_notMem fun hm => hd (h _ hm),
      Multiset.count_eq_zero_of_notMem fun hm => hd (h' _ hm)]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def flat (p : Formalism.BasicNotions.Part A.CG) : List ((Σ a : ℕ, A.CG a) × ℝ) :=
  (List.range p.d).map fun k : ℕ => (⟨p.a, p.π⟩, ((p.d : ℝ) - 1) / 2 - (k : ℝ))

theorem twSum_append (L L' : List ((Σ a : ℕ, A.CG a) × ℝ)) (w : PlE H) :
    GlobalTheory.RowTie.twSum N A (L ++ L') w = A.lpSum (GlobalTheory.RowTie.twSum N A L w) (GlobalTheory.RowTie.twSum N A L' w) := by
  unfold GlobalTheory.RowTie.twSum
  induction L with
  | nil => rw [List.nil_append, List.foldr_nil, A.lpSum_comm, A.lpSum_zero]
  | cons p L ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, A.lpSum_assoc]

theorem spehLoc_eq (p : Formalism.BasicNotions.Part A.CG) (w : PlE H) :
    spehLoc N A p w = GlobalTheory.RowTie.twSum N A (flat N A p) w := by
  unfold spehLoc GlobalTheory.RowTie.twSum flat
  have hl : (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = (List.range p.d).map (fun a : ℕ => (a : ℝ)) := by
    simp [List.map_eq_flatMap]
  rw [hl, List.foldr_map, List.foldr_map]

theorem isoLoc_eq (P : List (Formalism.BasicNotions.Part A.CG)) (w : PlE H) :
    isoLoc N A P w = GlobalTheory.RowTie.twSum N A (P.flatMap (flat N A)) w := by
  induction P with
  | nil => rfl
  | cons p P ih => rw [List.flatMap_cons, twSum_append, ← ih, ← spehLoc_eq]; rfl

def toPair (p : Formalism.BasicNotions.Part A.CG) : (Σ a : ℕ, A.CG a) × ℕ := (⟨p.a, p.π⟩, p.d)

theorem toPair_injective : Function.Injective (toPair N A) :=
  Function.LeftInverse.injective (g := fun q => ⟨q.1.1, q.1.2, q.2⟩) fun _ => rfl

theorem coe_flatMap (P : List (Formalism.BasicNotions.Part A.CG)) :
    Multiset.ofList (P.flatMap (flat N A)) =
      ((Multiset.ofList (P.map (toPair N A))).bind seg).map fun q => (q.1, (q.2 : ℝ) / 2) := by
  induction P with
  | nil => simp
  | cons p P ih =>
    rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind,
      Multiset.map_add]
    congr 1
    unfold seg flat toPair
    rw [Multiset.map_map, ← Multiset.map_coe]
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring

theorem isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.IsobaricRigid N A → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A := by
  intro R H what₂ N A hR Pa Pa' h h' he
  have hpos : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ P.flatMap (flat N A), 1 ≤ q.1.1 := by
    intro P hP q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hq
    exact (hP p hp).1
  have hd : ∀ P : List (Formalism.BasicNotions.Part A.CG), (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) →
      ∀ q ∈ Multiset.ofList (P.map (toPair N A)), 1 ≤ q.2 := by
    intro P hP q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hq)
    exact (hP p hp).2.1
  have h1 := hR _ _ (hpos Pa h) (hpos Pa' h') (by simpa only [isoLoc_eq] using he)
  have h2 := Multiset.coe_eq_coe.2 h1
  rw [coe_flatMap, coe_flatMap] at h2
  have hinj : Function.Injective fun q : (Σ a : ℕ, A.CG a) × ℤ => (q.1, (q.2 : ℝ) / 2) := by
    intro q q' e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    simp only at e1 e2
    refine Prod.ext e1 ?_
    have : (q.2 : ℝ) = q'.2 := by linarith
    exact_mod_cast this
  have h3 := eq_of_bind_seg _ _ (hd Pa h) (hd Pa' h') (Multiset.map_injective hinj h2)
  rw [← Multiset.map_coe, ← Multiset.map_coe] at h3
  exact Multiset.coe_eq_coe.1 (Multiset.map_injective (toPair_injective N A) h3)

end GlobalTheory.SpehRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
section
namespace GlobalTheory.RowLaws

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem tie_unit (T : WDTie N A) (w : PlE H) :
    (T.e w (A.lpUnr w {1})).unr ∧ (T.e w (A.lpUnr w {1})).lpDim = 1 ∧
      (T.e w (A.lpUnr w {1})).frobEig = {1} := by
  obtain ⟨h1, h2, h3⟩ := A.lpUnr_spec w {1} (by simp)
  refine ⟨(T.unr w _).1 h1, ?_, ?_⟩
  · rw [T.dim, h3]; rfl
  · rw [← T.frobEig w _ h1, h2]

theorem paramLaws_of_tie (T : WDTie N A) : ParamLaws N A := by
  intro w
  refine ⟨fun a b χ h => (T.e w).injective ?_, fun χ h => (T.e w).injective ?_,
    fun a χ s h => (T.e w).injective ?_, fun a b χ h hab => ?_, fun a b c h => (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h, T.sum, T.sum, T.char _ _ _ h, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h, T.zero]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (WD.lpZero (h := N.plOm.2 w)) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.1
  · rw [T.char _ _ _ h, T.tw, T.tw, T.char _ _ _ h]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · apply (T.e w).injective
    have hχ : (T.e w χ).lpDim = 1 := by rw [T.dim, h]
    have := congrArg (T.e w) hab
    rw [T.char _ _ _ h, T.char _ _ _ h] at this
    exact _root_.GlobalTheory.WeilDeligne.lpChar_left_injective_of_lpDim_one _ _ _ _ _ _ _ _ hχ this
  · have := congrArg (T.e w) h
    rw [T.sum, T.sum] at this
    exact _root_.GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ _ this

theorem cancel_of_tie (T : WDTie N A) : Cancel N A := fun w a b c h => (paramLaws_of_tie T w).2.2.2.2 a b c h

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).1
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.1
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ (WD.lpZero (h := N.plOm.2 w)) _ s).2.2.1
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2]
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _ _ _ _ 0).2.2.2.1
  · rw [T.char _ _ _ h5]
    obtain ⟨u1, u2, u3⟩ := tie_unit T w
    exact (GlobalTheory.T.lp_char_compatibilities _ _ _ _ _
      (T.e w a) (WD.lpZero (h := N.plOm.2 w)) _ 0).2.2.2.2.2 u1 u2 u3

end GlobalTheory.RowLaws


open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain in
theorem GlobalTheory.RowLaws.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A :=
  fun _ _ _ _ _ T => ⟨GlobalTheory.RowLaws.paramLaws_of_tie T, GlobalTheory.RowLaws.charLaws_of_tie T, GlobalTheory.RowLaws.cancel_of_tie T⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowSizeOfUnitarySphericalComponent
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowSizeClosing

theorem rowSize_of_unitarySphericalComponent :
    ∀ (D : D7), GlobalTheory.RowSatakeBound.UnitarySphericalComponent D.nd D.naut → GlobalTheory.RowCopy.RowSize D :=
  fun D h => by
    intro i σ hσ w hw hu α hα
    have hb := GlobalTheory.RowSatakeBound.rowSize_of_component D.nd D.naut h i σ hσ w hw hu α hα
    simpa only [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hb

end GlobalTheory.RowSizeClosing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLiftOfPairLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem pairs_of_thetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (σ : what₂.FT) (P : A.AV i) (h : thetaOf N A i σ P) : GlobalTheory.ThetaExh.Pairs N A i σ P := by
  obtain ⟨hne, hle⟩ := h
  obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hF
  exact ⟨f, hf, _, hle hF, fun h0 => hF0 (inner_self_eq_zero.1 h0)⟩

theorem splitLift_of_pairLift : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.ThetaExh.SplitLift N A i :=
  fun _ _ _ N A i h σ P hθ => h σ P (pairs_of_thetaLift N A i σ P hθ)

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TraceEvalOriginEqFibreTraceStatement
section
open GlobalTheory GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_eval_origin_eq_fibre_trace : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ ev : rA k x {0} →ₐ[k] k, RingHom.ker ev = Ideal.span (Set.range fun j : Fin d => (⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩ : rA k x {0})) → ∀ (h : rB k K x {0}) (a : rA k x {0}), (a : F) = Algebra.trace F K (h : K) → ev a = Algebra.trace k ((rB k K x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : (rB k K x {0}))))) (Ideal.Quotient.mk _ h) := by
  first | (exact @GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (exact GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot) | (intros; apply GlobalTheory.PD.TraceOrigin.ev_eq_trace_quot  <;> assumption)
end

