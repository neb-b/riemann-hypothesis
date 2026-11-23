module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

theorem GenericFibreVar.proof : GenericFibreVar.Statement := by
  intro K _ ι _ Ω _ y D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (mCoordIdeal y).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ mCoordIdeal y → m = 0 := by
    intro m hm
    have h1 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hm
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) = KH.genIdeal y := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · show (mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)) = _
      rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq
      (D + Fintype.card K) _ ?_
    rw [hform, hdim, show D + 1 + Fintype.card K = (D + Fintype.card K) + 1 by omega]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubquot

set_option linter.unusedSectionVars false

theorem iSupIndep_comap {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (p j).comap g) ≤ (⨆ (j) (_ : j ≠ i), p j).comap g :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  have h0 := (Submodule.disjoint_def.mp (hp i)) (g x) (Submodule.mem_comap.mp hx) (Submodule.mem_comap.mp (hle hx'))
  exact hg (by rw [h0, map_zero])

theorem iSupIndep_map_of_ker_le {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨x, hx, rfl⟩ := hy
  have hy2 : f x ∈ (⨆ (j) (_ : j ≠ i), p j).map f := by
    simpa only [Submodule.map_iSup] using hy'
  obtain ⟨z, hz, hzx⟩ := hy2
  have hk : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  have hk' := hL hk
  rw [iSup_split_single (fun c => LinearMap.ker f ⊓ p c) i, Submodule.mem_sup] at hk'
  obtain ⟨l, hl, w, hw, hlw⟩ := hk'
  have hw1 : w ∈ ⨆ (j) (_ : j ≠ i), p j :=
    (show (⨆ (j) (_ : j ≠ i), LinearMap.ker f ⊓ p j) ≤ ⨆ (j) (_ : j ≠ i), p j from
      iSup₂_mono fun j _ => inf_le_right) hw
  have hxl : x - l ∈ p i := sub_mem hx (Submodule.mem_inf.mp hl).2
  have hxl' : x - l ∈ ⨆ (j) (_ : j ≠ i), p j := by
    have e : x - l = z + w := by
      calc x - l = (x - z) - l + z := by abel
        _ = z + w := by rw [← hlw]; abel
    rw [e]
    exact Submodule.add_mem _ hz hw1
  have h0 := (Submodule.disjoint_def.mp (hp i)) (x - l) hxl hxl'
  rw [sub_eq_zero.mp h0]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k


variable (S ι) in
def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}

theorem monTimes_subset_span (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by
  rintro _ ⟨u, h, hh, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hh)

theorem span_monTimes_le (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S :=
  Submodule.span_le.mpr (monTimes_subset_span H)

theorem monomial_smul_mem (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx

theorem span_le_span_monTimes (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by
  let T : Submodule (MRingOver S ι) M :=
    { carrier := Submodule.span S (monTimes S ι H)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro p y hy
        refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
        · have e : (monomial u a : MRingOver S ι) = a • monomial u (1 : S) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [e, smul_assoc]
          exact Submodule.smul_mem _ a (monomial_smul_mem H u hy)
        · rw [add_smul]
          exact Submodule.add_mem _ hp hq }
  have hT : Submodule.span (MRingOver S ι) H ≤ T := by
    rw [Submodule.span_le]
    intro h hh
    have e : h = (monomial 0 (1 : S) : MRingOver S ι) • h := by
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_smul]
    exact Submodule.subset_span ⟨0, h, hh, e⟩
  exact fun x hx => hT hx

theorem monTimes_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩

theorem mem_iSup_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN

end GradedSubquot


open GradedSubquot in
theorem GradedSubquot.proof : GradedSubquot.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 G H hM hG hH hGH

  have hind : iSupIndep (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) :=
    iSupIndep_comap hM.1.submodule_iSupIndep ((Submodule.span (MRingOver S ι) H).subtype.restrictScalars S)
      (fun a b h => Subtype.ext h)
  have hsup : ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    exact (show (⨆ c, ((Submodule.span (MRingOver S ι) H).comap (Submodule.span (MRingOver S ι) H).subtype).restrictScalars S ⊓
        subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) ≤ ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c from
      iSup_mono fun c => inf_le_right) (mem_iSup_inf hM hH le_rfl x x.2)
  refine ⟨⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup,
    fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩, ?_⟩

  set L := (Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype with hLdef
  set f := L.mkQ.restrictScalars S with hfdef
  have hker : LinearMap.ker f = L.restrictScalars S := by
    ext x
    simp [hfdef]
  have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) := by
    rw [hker]
    intro x hx
    exact mem_iSup_inf hM hG hGH x hx
  have hind2 := iSupIndep_map_of_ker_le hind f hL
  have hsup2 : ⨆ c, quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) L c = ⊤ := by
    change ⨆ c, (subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c).map f = ⊤
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective L
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
  rintro a c p _ hp ⟨x, hx, rfl⟩
  exact ⟨p • x, hM.2 a c p (x : M) hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem nefOnF_mono {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {I : IFamily F ι} {V Q : Ideal (MRingOver F ι)} {α : K → ℤ} (hN : KH.NefOnF I V α) (hVQ : V ≤ Q) :
    KH.NefOnF I Q α :=
  fun W hW hQW => hN W hW (hVQ.trans hQW)

theorem ampleV_of_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {V : Ideal (MRingOver S ι)} {N : K → ℤ} {q : ℕ} (hq : 1 ≤ q)
    (h : KH.AmpleV S V (q • N)) : KH.AmpleV S V N := by
  obtain ⟨q₂, hq₂, hgen, hvan⟩ := h
  refine ⟨q₂ * q, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, fun e => ?_⟩
  · rwa [mul_smul]
  · obtain ⟨c₁, hc⟩ := hvan e
    refine ⟨c₁, fun c hc' => ?_⟩
    have := hc c hc'
    rwa [smul_smul, mul_assoc] at this

theorem KleimanScheme.proof (hVar : KleimanVarietyH1Generation.Statement) (hDev : H1GenerationDevissage.Statement)
    (hGen : GenerationOfH1GenAmple.Statement) (hAG : AmpleOfGenTwist.Statement) : KleimanScheme.Statement := by
  intro F _ K _ _ ι _ _ I V α b a hI hV hN hb ha

  have hamp : H1GenAmple F V (b • α + fun _ => (a : ℤ)) :=
    hDev F K ι V _ inferInstance fun P hP hVP => hVar F K ι I P α b a hI hP (nefOnF_mono hN hVP) hb ha

  obtain ⟨c₁, hc⟩ := hGen F K ι V _ hV hamp (fun _ => -1)
  have hg := hc (c₁ + 1) (Nat.le_succ c₁)

  have h := hAG F K ι V _ 1 1 hV hg le_rfl
  have e : ((1 : ℕ) : ℤ) • ((fun _ => (-1 : ℤ)) + (c₁ + 1) • (b • α + fun _ => (a : ℤ))) +
      (fun _ => ((1 : ℕ) : ℤ)) = (c₁ + 1) • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Nat.cast_one, one_smul, Pi.add_apply]
    ring
  rw [e] at h
  exact ampleV_of_nsmul (Nat.le_add_left 1 c₁) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKrullDimMatAct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KrullDimMatAct

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def coneAdjoinQ (x : J → Ω) : Subalgebra ℚ (Polynomial Ω) :=
  Algebra.adjoin ℚ (Set.range fun j => Polynomial.C (x j) * Polynomial.X)

theorem mem_coneAdjoinQ_matAct (A : Matrix J J ℚ) (x : J → Ω) (i : J) :
    Polynomial.C (matAct A x i) * Polynomial.X ∈ coneAdjoinQ x := by
  have h : Polynomial.C (matAct A x i) * Polynomial.X =
      ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [matAct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]
  rw [h]
  exact Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _

theorem coneAdjoinQ_matAct_le (A : Matrix J J ℚ) (x : J → Ω) :
    coneAdjoinQ (matAct A x) ≤ coneAdjoinQ x :=
  Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)

theorem coneAdjoinQ_matAct_eq {B : Matrix J J ℚ} (hB : IsInvMat B) (x : J → Ω) :
    coneAdjoinQ (matAct B x) = coneAdjoinQ x := by
  classical
  obtain ⟨B', _, hB'B⟩ := isInvMat_mul hB
  refine le_antisymm (coneAdjoinQ_matAct_le B x) ?_
  have h := coneAdjoinQ_matAct_le B' (matAct B x)
  rwa [matAct_matAct hB'B] at h

theorem ringKrullDim_quot_coordIdeal (x : J → Ω) :
    ∃ s : ℕ, Algebra.trdeg ℚ (coneAdjoinQ x) = s ∧
      ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x) = (s : WithBot ℕ∞) + 1 := by
  obtain ⟨s, h1, h2⟩ := GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker
    (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)
  have hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) =
      fun j => Polynomial.C (x j) * Polynomial.X :=
    funext fun v => by simp [coneMap]
  rw [hX] at h1
  exact ⟨s, h1, h2⟩

theorem proof : KrullDimMatAct.Statement := by
  intro Ω _ _ J _ x B hB
  obtain ⟨s, hs, hds⟩ := ringKrullDim_quot_coordIdeal (matAct B x)
  obtain ⟨t, ht, hdt⟩ := ringKrullDim_quot_coordIdeal x
  rw [coneAdjoinQ_matAct_eq hB, ht] at hs
  have hst : s = t := by exact_mod_cast hs.symm
  rw [hds, hdt, hst]

end KrullDimMatAct

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem RelLatticeFinite.proof (hL : RelSectionsLarge.Statement) : RelLatticeFinite.Statement := by
  intro K _ ι _ Ω _ y a n m g hy
  have hN : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := adjoin_isNoetherianRing g
  obtain ⟨n₁, hn₁⟩ := hL K ι Ω (Algebra.adjoin ℤ (Set.range g)) hN y hy
  choose c0 hc0 using hy
  set R := Algebra.adjoin ℤ (Set.range g)
  let e : K → ℕ := fun k => n₁ + ((n : ℤ) * a k).natAbs
  let b : K → ℕ := fun k => ((n : ℤ) * a k + e k).toNat
  have hb : ∀ k, ((b k : ℕ) : ℤ) = (n : ℤ) * a k + e k := by
    intro k
    refine Int.toNat_of_nonneg ?_
    simp only [e]
    push_cast
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  have hbn : ∀ k, n₁ ≤ b k := by
    intro k
    have h1 := hb k
    simp only [e] at h1
    push_cast at h1
    have := neg_abs_le ((n : ℤ) * a k)
    omega
  set mon : Ω := ∏ k, y ⟨k, c0 k⟩ ^ e k
  have hmon : mon ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  let φ : Ω →ₗ[R] Ω := LinearMap.mulRight R mon
  have hφ : Function.Injective φ := mul_left_injective₀ hmon
  have hmap : (relChartLat R y a n).map φ ≤ relSecM R y b := by
    rintro _ ⟨s, hs, rfl⟩
    exact hn₁ b hbn (mul_prod_mem_relChartLat R y e c0 (fun k => hb k) hs)
  have : IsNoetherian R (relSecM R y b) := isNoetherian_of_fg_of_noetherian _ (relSecM_fg R y b)
  exact Submodule.fg_of_fg_map_injective φ hφ (Submodule.FG.of_le_of_isNoetherian hmap)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockOldPartSurj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockOldPartSurj.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    (∀ j, v j ∈ chartLat y a m) → KH.GeneratesOn y (fun k => (m : ℤ) * a k) v →
    ∀ x ∈ mcPts (mCoordIdeal y), ∃ z ∈ mcPts (mCoordIdeal (addBlock y v)), basePart₂ z = x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

