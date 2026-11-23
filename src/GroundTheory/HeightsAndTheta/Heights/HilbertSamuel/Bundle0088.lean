module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0065
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0085
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CechHcSubsingletonOfBij
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace H1VanishingDevissage

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem cechHc_subsingleton_iff (𝓜 : (K → ℤ) → Submodule S M) (c : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι 𝓜 c n) ↔ KH.cechZc ι 𝓜 c n ≤ KH.cechBc ι 𝓜 c n := by
  show Subsingleton (_ ⧸ _) ↔ _
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem locPart_shift (𝓜 : (K → ℤ) → Submodule S M) (T : Submonoid (MRingOver S ι)) (c x : K → ℤ) :
    KH.locPart ι (fun d => 𝓜 (d + c)) T x = KH.locPart ι 𝓜 T (x + c) := by
  have h : ∀ a : K → ℕ, x + (fun k => (a k : ℤ)) + c = x + c + fun k => (a k : ℤ) :=
    fun _ => add_right_comm _ _ _
  simp only [KH.locPart, h]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem cechCc_shift (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    KH.cechCc ι (fun d => 𝓜 (d + c)) x n = KH.cechCc ι 𝓜 (x + c) n := by
  simp only [KH.cechCc, locPart_shift]

theorem cechHc_shift_iff (𝓜 : (K → ℤ) → Submodule S M) (c x : K → ℤ) (n : ℕ) :
    Subsingleton (KH.cechHc ι (fun d => 𝓜 (d + c)) x n) ↔ Subsingleton (KH.cechHc ι 𝓜 (x + c) n) := by
  rw [cechHc_subsingleton_iff, cechHc_subsingleton_iff]
  cases n <;> simp only [KH.cechZc, KH.cechBc, cechCc_shift]


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem isMGraded_shift {𝓜 : (K → ℤ) → Submodule S M} (h : KH.IsMGraded S ι 𝓜) (c : K → ℤ) :
    KH.IsMGraded S ι (fun d => 𝓜 (d + c)) := by
  refine ⟨?_, fun a d p m hp hm => ?_⟩
  · have h1 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top 𝓜).1 h.1
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨h1.1.comp (add_left_injective c), ?_⟩
    rw [← h1.2]
    exact (Equiv.addRight c).iSup_comp (g := 𝓜)
  · have := h.2 a (d + c) p m hp hm
    rwa [add_right_comm] at this

theorem cechHc_subsingleton_of_bij (hSES : KH.CechSESStatement)
    {A B : Type} [AddCommGroup A] [Module (MRingOver S ι) A] [Module S A] [IsScalarTower S (MRingOver S ι) A]
    [AddCommGroup B] [Module (MRingOver S ι) B] [Module S B] [IsScalarTower S (MRingOver S ι) B]
    (𝓐 : (K → ℤ) → Submodule S A) (𝓑 : (K → ℤ) → Submodule S B) (g : A →ₗ[MRingOver S ι] B)
    (hA : KH.IsMGraded S ι 𝓐) (hB : KH.IsMGraded S ι 𝓑) (hg : KH.IsMGradedMap S ι 𝓐 𝓑 g)
    (hinj : Function.Injective g) (hsurj : Function.Surjective g) (c : K → ℤ) (n : ℕ)
    (h : Subsingleton (KH.cechHc ι 𝓐 c n)) : Subsingleton (KH.cechHc ι 𝓑 c n) := by
  have hhG : KH.IsMGradedMap S ι 𝓑 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hex : LinearMap.range g = LinearMap.ker (0 : B →ₗ[MRingOver S ι] PUnit) := by
    rw [LinearMap.range_eq_top.2 hsurj, LinearMap.ker_zero]
  have hU' : Subsingleton (KH.cechHc ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) c n) := by
    have : Subsingleton (KH.CechC S ι PUnit n) :=
      ⟨fun f g => funext fun I => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  exact (hSES S K ι A B PUnit 𝓐 𝓑 _ g 0 hA hB isMGraded_punit hg hhG hinj
    (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex c n).1 h hU'

end H1VanishingDevissage

theorem H1VanishingDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) : H1VanishingDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _).1⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hml : m l ∈ F (j + 1) := Submodule.subset_span ⟨l, Nat.lt_succ_self j, rfl⟩

      let ψ : MRingOver S ι →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        LinearMap.toSpanSingleton _ _ (L.mkQ ⟨m l, hml⟩)
      have hψ : ∀ p, ψ p = L.mkQ (p • ⟨m l, hml⟩) := fun p => (L.mkQ.map_smul p _).symm
      have hker : ∀ p, ψ p = 0 ↔ p ∈ 𝔭 l := by
        intro p
        rw [hψ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hcol l p
      let φ : (MRingOver S ι ⧸ 𝔭 l) →ₗ[MRingOver S ι] (F (j + 1) ⧸ L) :=
        (𝔭 l).liftQ ψ fun p hp => (LinearMap.mem_ker).2 ((hker p).2 hp)
      have hφ : ∀ p, φ (Ideal.Quotient.mk (𝔭 l) p) = ψ p := fun _ => rfl
      have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1
        (Submodule.ker_liftQ_eq_bot _ _ _ fun p hp => (hker p).1 (LinearMap.mem_ker.1 hp))

      have hdec : ∀ y ∈ F (j + 1), ∃ p : MRingOver S ι, y - p • m l ∈ F j := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact ⟨0, by rw [zero_smul, sub_zero]; exact Submodule.subset_span ⟨l', h, rfl⟩⟩
          · exact ⟨1, by rw [one_smul, show l' = l from Fin.ext h, sub_self]; exact (F j).zero_mem⟩
        | zero => exact ⟨0, by rw [zero_smul, sub_zero]; exact (F j).zero_mem⟩
        | add x y _ _ hx hy =>
          obtain ⟨p, hp⟩ := hx
          obtain ⟨p', hp'⟩ := hy
          refine ⟨p + p', ?_⟩
          have : x + y - (p + p') • m l = (x - p • m l) + (y - p' • m l) := by rw [add_smul]; abel
          rw [this]
          exact (F j).add_mem hp hp'
        | smul a x _ hx =>
          obtain ⟨p, hp⟩ := hx
          refine ⟨a * p, ?_⟩
          rw [mul_smul, ← smul_sub]
          exact (F j).smul_mem a hp
      have hsurj : Function.Surjective φ := by
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        obtain ⟨p, hp⟩ := hdec y y.2
        refine ⟨Ideal.Quotient.mk (𝔭 l) p, ?_⟩
        rw [hφ, hψ, Submodule.mkQ_apply, Submodule.Quotient.eq]
        show ((p • ⟨m l, hml⟩ - y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_sub, Submodule.coe_smul, ← neg_sub]
        exact (F j).neg_mem hp
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        ·
          obtain ⟨c₂, hc₂⟩ := hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (e + -c l)
          have hA := isMGraded_shift (QuotPartGraded.proof S K ι (𝔭 l) (h𝔭 l).2.1) (-c l)
          have hG : KH.IsMGradedMap S ι (fun d => KH.quotPart S (𝔭 l) (d + -c l))
              (quotGrading (subGrading 𝓜 (F (j + 1))) L) φ := by
            intro d x hx
            refine (Submodule.span_le (p := (quotGrading (subGrading 𝓜 (F (j + 1))) L d).comap
              (φ.restrictScalars S))).2 ?_ hx
            rintro _ ⟨p, ⟨h0, hp⟩, rfl⟩
            refine ⟨p • ⟨m l, hml⟩, ?_, (hψ p).symm⟩
            have h := hgr.2 _ (c l) p (m l) hp (hm l)
            have hd : c l + (fun k => (((d + -c l) k).toNat : ℤ)) = d := by
              funext k
              have := h0 k
              simp only [Pi.add_apply, Pi.neg_apply] at this ⊢
              rw [Int.toNat_of_nonneg this]
              ring
            rw [hd] at h
            exact h
          refine ⟨c₂, fun n hn => cechHc_subsingleton_of_bij hSES _ _ φ hA hq hG hinj hsurj _ _ ?_⟩
          rw [cechHc_shift_iff, show e + n • N + -c l = e + -c l + n • N by abel]
          exact hc₂ n hn
        · have hirr : ¬ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => (h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _).1⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          refine loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩) fun y => ?_
          obtain ⟨y, rfl⟩ := hsurj y
          obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [← LinearMap.map_smul, show (X ⟨k, i⟩ : MRingOver S ι) • Ideal.Quotient.mk (𝔭 l) p' =
            Ideal.Quotient.mk (𝔭 l) (X ⟨k, i⟩ * p') from rfl, hφ]
          exact (hker _).2 (Ideal.mul_mem_right _ _ (hk i))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      exact (hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1).1
        (hc₀ n (le_of_max_le_left hn)) (hc₂ n (le_of_max_le_right hn))
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  exact ⟨c₁, fun n hn => cechHc_subsingleton_of_bij hSES _ 𝓜 (F r).subtype (hgrF r) hgr (fun _ _ hx => hx)
    (Submodule.injective_subtype _) (fun y => ⟨⟨y, hFr ▸ Submodule.mem_top⟩, rfl⟩) _ _ (hc₁ n hn)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenerationOfH1Vanishing.proof (hU : ClosedPtGenUniform.Statement) (hC : GenNearCover.Statement) :
    GenerationOfH1Vanishing.Statement := by
  intro S _ K _ _ ι _ _ V N hS hH M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨c₂, hc₂⟩ := hH M 𝓜 hfin hgr hV e
  obtain ⟨c₃, hc₃⟩ := hC S K ι V M 𝓜 (fun c => e + c • N) hS hgr hV
    (fun P hP _ => hU S K ι V N hS hH M 𝓜 hfin hgr hV e P hP)
  exact ⟨max c₂ c₃, fun c hc => ⟨hc₂ c (le_of_max_le_left hc), hc₃ c (le_of_max_le_right hc)⟩⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace G1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (b : Fin n → K → ℤ),
    (∀ j k, 0 ≤ b j k) → 0 ≤ geoNum n V b
  | 0, V, b, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, b, hb => by
    rw [geoNum]
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_
      exact finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.init b) fun j k => hb _ k)
    · exact le_rfl

theorem finsum_nonpos' {α : Sort*} {g : α → ℝ} (h : ∀ x, g x ≤ 0) : ∑ᶠ x, g x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -g x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

theorem mcPts_anti {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem exists_monomial_not_mem {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ monomial μ (1 : ℤ) ∉ P := by
  classical
  choose c hc using hP.2.2
  let μ : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  refine ⟨μ, fun k => ?_, ?_⟩
  · simp [μ]
  · intro hmem
    have := hP.1
    rw [monomial_eq, C_1, one_mul, Finsupp.prod] at hmem
    obtain ⟨p, hp, hpP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    have hX := hP.1.mem_of_pow_mem _ hpP
    have hμp : μ p ≠ 0 := Finsupp.mem_support_iff.1 hp
    obtain ⟨k, j⟩ := p
    by_cases hj : j = c k
    · subst hj
      exact hc k hX
    · exact hμp (by simp [μ, hj])

theorem isMultiHomog_monomial {μ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ (1 : ℤ)) a := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact hμ k

theorem eval_monomial_one (μ : (Σ k, ι k) →₀ ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
  rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  intro p
  simp

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 A.h (γ y) :=
    (hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) := hh.log (A.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem arInt_nonpos {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {s : MRing ι}
    (hs : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) (e : ℕ) :
    arInt P s A (fun _ : Fin e => A) ≤ 0 := by
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z))
        (logNorm A s) y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        have hpos := A.pos _ hz.1
        have hg : logNorm A s (hγ.choose y) ≤ 0 :=
          Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
            ((div_le_one hpos).2 (hs _ hz))
        exact mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos' fun w => finsum_nonpos' fun _ => key w
  · exact le_rfl

theorem nonneg_of_family (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (a : K → ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = fun k => (a k : ℤ))
    (P0 : Ideal (MRing ι)) (n : ℕ) :
    ∀ P : Ideal (MRing ι), IsArithVar P n → P0 ≤ P → IsSemipositiveRel P0 P A →
      MonomialsBounded P A a → 0 ≤ I P n (fun _ => A) := by
  induction n with
  | zero =>
    intro P hP
    exact (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim
  | succ m ih =>
    intro P hP hP0 hsp hmb
    obtain ⟨μ, hμ, hμP⟩ := exists_monomial_not_mem hP.2.1 a
    set s : MRing ι := monomial μ (1 : ℤ) with hsdef
    have hsa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a := isMultiHomog_monomial hμ
    have hAa : ∀ k, A.a k = a k := fun k => by rw [hA]
    have hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z := by
      intro z hz
      rw [hsdef, eval_monomial_one]
      exact hmb z hz μ hμ
    have hR := hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP
    have hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = fun _ => A := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hconst] at hR
    rw [hR, recR]
    refine sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m)
      (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))
    have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
    split_ifs with hH
    · have hWar := (divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH
      exact ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩
        (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')
    · refine mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_))
        (Real.log_natCast_nonneg _)
      simp [hA]

end G1

theorem G1.proof : G1.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _
  exact G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

theorem BlockResolutionMixedBridge.proof : BlockResolutionMixedBridge.Statement := by
  intro D K _ _ ι _ Ω _ _ d L A₁ hL hdeg hA₁
  have hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (mCoordIdeal d.y) Ψ :=
    goodProjExists K ι (mCoordIdeal d.y) D d.arith
  set B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := A₁.tensor d.A.inv with hBdef
  have hB0 : B.a = 0 := by
    funext k
    simp [B, HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, hdeg, d.deg]
  have hgl : (fun z => Real.log (A₁.h z / d.A.h z)) = logNorm B.inv 1 := by
    funext z
    rw [logNorm_inv_one]
    simp only [B, HermLine.tensor, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.inv, div_eq_mul_inv]
  have hBs : IsSmoothHerm B.inv :=
    isSmoothHerm_inv (isSmoothHerm_tensor hA₁ (isSmoothHerm_inv d.semipos.1))
  have hsec : IsSectionOn (mCoordIdeal d.y) B.inv 1 := isSectionOn_inv_one d.arith.2.1.1 hB0
  have key := AnResBridge.bridge d.R hex.choose L B.inv 1 d.arith hex.choose_spec hL hBs hsec
  have hgr : (fun x => Real.log (A₁.h (blockPt d x) / d.A.h (blockPt d x))) =
      fun x => logNorm B.inv 1 (d.R.lift x x) :=
    funext fun x => congrFun hgl (d.R.lift x x)
  unfold ptsIntegral
  rw [dite_eq_left hex, hgl, hgr]
  exact key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

