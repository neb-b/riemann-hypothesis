module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.Bundle0004
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0012
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothVec

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CreAnnApply
section
open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.GopEntries

open CompanionTheory.D.DSIC

variable {n : ℕ} {ε : Fin n → Bool}

def sgR (i : NC ε) (A : Finset (NC ε)) : ℝ := (-1) ^ (A.filter fun j => key j < key i).card

def hh (i j : NC ε) (A B : Finset (NC ε)) : ℝ :=
  if i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j then sgR i (A.erase i) * sgR j (B.erase j) else 0

def coef (c d : Fin n) (i j : NC ε) : ℝ :=
  (if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
    (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0)

def gg (c d : Fin n) (A B : Finset (NC ε)) : ℝ := ∑ i : NC ε, ∑ j : NC ε, coef c d i j * hh i j A B

lemma sg_eq (i : NC ε) (A : Finset (NC ε)) : sg i A = (sgR i A : ℂ) := by
  simp [sg, sgR]

lemma sgR_erase (i : NC ε) (A : Finset (NC ε)) : sgR i (A.erase i) = sgR i A := by
  unfold sgR
  congr 2
  ext j
  simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨?_, h⟩, h'⟩
    rintro rfl
    exact lt_irrefl _ h'

lemma sgR_mul_self (i : NC ε) (A : Finset (NC ε)) : sgR i A * sgR i A = 1 := by
  unfold sgR
  rw [← mul_pow]; simp

lemma hh_symm (i j : NC ε) (A B : Finset (NC ε)) : hh i j A B = hh j i B A := by
  unfold hh
  by_cases h : i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, mul_comm]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩)]

lemma coef_symm (c d : Fin n) (i j : NC ε) : coef c d i j = coef d c j i := by
  unfold coef
  congr 1
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl
  · exact if_congr ⟨fun h => ⟨h.2.1, h.1, h.2.2.symm⟩, fun h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩ rfl rfl

lemma cre_ann_apply {V : Type} [AddCommGroup V] [Module ℂ V] (i j : NC ε) (x : Ch ε V)
    (A : Finset (NC ε)) :
    (cre i * ann j : Module.End ℂ (Ch ε V)) x A = ∑ B, (hh i j A B : ℂ) • x B := by
  change (if i ∈ A then sg i A • (if j ∈ A.erase i then 0 else
    sg j (A.erase i) • x (insert j (A.erase i))) else 0) = _
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    by_cases hj : j ∈ A.erase i
    · rw [if_pos hj, smul_zero]
      symm
      refine Finset.sum_eq_zero fun B _ => ?_
      have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
        rintro ⟨_, _, h⟩
        rw [h] at hj
        exact Finset.notMem_erase _ _ hj
      simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
    · rw [if_neg hj, Finset.sum_eq_single (insert j (A.erase i))]
      · have : i ∈ A ∧ j ∈ insert j (A.erase i) ∧ A.erase i = (insert j (A.erase i)).erase j :=
          ⟨hi, mem_insert_self _ _, (Finset.erase_insert hj).symm⟩
        rw [hh, if_pos this, Finset.erase_insert hj, sgR_erase, smul_smul, sg_eq, sg_eq,
          Complex.ofReal_mul]
      · intro B _ hB
        have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := by
          rintro ⟨_, h1, h⟩
          apply hB
          rw [h, Finset.insert_erase h1]
        simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]
      · intro h; exact absurd (mem_univ _) h
  · rw [if_neg hi]
    symm
    refine Finset.sum_eq_zero fun B _ => ?_
    have : ¬ (i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j) := fun h => hi h.1
    simp only [hh, if_neg this, Complex.ofReal_zero, zero_smul]

lemma Gop_apply {V : Type} [AddCommGroup V] [Module ℂ V] (c d : Fin n) (x : Ch ε V)
    (A : Finset (NC ε)) : Gop ε c d x A = ∑ B, (gg c d A B : ℂ) • x B := by
  have hc : ∀ i j : NC ε, ((if i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2 then 1 else 0) -
      (if i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1 then 1 else 0) : ℂ) = (coef c d i j : ℂ) := by
    intro i j
    unfold coef
    split_ifs <;> simp
  unfold Gop gg
  simp only [hc, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    cre_ann_apply, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma wtA_erase (i : NC ε) (A : Finset (NC ε)) (hi : i ∈ A) :
    wtA A = wtA (A.erase i) + Pi.single i.1.1 1 - Pi.single i.1.2 1 := by
  funext c
  have key : ∀ (p : NC ε → Prop) [DecidablePred p],
      ((A.filter p).card : ℝ) = (((A.erase i).filter p).card : ℝ) + if p i then 1 else 0 := by
    intro p _
    conv_lhs => rw [← Finset.insert_erase hi, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]; simp
    · simp
  simp only [wtA, Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  rw [key (fun i => i.1.1 = c), key (fun i => i.1.2 = c)]
  simp only [eq_comm (a := c)]
  ring

lemma exists_of_ne {c d : Fin n} {A B : Finset (NC ε)} (h : gg c d A B ≠ 0) :
    ∃ i j : NC ε, ((i.1.1 = c ∧ j.1.1 = d ∧ i.1.2 = j.1.2) ∨ (i.1.2 = d ∧ j.1.2 = c ∧ i.1.1 = j.1.1)) ∧
      i ∈ A ∧ j ∈ B ∧ A.erase i = B.erase j := by
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨j, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨i, j, ?_, ?_⟩
  · by_contra h'
    rw [not_or] at h'
    exact left_ne_zero_of_mul h (by rw [coef, if_neg h'.1, if_neg h'.2, sub_zero])
  · by_contra h'
    exact right_ne_zero_of_mul h (by rw [hh, if_neg h'])

lemma gg_diag (c : Fin n) (A B : Finset (NC ε)) : gg c c A B = if A = B then wtA A c else 0 := by
  have h1 : ∀ i : NC ε, ∑ j : NC ε, coef c c i j * hh i j A B = coef c c i i * hh i i A B := by
    intro i
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (mem_univ _) h)
    have e1 : ¬ (i.1.1 = c ∧ j.1.1 = c ∧ i.1.2 = j.1.2) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext (b.trans a.symm) e.symm))
    have e2 : ¬ (i.1.2 = c ∧ j.1.2 = c ∧ i.1.1 = j.1.1) := by
      rintro ⟨a, b, e⟩
      exact hj (Subtype.ext (Prod.ext e.symm (b.trans a.symm)))
    rw [coef, if_neg e1, if_neg e2, sub_zero, zero_mul]
  unfold gg
  simp only [h1]
  split_ifs with h
  · subst h
    have h2 : ∀ i : NC ε, hh i i A A = if i ∈ A then 1 else 0 := by
      intro i
      unfold hh
      by_cases hi : i ∈ A
      · simp [hi, sgR_mul_self]
      · simp [hi]
    simp only [h2, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp [coef, wtA, Finset.sum_sub_distrib]
  · refine Finset.sum_eq_zero fun i _ => ?_
    have : ¬ (i ∈ A ∧ i ∈ B ∧ A.erase i = B.erase i) := by
      rintro ⟨a, b, e⟩
      apply h
      rw [← Finset.insert_erase a, e, Finset.insert_erase b]
    rw [hh, if_neg this, mul_zero]

theorem gFacts : GFacts := by
  intro n ε
  refine ⟨gg, fun V _ _ c d x A => Gop_apply c d x A, fun c d A B => ?_, fun c d A B h => ?_,
    gg_diag, fun c d A hdc => ?_⟩
  · unfold gg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [coef_symm, hh_symm]
  · obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    refine ⟨?_, ?_⟩
    · rw [← Finset.card_erase_add_one hi, e, Finset.card_erase_add_one hj]
    · rw [wtA_erase i A hi, wtA_erase j B hj, e]
      rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
      · rw [a, b, f]; abel
      · rw [a, b, f]; abel
  · by_contra h
    obtain ⟨i, j, hc, hi, hj, e⟩ := exists_of_ne h
    have hn : i ∉ (A1 ε).erase j := e ▸ Finset.notMem_erase i A
    apply hn
    simp only [A1, mem_filter, mem_univ, true_and, mem_erase] at hj ⊢
    rcases hc with ⟨a, b, f⟩ | ⟨a, b, f⟩
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (b.symm.trans a)
      · rw [a, f]; rw [b] at hj; exact hj.trans hdc
    · refine ⟨?_, ?_⟩
      · rintro rfl
        exact hdc.ne (a.symm.trans b)
      · rw [a, f]; rw [b] at hj; exact hdc.trans hj

end GlobalTheory.CompanionTheory.GopEntries
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantMonoidElementsAreAntitonePowersStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_monoid_elements_are_antitone_powers : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | exact GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone | (intros; apply GlobalTheory.CompanionTheory.CartGL.closure_tGen_antitone <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsCocycleOfMapToDegreeOneTerm
section
open Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.ChainHighest

open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
open PI.UpqRep (lowK)

theorem kRel_map {n : ℕ} {A B : Type} [Ring A] [Ring B] (ε : Fin n → Bool) (f : A →+* B)
    (F : Fin n → Fin n → A) (h : KRel ε F) : KRel ε (fun a b => f (F a b)) := by
  intro a b c d hab hcd
  have := congrArg f (h a b c d hab hcd)
  simp only [map_sub, map_mul] at this
  rw [this]
  congr 1 <;> split_ifs <;> simp

theorem fdual_single {n : ℕ} {ε : Fin n → Bool} {U : Type} [AddCommGroup U] [Module ℂ U]
    (EU : Fin n → Fin n → Module.End ℂ U) (g : Fin n → Fin n → Finset (NC ε) → Finset (NC ε) → ℝ)
    (hg : ∀ (c d : Fin n) (x : Ch ε U) (A : Finset (NC ε)), Gop ε c d x A = ∑ B, (g c d A B : ℂ) • x B)
    (a b : Fin n) (A B : Finset (NC ε)) (u : U) :
    Fdual ε EU a b (Pi.single A u) B =
      (Pi.single A (EU a b u) : Ch ε U) B - (g b a B A : ℂ) • u := by
  unfold Fdual
  rw [LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg]
  congr 1
  · by_cases h : B = A
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single A]
    · simp
    · intro C _ hC; simp [hC]
    · simp

theorem aux₃ : FRel → GFacts → GamDom → KHWExists → HWMap → PRV := by
  intro hF hG hγ hK hM n ε lam V _ _ E v S hlam hE hEu hv hS hSt hvS
  obtain ⟨γ, hγ1, hγ2⟩ := hγ n ε lam hlam
  obtain ⟨U, _, _, _, EU, u, hU, hUu, hu0, hu⟩ := hK n ε γ hγ2
  obtain ⟨g, hg, hgs, hgc, hgd, hgl⟩ := hG n ε
  let T : Type := PiLp 2 (fun _ : Finset (NC ε) => U)
  let e : Ch ε U ≃ₗ[ℂ] T := (WithLp.linearEquiv 2 ℂ (Finset (NC ε) → U)).symm
  have he : ∀ (x : Ch ε U) A, (e x).ofLp A = x A := fun _ _ => rfl
  let ET : Fin n → Fin n → Module.End ℂ T := fun a b => e.conjRingEquiv.toRingHom (Fdual ε EU a b)
  have hET : ∀ a b x, ET a b (e x) = e (Fdual ε EU a b x) := by
    intro a b x
    rfl
  have hTrel : KRel ε ET := kRel_map ε _ _ (hF n ε U EU hU).2
  have hTu : KUnit ε ET := by
    intro a b hab x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [hET, hET, PiLp.inner_apply, PiLp.inner_apply]
    simp only [he, Fdual, LinearMap.sub_apply, Pi.sub_apply, lift_apply, hg, inner_sub_left,
      inner_sub_right, Finset.sum_sub_distrib, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal]
    congr 1
    · exact Finset.sum_congr rfl fun A _ => hUu a b hab _ _
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
      rw [hgs b a B A]
  have ht0 : e (Pi.single (A1 ε) u) ≠ 0 := by
    intro h
    have := he (Pi.single (A1 ε) u) (A1 ε)
    rw [h] at this
    apply hu0
    simpa using this.symm
  have ht : KHighest ε ET (lowK ε lam) (e (Pi.single (A1 ε) u)) := by
    constructor
    · intro a
      rw [hET, ← map_smul]
      congr 1
      funext B
      rw [fdual_single EU g (hg U), hu.1 a, hgd]
      by_cases h : B = A1 ε
      · subst h
        have h1 := hγ1 a
        simp only [gam, Pi.add_apply] at h1
        simp only [Pi.single_eq_same, if_true, Pi.smul_apply, ← sub_smul, ← h1]
        congr 1
        push_cast
        ring
      · simp [h]
    · intro a b hab hε
      rw [hET, map_eq_zero_iff _ e.injective]
      funext B
      rw [fdual_single EU g (hg U), hu.2 a b hab hε, hgl b a B hab]
      simp
  obtain ⟨φ, hφ1, hφ2⟩ := hM n ε T V ET E (lowK ε lam) _ v S hTrel hTu hE hEu ht0 ht hv hS hSt hvS
  let c : Ch ε V := fun A => if A.card = (A1 ε).card then φ (e (Pi.single A u)) else 0
  have key : ∀ a b, ε a = ε b → ∀ A, Fop ε E a b c A =
      if A.card = (A1 ε).card then φ (e (Pi.single A (EU a b u))) else 0 := by
    intro a b hab A
    unfold Fop
    rw [LinearMap.add_apply, Pi.add_apply, lift_apply, hg]
    by_cases hA : A.card = (A1 ε).card
    · have h1 : Fdual ε EU a b (Pi.single A u) =
          Pi.single A (EU a b u) - ∑ B, (g a b A B : ℂ) • (Pi.single B u : Ch ε U) := by
        funext B
        rw [fdual_single EU g (hg U), Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single B, hgs b a B A]
        · simp
        · intro C _ hC; simp [hC.symm]
        · simp
      have h2 : ∀ B, (g a b A B : ℂ) • c B = (g a b A B : ℂ) • φ (e (Pi.single B u)) := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_true]
      simp only [h2]
      simp only [c, hA, if_true]
      rw [← hφ2 a b hab, hET, h1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sub, map_sum, map_smul]
      abel
    · have h2 : ∀ B, (g a b A B : ℂ) • c B = 0 := by
        intro B
        by_cases h0 : g a b A B = 0
        · simp [h0]
        · have := (hgc a b A B h0).1
          simp only [c, ← this, hA, if_false, smul_zero]
      simp only [h2]
      simp [c, hA]
  refine ⟨c, fun A hA => by simp [c, hA], ⟨fun a => ?_, fun a b hab hε => ?_⟩, by simp [c, hφ1]⟩
  · funext A
    rw [key a a rfl, hu.1 a, Pi.smul_apply, hγ1 a]
    by_cases hA : A.card = (A1 ε).card
    · simp only [c, hA, if_true]
      rw [Pi.single_smul, map_smul, map_smul]
    · simp [c, hA]
  · funext A
    rw [key a b hε, hu.2 a b hab hε]
    simp

end GlobalTheory.CompanionTheory.ChainHighest
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasDerivAtExt
section
open Matrix Filter Topology
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmBracket

open CompanionTheory.D.Upq.Sm
open PI.UpqRep (UJset IsURepOn inG)
open PI.PhMeasCore (dsig smoothVecs)

theorem fderiv_comm {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → G} {x : E} (hF : ContDiffAt ℝ ∞ F x) (L M : E →L[ℝ] E) {a b c : E}
    (ha : M x = a) (hb : L x = b) (hc : L a - M b = c) :
    fderiv ℝ (fun g => fderiv ℝ F g (L g)) x a - fderiv ℝ (fun g => fderiv ℝ F g (M g)) x b =
      fderiv ℝ F x c := by
  subst ha hb hc
  have hD : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 1) (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).differentiableAt (by simp)
  have hs : IsSymmSndFDerivAt ℝ F x :=
    hF.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 le_top)
  rw [(hD.hasFDerivAt.clm_apply L.hasFDerivAt).fderiv, (hD.hasFDerivAt.clm_apply M.hasFDerivAt).fderiv]
  simp [hs (M x) (L x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem lie_bracket {J X Y : Mat n} (hX : Xᴴ * J + J * X = 0) (hY : Yᴴ * J + J * Y = 0) :
    (X * Y - Y * X)ᴴ * J + J * (X * Y - Y * X) = 0 := by
  have hLX : Xᴴ * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have hLY : Yᴴ * J = -(J * Y) := eq_neg_of_add_eq_zero_left hY
  have e1 : Yᴴ * Xᴴ * J = J * (Y * X) := by
    rw [Matrix.mul_assoc, hLX, Matrix.mul_neg, ← Matrix.mul_assoc, hLY, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  have e2 : Xᴴ * Yᴴ * J = J * (X * Y) := by
    rw [Matrix.mul_assoc, hLY, Matrix.mul_neg, ← Matrix.mul_assoc, hLX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
  rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub]
  abel

variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem hasDerivAt_ext (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {f F : Mat n → H}
    {U : Set (Mat n)} (hU : IsOpen U) (hgU : g ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ x ∈ U, x ∈ G → f x = F x) :
    HasDerivAt (fun t => f (g * ex X t)) (fderiv ℝ F g (g * X)) 0 :=
  hasDerivAt_local (A := G) (γ := fun t => g * ex X t) (fun t => h.mul_mem _ hg _ (hX t))
    (by simp [ex_zero]) (hasDerivAt_mul_ex g X) hU hgU hF hfF

theorem ds_ds (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G) {v : H}
    (hv : IsSm G σ v) {F : Mat n → H} {U : Set (Mat n)} (hU : IsOpen U) (h1 : (1 : Mat n) ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ x ∈ U, x ∈ G → σ x v = F x) (L : Mat n →L[ℝ] Mat n)
    (hL : ∀ x, L x = x * Y) :
    ds σ X (ds σ Y v) = fderiv ℝ (fun g => fderiv ℝ F g (L g)) 1 X := by
  have hG : ContDiffOn ℝ ∞ (fun g => fderiv ℝ F g (L g)) U :=
    (hF.fderiv_of_isOpen hU (by simp)).clm_apply L.contDiff.contDiffOn
  have hGe : ∀ g ∈ U, g ∈ G → σ g (ds σ Y v) = fderiv ℝ F g (L g) := by
    intro g hg hgG
    rw [apply_ds h hY hgG (hv.differentiableAt h hY), hL]
    exact (hasDerivAt_ext h (f := fun x => σ x v) hY hgG hU hg hF hfF).deriv
  have h2 := hasDerivAt_ext h (f := fun g => σ g (ds σ Y v)) hX h.one_mem hU h1 hG hGe
  simp only [Matrix.one_mul] at h2
  exact h2.deriv

theorem ds_bracket (h : RepOn G σ) {X Y : Mat n} (hX : ∀ t, ex X t ∈ G) (hY : ∀ t, ex Y t ∈ G)
    (hXY : ∀ t, ex (X * Y - Y * X) t ∈ G) {v : H} (hv : IsSm G σ v) :
    ds σ X (ds σ Y v) - ds σ Y (ds σ X v) = ds σ (X * Y - Y * X) v := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  have h2 := hasDerivAt_ext h (f := fun x => σ x v) hXY h.one_mem hU h1 hF hfF
  simp only [Matrix.one_mul] at h2
  have e : ds σ (X * Y - Y * X) v = fderiv ℝ F 1 (X * Y - Y * X) := h2.deriv
  let L : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ Y).toContinuousLinearMap
  have hL : ∀ x, L x = x * Y := by intro x; simp [L]
  let M : Mat n →L[ℝ] Mat n := (LinearMap.mulRight ℝ X).toContinuousLinearMap
  have hM : ∀ x, M x = x * X := by intro x; simp [M]
  rw [ds_ds h hX hY hv hU h1 hF hfF L hL, ds_ds h hY hX hv hU h1 hF hfF M hM, e]
  exact fderiv_comm (hF.contDiffAt (hU.mem_nhds h1)) L M ((hM 1).trans (Matrix.one_mul X))
    ((hL 1).trans (Matrix.one_mul Y)) (congrArg₂ (· - ·) (hL X) (hM Y))

theorem smBracket : CompanionTheory.D.DSIC.SmBracket := by
  intro n ε H _ _ σ hσ X Y hX hY v hv
  have h : RepOn (UJset ε) σ :=
    ⟨by simp [UJset, PI.UpqRep.inUJ], fun a ha b hb => Formalism.REAL.indefinite_unitary_mul_mem ε ha hb, hσ.1.1, hσ.1.2⟩
  have hex : ∀ Z, inG ε Z → ∀ t, ex Z t ∈ UJset ε := fun Z hZ t => Formalism.REAL.exp_indefinite_unitary_holds n ε Z hZ t
  exact ds_bracket h (hex X hX) (hex Y hY) (hex _ (lie_bracket hX hY)) hv

theorem smBracket_of : CompanionTheory.D.DSIC.SmLin → CompanionTheory.D.DSIC.SmBracket := fun _ => smBracket

end GlobalTheory.CompanionTheory.SmBracket
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.NearIdentityUpperLowerFactorizationStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.near_identity_upper_lower_factorization : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ), 0 ≤ r → r < 1 → ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) → ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧ (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | exact GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation | (intros; apply GlobalTheory.CompanionTheory.CartGL.IwahoriLU.iwahori_factorisation <;> assumption)
end

