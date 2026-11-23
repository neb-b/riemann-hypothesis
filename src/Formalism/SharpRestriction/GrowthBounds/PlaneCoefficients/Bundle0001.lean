module

public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Bundle0004

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PlanePairsOnBlocksAt
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Block

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (hk : m + 1 = r + K) {J : ℕ} [NeZero J]
  (nL : ZMod J → ℕ)

def BlockDeg (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ) : Prop :=
  ∀ x : TL J nL r, ∑ c, rho (x, c) + lowP Fr p x * (dPl x + dNo x) = dd (posOf n' (posTL Fr x))

theorem blockDeg_of (dd : Fin n' → ℕ) (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (mo : TV n' (m + 1) →₀ ℕ) (h1 : InLow Fr p hk nL rho mo) (h2 : InBlock Fr p hk nL dPl dNo mo)
    (h3 : ∀ t, ∑ c, mo (t, c) = dd t) : BlockDeg Fr p nL dd rho dPl dNo := by
  intro x
  rw [← h3, ← h2.1 x, ← h2.2 x]
  have e : ∑ c : Fin (m + 1), mo (posOf n' (posTL Fr x), c) =
      ∑ c : Fin (r + K), mo (posOf n' (posTL Fr x), Fin.cast hk.symm c) :=
    (Fintype.sum_equiv (finCongr hk.symm) _ _ (fun c => rfl)).symm
  rw [e, Fin.sum_univ_add, Fin.sum_univ_add]
  simp_rw [← h1.1 x, ← h1.2 x]
  have hA : ∑ a, mo (plVar Fr hk nL x a) = ∑ a, mo (plVar Fr hk nL x a) % lowP Fr p x +
      ∑ a, lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  have hB : ∑ b, mo (noVar Fr hk nL x b) = ∑ b, mo (noVar Fr hk nL x b) % lowP Fr p x +
      ∑ b, lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun a _ => (Nat.mod_add_div _ _).symm)
  change _ = ∑ a, mo (plVar Fr hk nL x a) + ∑ b, mo (noVar Fr hk nL x b)
  rw [hA, hB, mul_add, Finset.mul_sum, Finset.mul_sum]
  ring

end Block

def MemAtB (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (dd : Fin n' → ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J) (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ),
    TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL Dt dPl ka →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ), BlockDeg Fr p Dt.nL dd rho dPl dNo →
    ∀ (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        Dt.XX (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

section MemLin

variable (sc sL : ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ) (Y : ℝ) (N₁ G' cP : ℕ)
  (dd : Fin n' → ℕ)

def memSubB : Submodule (KK O) (MvPolynomial (TV n' (m + 1)) (KK O)) where
  carrier := {F | MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F}
  add_mem' := by
    intro F G hF hG J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_add, oneT_add, planeCoeff_add]
    exact XX_add Dt (hF J Dt dPl dNo ka hT rho hb e he nu) (hG J Dt dPl dNo ka hT rho hb e he nu)
  zero_mem' := by
    intro J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_zero, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt
  smul_mem' := by
    intro c F hF J _ Dt dPl dNo ka hT rho hb e he nu
    rw [levImg_smul, oneT_smul, planeCoeff_smul]
    exact XX_smul Dt c (hF J Dt dPl dNo ka hT rho hb e he nu)

theorem memAtG_of_B (F : MvPolynomial (TV n' (m + 1)) (KK O)) (hdeg : ∀ mo ∈ F.support, ∀ t, ∑ c, mo (t, c) = dd t)
    (h : MemAtB sc sL p O hk Fr deg Y N₁ G' cP dd F) : MemAtG sc sL p O hk Fr deg Y N₁ G' cP F := by
  intro J _ Dt dPl dNo ka hT rho e he nu
  by_cases hb : BlockDeg Fr p Dt.nL dd rho dPl dNo
  · exact h J Dt dPl dNo ka hT rho hb e he nu
  · have h0 : levImg Fr p hk Dt.nL rho dPl dNo F = 0 := by
      unfold levImg
      apply Finset.sum_eq_zero
      intro mo hmo
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.1 hmo
      exact absurd (blockDeg_of Fr p hk Dt.nL dd rho dPl dNo mo h2 h3 (hdeg mo h1)) hb
    rw [h0, oneT_zero, planeCoeff_zero]
    exact XX_zero Dt

end MemLin

def topDeg {n' k : ℕ} (ga : TV n' k →₀ ℕ) (t : Fin n') : ℕ := ∑ c, ga (t, c)

theorem castV_inj {n' m r K : ℕ} (hk : m + 1 = r + K) : Function.Injective (castV (n' := n') hk) := by
  intro u v huv
  have h1 : (castV hk u).1 = (castV hk v).1 := congrArg Prod.fst huv
  have h2 : (castV hk u).2 = (castV hk v).2 := congrArg Prod.snd huv
  exact Prod.ext h1 (Fin.cast_injective hk.symm h2)

theorem topDeg_castV {n' m r K : ℕ} (hk : m + 1 = r + K) (b : Fin n' × Fin (r + K) →₀ ℕ) (t : Fin n') :
    topDeg (b.mapDomain (castV hk)) t = ∑ c, b (t, c) := by
  unfold topDeg
  have hinj := castV_inj (n' := n') hk
  rw [← Fintype.sum_equiv (finCongr hk.symm) (fun c => (b.mapDomain (castV hk)) (t, Fin.cast hk.symm c)) _
    (fun c => rfl)]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact Finsupp.mapDomain_apply_of_injective hinj b (t, c)

def PlanePairsOnBlocksAt (C CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ)
    (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1) (F : Frames n' r) (nb : ℕ)
    (B : Fin nb → RRing O n' (r + K)),
    DataII C CLa p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar K F nb B →
    ∀ (E' : Fin n' → ℕ) (xs : ℤ → SegRing O r K),
      (∀ i : ℕ, i < F.J → xs i ∈ pairSet O r K F (i : ℤ)
        (g2mg p n' r K F (flatDeg lam0) (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x)
          (cPrime n' r TT.card c0 cpp cStar)) Y (i : ℤ)) (g2th p n' F (flatDeg lam0) (i : ℤ))) →
    ∀ l : Fin n' × Fin (r + K) →₀ ℕ, IsLabel p F l →
    ∀ ga ∈ (SPR O p F hrk (cPrime n' r TT.card c0 cpp cStar) (p ^ goodG' r de h x)).support,
      MemAtB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)
        (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t) (symG p O hk F l ga xs)

theorem rest5aMonoStep_of_B (C CLa : ℝ) (h : PlanePairsOnBlocksAt C CLa) : Lemma5aMonomialAt C CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K _ _ hk hrk
    F nb B hD b ga hga
  have hGen := hD.2.2.2.1.choose_spec.2 b
  set E' := hD.2.2.2.1.choose with hE'
  obtain ⟨xs, hxs, l, hl, hB, hdeg⟩ := hGen
  have e1 : MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (B b) * monomial ga 1) =
      symG p O hk F l ga xs := by rw [hB]; rfl
  apply memAtG_of_B 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)
  · intro mo hmo t
    have h1 := MvPolynomial.support_map_subset (algebraMap O (KK O)) _ hmo
    obtain ⟨d, hd, g, hg, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ h1)
    have hg' := MvPolynomial.support_monomial_subset hg
    rw [Finset.mem_singleton] at hg'
    subst hg'
    have hd' := hd
    rw [MvPolynomial.support_rename_of_injective (castV_inj hk)] at hd'
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hd'
    have h2 : ∑ c, b' (t, c) = G2d F (flatDeg lam0) E' t :=
      ((MvPolynomial.mem_restrictSupport_iff O).1 hdeg) hb' t
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    rw [← h2, ← topDeg_castV hk b' t]
    rfl
  rw [e1]
  let mS : ℕ := mStar p F (r + K) (orbitWindowCount r de h' x) (p ^ goodG' r de h' x) (cPrime n' r TT.card c0 cpp cStar)
  let Sj : ℤ → Set (SegRing O r K) := fun jj =>
    pairSet O r K F jj (g2mg p n' r K F (flatDeg lam0) mS Y jj) (g2th p n' F (flatDeg lam0) jj)
  have hspan : ∀ i : ℕ, i < F.J → xs i ∈ Submodule.span O (Sj i) := fun i _ =>
    symbol_spaces_le_pair_span CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h' x) (2 * TT.card)) mS a Y (i : ℤ) (hxs i)
  exact symG_span p O hk F (memSubB 0 (1 / 8) p O hk F (flatDeg lam0) Y (orbitWindowCount r de h' x) (goodG' r de h' x)
      (cPrime n' r TT.card c0 cpp cStar) (fun t => G2d F (flatDeg lam0) E' t + topDeg ga t)) Sj l ga
    (fun xs' hxs' => h p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h' x lam0 aT bT a Y cpp c0 Dp cStar K hk hrk F nb B hD
      E' xs' hxs' l hl ga hga)
    xs hspan

def PlanePairsOnBlocks (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → PlanePairsOnBlocksAt C CLa

theorem rest5aMono_of_B (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (h : PlanePairsOnBlocks D CLa Ck Crk Cdeg) :
    Lemma5aMonomial D CLa Ck Crk Cdeg := by
  intro hA
  obtain ⟨C₁, h1, h2⟩ := h hA
  exact ⟨C₁, h1, fun C hC => rest5aMonoStep_of_B C CLa (h2 C hC)⟩

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.UpdDModelLet
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Upd

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}

def updD (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) : SignedChainData p O r J :=
  SignedChainData.mk Dt.nL Dt.sgn d Dt.gP Dt.nch Dt.chain Dt.chain_mono Dt.chain_w th Dt.sl thL h Dt.ga Dt.ga_unit Dt.ga_dig
    Dt.c Dt.one_le_c

section With

variable (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m)

theorem updD_modelLet : (updD Dt d th thL h).modelLet = Dt.modelLet := by
  unfold SignedChainData.modelLet
  congr 1
  funext x
  cases x <;> rfl

theorem updD_trueLet : (updD Dt d th thL h).trueLet = Dt.trueLet := by
  unfold SignedChainData.trueLet
  congr 1
  funext x
  obtain ⟨j, s⟩ := x
  cases s <;> rfl

theorem updD_levToML (j) : (updD Dt d th thL h).levToML j = Dt.levToML j := by
  funext x
  cases x <;> rfl

theorem updD_chainML (j i) : (updD Dt d th thL h).chainML j i = Dt.chainML j i := by
  unfold SignedChainData.chainML
  rw [updD_levToML]
  rfl

theorem updD_TSet (j i) : (updD Dt d th thL h).TSet j i = Dt.TSet j i := rfl

theorem updD_digOK (rho) : (updD Dt d th thL h).digOK rho = Dt.digOK rho := rfl

theorem updD_liftVar : (updD Dt d th thL h).liftVar = Dt.liftVar := by
  funext x
  obtain ⟨⟨j, s⟩, a⟩ := x
  cases s <;> rfl

theorem updD_liftExp : (updD Dt d th thL h).liftExp = Dt.liftExp := by
  funext mo x
  obtain ⟨⟨j, s⟩, a⟩ := x
  cases s <;> rfl

theorem updD_Fdig (rho F) : (updD Dt d th thL h).Fdig rho F = Dt.Fdig rho F := by
  unfold SignedChainData.Fdig
  rw [updD_digOK, updD_liftVar, updD_liftExp]
  rfl

theorem updD_normE (K : ℕ) [NeZero K] [NeZero J] : normE p K (updD Dt d th thL h) = normE p K Dt := by
  unfold normE
  rw [updD_trueLet]
  rfl

theorem valS_congr3' {Kf : Type} [Field Kf] {ι : Type} {r : ℕ} [NeZero r] {LL LL' : Letters ι} {S S' : Set ι}
    {F F' : MvPolynomial (ι × Fin r) Kf} (h1 : LL = LL') (h2 : S = S') (h3 : F = F') :
    valS LL S F = valS LL' S' F' := by
  subst h1 h2 h3
  rfl

end With

variable [NeZero J] [NeZero r]

def XXg (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) : Prop :=
  F ∈ Pol (KK O) r d ∧
  (∀ (rho : (ZMod J × Fin r) × Fin r → ℕ) (j : ZMod J) (i : Fin (Dt.nch j)),
    geZ (valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho F)) (th j i)) ∧
  ∀ (j : ZMod J) (m : Fin r), m.val + 2 ≤ r → geZ (valS Dt.trueLet (Dt.TSet j m) F) (thL j m)

theorem updD_XX (Dt : SignedChainData p O r J) (d : TL J Dt.nL r → ℕ) (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ)
    (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O))
    (hF : (updD Dt d th thL h).XX F) : XXg Dt d th thL F := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · have e : valS Dt.modelLet (Dt.chainML j i) (Dt.Fdig rho F) =
        valS (updD Dt d th thL h).modelLet ((updD Dt d th thL h).chainML j i) ((updD Dt d th thL h).Fdig rho F) :=
      valS_congr3' (updD_modelLet Dt d th thL h).symm (updD_chainML Dt d th thL h j i).symm
        (updD_Fdig Dt d th thL h rho F).symm
    rw [e]
    exact h2 rho j i
  · have e : valS Dt.trueLet (Dt.TSet j m) F =
        valS (updD Dt d th thL h).trueLet ((updD Dt d th thL h).TSet j m) F :=
      valS_congr3' (updD_trueLet Dt d th thL h).symm (updD_TSet Dt d th thL h j m).symm rfl
    rw [e]
    exact h3 j m hm

end Upd

section Lev

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (deg : Fin n' → ℕ) (Y : ℝ) (k : ℕ) (mS : ℕ)
  {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {J : ℕ} (K : ℕ) [NeZero K]

def Base (Dt : SignedChainData p O r J) : Prop :=
  J = Fr.J ∧
  (∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) ∧
  (∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) ∧
  (∀ j (mm : Fin r), Dt.gP j mm = (Fr.fr (segZ j + 1) (r - 1) - Fr.fr (segZ j) (r - 1)).toNat) ∧
  (∀ j, Dt.nch j = Dt.nL j + 1) ∧
  (∀ j (i : Fin (Dt.nch j)), Dt.chain j i = {x | x.isRight} ∪ {x | ∃ l : Fin (Dt.nL j), x = Sum.inl l ∧ l.val < i.val})

def ThLe (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (Dt : SignedChainData p O r J) (ka : ZMod J → ℕ → Fin K → ℤ)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) : Prop :=
  (∀ j (i : Fin (Dt.nch j)), th j i ≤ thStar Fr p deg Y k mS Dt.nL K ka j i.val -
    sc * slU Fr p deg Y k Dt.nL j i.val - loss (segZ j) i.val) ∧
  ∀ j (mm : Fin r), mm.val + 2 ≤ r →
    thL j mm ≤ thStar Fr p deg Y k mS Dt.nL K ka j (Dt.nL j + (r - 1 - mm.val)) -
      sL * slU Fr p deg Y k Dt.nL j (Dt.nL j + (r - 1 - mm.val)) - loss (segZ j) (Dt.nL j + (r - 1 - mm.val))

end Lev

def MemLev (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) (F : MvPolynomial (TV n' (m + 1)) (KK O)) : Prop :=
  ∀ (dPl dNo : TL J Dt.nL r → ℕ) (ka : ZMod J → ℕ → Fin K → ℤ) (th : ∀ j, Fin (Dt.nch j) → ℝ)
    (thL : ZMod J → Fin r → ℝ), (∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm) →
    ThLe Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL loss Dt ka th thL →
    ∀ (rho : TL J Dt.nL r × Fin (r + K) → ℕ) (e : Module.End (KK O) (MvPolynomial (TL J Dt.nL r × Fin K) (KK O))),
      IsJProj (normE p K Dt) {fun i => ka i.1 i.2.val} e →
      ∀ nu : TL J Dt.nL r × Fin K →₀ ℕ,
        XXg Dt dPl th thL (planeCoeff nu (oneT e (levImg Fr p hk Dt.nL rho dPl dNo F)))

theorem memAtLe_iff (sc sL : ℝ) (loss : ℤ → ℕ → ℝ) (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type)
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (hk : m + 1 = r + K) (Fr : Frames n' r) (deg : Fin n' → ℕ)
    (Y : ℝ) (N₁ G' cP : ℕ) (F : MvPolynomial (TV n' (m + 1)) (KK O)) :
    MemAtLe sc sL loss p O hk Fr deg Y N₁ G' cP F ↔
      ∀ (J : ℕ) [NeZero J] (Dt : SignedChainData p O r J), Base Fr p Dt → MemLev sc sL loss p O hk Fr deg Y N₁ G' cP Dt F := by
  constructor
  · intro h J _ Dt hB dPl dNo ka th thL hpos hT rho e he nu
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hB
    exact updD_XX Dt dPl th thL hpos _ (h J (updD Dt dPl th thL hpos) dPl dNo ka ⟨b1, b2, b3, rfl, b4, b5, b6, hT.1, hT.2⟩ rho e
      (by rw [updD_normE]; exact he) nu)
  · intro h J _ Dt dPl dNo ka hT rho e he nu
    obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
    subst t4
    exact h J Dt ⟨t1, t2, t3, t5, t6, t7⟩ Dt.d dNo ka Dt.th Dt.thL Dt.thL_pos ⟨t8, t9⟩ rho e he nu

section TotallyRealRoots

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

def cost1 (s : Fin n') (jz : ℤ) (u : ℕ) : ℝ := if touchT Fr jz u s then 1 else 0

theorem opCost_eq (s : Fin n') (jz : ℤ) (u : ℕ) : opCost Fr s jz u = cost1 Fr s jz u + cost1 Fr s jz u := by
  unfold opCost cost1
  split_ifs <;> norm_num

end TotallyRealRoots

end Formalism.MainNotions.PairMembershipBlocks
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WithThModelLet
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

def withTh {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m) :
    SignedChainData p O r J :=
  SignedChainData.mk Dt.nL Dt.sgn Dt.d Dt.gP Dt.nch Dt.chain Dt.chain_mono Dt.chain_w th Dt.sl thL h Dt.ga Dt.ga_unit Dt.ga_dig
    Dt.c Dt.one_le_c

section With

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} (Dt : SignedChainData p O r J)
    (th : ∀ j, Fin (Dt.nch j) → ℝ) (thL : ZMod J → Fin r → ℝ) (h : ∀ j (m : Fin r), m.val + 2 ≤ r → 0 < thL j m)

theorem withTh_modelLet : (withTh Dt th thL h).modelLet = Dt.modelLet := by
  unfold SignedChainData.modelLet withTh
  congr 1
  funext x
  cases x <;> rfl

theorem withTh_trueLet : (withTh Dt th thL h).trueLet = Dt.trueLet := by
  unfold SignedChainData.trueLet withTh
  congr 1
  funext x
  obtain ⟨j, l | m⟩ := x <;> rfl

theorem withTh_levToML (j) : (withTh Dt th thL h).levToML j = Dt.levToML j := by
  funext x
  cases x <;> rfl

theorem withTh_chainML (j i) : (withTh Dt th thL h).chainML j i = Dt.chainML j i := by
  unfold SignedChainData.chainML
  rw [withTh_levToML]
  rfl

theorem withTh_TSet (j i) : (withTh Dt th thL h).TSet j i = Dt.TSet j i := rfl

theorem withTh_digOK (rho) : (withTh Dt th thL h).digOK rho = Dt.digOK rho := rfl

theorem withTh_liftVar : (withTh Dt th thL h).liftVar = Dt.liftVar := by
  funext x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

theorem withTh_liftExp : (withTh Dt th thL h).liftExp = Dt.liftExp := by
  funext mo x
  obtain ⟨⟨j, l | m⟩, a⟩ := x <;> rfl

theorem withTh_Fdig (rho F) : (withTh Dt th thL h).Fdig rho F = Dt.Fdig rho F := by
  simp only [SignedChainData.Fdig, withTh_digOK, withTh_liftVar, withTh_liftExp]
  rfl

theorem withTh_normE (K : ℕ) [NeZero K] [NeZero J] : normE p K (withTh Dt th thL h) = normE p K Dt := by
  unfold normE
  rw [withTh_trueLet]
  rfl

theorem XX_withTh [NeZero J] [NeZero r] (hth : ∀ j i, Dt.th j i ≤ th j i)
    (hthL : ∀ j (m : Fin r), m.val + 2 ≤ r → Dt.thL j m ≤ thL j m)
    (F : MvPolynomial (TL J Dt.nL r × Fin r) (KK O)) (hF : (withTh Dt th thL h).XX F) : Dt.XX F := by
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨h1, fun rho j i => ?_, fun j m hm => ?_⟩
  · have hx := h2 rho j i
    erw [withTh_modelLet, withTh_chainML, withTh_Fdig] at hx
    exact geZ_anti (hth j i) hx
  · have hx := h3 j m hm
    erw [withTh_trueLet, withTh_TSet] at hx
    exact geZ_anti (hthL j m hm) hx

end With

theorem restLeOfG : RestLeOfG := by
  intro sc sL p n' r K m _ _ _ O _ _ _ hk Fr deg Y N₁ G' cP F hG J _ Dt dPl dNo ka hT rho e he nu
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := hT
  let th : ∀ j, Fin (Dt.nch j) → ℝ := fun j i =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (i : ℕ) -
      sc * slU Fr p deg Y (r + K) Dt.nL j (i : ℕ)
  let thL : ZMod J → Fin r → ℝ := fun j mm =>
    thStar Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) Dt.nL K ka j (Dt.nL j + (r - 1 - (mm : ℕ))) -
      sL * slU Fr p deg Y (r + K) Dt.nL j (Dt.nL j + (r - 1 - (mm : ℕ)))
  have hpos : ∀ j (mm : Fin r), mm.val + 2 ≤ r → 0 < thL j mm := by
    intro j mm hmm
    have a := Dt.thL_pos j mm hmm
    have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact lt_of_lt_of_le a b
  have hT' : TwistedSubstitutionGrowthBound Fr p deg Y (r + K) (mStar p Fr (r + K) N₁ (p ^ G') cP) K sc sL
      (withTh Dt th thL hpos) dPl ka :=
    ⟨t1, t2, t3, t4, t5, t6, t7, fun j i => rfl, fun j mm _ => rfl⟩
  have hX := hG J (withTh Dt th thL hpos) dPl dNo ka hT' rho e (by rw [withTh_normE]; exact he) nu
  refine XX_withTh Dt th thL hpos (fun j i => ?_) (fun j mm hmm => ?_) _ hX
  · have b := t8 j i
    simp only [sub_zero] at b
    exact b
  · have b := t9 j mm hmm
    simp only [sub_zero] at b
    exact b

end Formalism.MainNotions.PairMembershipBlocks
end
end

