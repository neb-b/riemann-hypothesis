module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CechZero
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni]

private theorem cech_zero {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    {G : Finset ι → Submodule ℂ E} {n : ℤ} {y : Finset ι → E} (hy : y ∈ (cech G).Z n)
    (s : Finset ι) (h : (s.card : ℤ) ≠ n + 1) : y s = 0 := by
  have h1 : y s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then G s else ⊥) := hy.1 s (Set.mem_univ s)
  rw [if_neg (fun h' => h h'.2)] at h1
  simpa using h1

private theorem res_mu {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] (τ : DR ℂ K →ₗ[K] K) (ρ : F →ₗ[ℂ] ℂ) (e f w : DR ℂ K) :
    resP (DR ℂ K) ρ (muP F K τ (e ⊗ₜ f) w) = trF ℂ τ ρ (e * w) • f := by
  simp [muP, resP, trF]

end UpperTheory.Gal.productCup_of_system.PartialZeroIdentity

open UpperTheory.Gal.productCup_of_system.PartialZeroIdentity in
theorem UpperTheory.Gal.productCup_of_system.zId_of :
    ZAct → RCupTop → KunDec → SysBasic → GoodZ → ZId := by
  intro hZA hRC hKD hSB hGZ F K _ _ _ _ _ _ d x hFC τ hT ρ hR a ha c hc hD
  have htop : top c ∈ (sysZ K x a).mix.Z (d + 2) :=
    (hSB d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).2.2.1 c hc
  obtain ⟨m, p, e, f, hk, hB⟩ := hKD (Fin (d + 1)) (DR ℂ K) (DR ℂ K)
    (fun s => omB ℂ K (rB ℂ K (xv x) s) (d - a)) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) d
    (hGZ F K d x hFC (d - a)).2.2 (hGZ F K d x hFC a).2.2 (top c) htop
  refine ⟨m, p, e, f, hk, hB, ?_⟩
  intro q α hα
  have h1 := hZA F K d x hFC τ hT ρ hR a q ha c hc hD α hα
  have h2 := hRC F K d x hFC τ hT ρ hR a q ha _ hB α hα
  have hzero : ∀ k, p k ≠ q → pr K τ ρ (e k) α = 0 := by
    intro k hkq
    simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
      LinearMap.proj_apply, LinearMap.mul_apply']
    refine Finset.sum_eq_zero fun j _ => ?_
    have hc1 : ((Finset.univ.filter (· ≤ j)).card : ℤ) = (j : ℤ) + 1 := by
      rw [Finset.filter_ge_eq_Iic, Fin.card_Iic]; push_cast; ring
    have hc2 : ((Finset.univ.filter (j ≤ ·)).card : ℤ) = (d : ℤ) + 1 - j := by
      rw [Finset.filter_le_eq_Ici, Fin.card_Ici]; have := j.2; omega
    by_cases hA : ((Finset.univ.filter (· ≤ j)).card : ℤ) = ((d : ℤ) - p k) + 1
    · have : α (Finset.univ.filter (j ≤ ·)) = 0 := by
        refine cech_zero hα _ ?_
        rw [hc2]; rw [hc1] at hA
        intro h; apply hkq; omega
      simp [this]
    · have : e k (Finset.univ.filter (· ≤ j)) = 0 := cech_zero (hk k).2.1 _ hA
      simp [this]
  have key : ∀ J, resP (DR ℂ K) ρ (∑ i, muP F K τ
      ((∑ k, join (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) (e k) (f k))
        (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
      ∑ k ∈ Finset.univ.filter (fun k => p k = q), pr K τ ρ (e k) α • f k J := by
    intro J
    rw [Finset.sum_filter_of_ne (fun k _ hne => ?_)]
    · set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, join, lft_uni', rgt_uni', TensorProduct.mk_apply, map_sum,
        LinearMap.sum_apply, res_mu]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [pr, cupPair, LinearMap.sum_apply, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply,
        LinearMap.proj_apply, LinearMap.mul_apply', Finset.sum_smul]
    · by_contra hpq
      exact hne (by rw [hzero k hpq, zero_smul])
  have hfin := add_mem h1 h2
  convert hfin using 1
  ext J
  simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
  rw [← key J]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, map_sum, LinearMap.sum_apply]
  abel
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeDifferentialIdentityApply
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem acx_off {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) ≠ n) : c s = 0 := by
  have hc' : c ∈ Submodule.pi Set.univ (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) := hc
  have h := (Submodule.mem_pi.1 hc') s (Set.mem_univ s)
  rw [if_neg hs] at h
  simpa using h

private theorem acx_on {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) = n) : c s ∈ A s := by
  have hc' : c ∈ Submodule.pi Set.univ (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) := hc
  have h := (Submodule.mem_pi.1 hc') s (Set.mem_univ s)
  rwa [if_pos hs] at h

private theorem cubeDifferential_identity_apply {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (c : Finset σ → E) (t : Finset σ) :
    wd (fun _ => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • c (t.erase i) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem pk_mem {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dite_eq_left h]
  exact I.min'_mem h

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S)

private theorem col_KE (hRS : RS) (hKS : KSub) (hOk : SysOk) (hG : T.Good) (hAd : T.admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (e : Fin d ↪o κ)
    (h : KE (kos T.act (T.M I J) fun l => T.r n z (pk I) (pk J) (e l)) d) :
    KE (T.colCx n z I J) d := by
  have hr := ((hOk d S E T κ n z hG hAd).2.1 I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  have hk := (hKS S E T.act κ (T.R I J) (T.M I J) (T.r n z (pk I) (pk J)) (hG.stab I J hI hJ) hr).1 d e h
  intro m hm x hx
  have hR := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun _ => rfl) m x
  exact hR.2.2.1.2 (hk m hm (hR.2.1.1 hx))

private theorem col_B (hRS : RS) (hKS : KSub) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hOk : SysOk) (hG : T.Good) (hAd : T.admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (e : Fin d ↪o κ)
    (h : KE (kos T.act (T.M I J) fun l => T.r n z (pk I) (pk J) (e l)) d)
    (x : Finset κ → E) (hx : x ∈ (T.colCx n z I J).Z d)
    (hm : unsc T.act (T.u n (pk I) (pk J)) x (img e) ∈
      sm T.act (T.M I J) (Set.range fun j => T.r n z (pk I) (pk J) (e j))) :
    x ∈ (T.colCx n z I J).B d := by
  have hr := ((hOk d S E T κ n z hG hAd).2.1 I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  have hR := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun _ => rfl) d x
  exact hR.2.2.1.2 (hK2 S E T.act κ (T.R I J) (T.M I J) (T.r n z (pk I) (pk J)) d e (hG.stab I J hI hJ) hr h _
    (hR.2.1.1 hx) hm)

private theorem core (hU : WdUni) (hW : WdBasic) (hB : SysBasic) (hOk : SysOk) (hL1 : CechKoszulSystemBoundaryCriterion)
    (hG : T.Good) (hAd : T.admitted n z)
    (hK : ∀ I J, I.Nonempty → J.Nonempty → KE (T.colCx n z I J) d) (p : ℕ)
    (c : Finset (Two d ⊕ₗ κ) → E) (hc : c ∈ (T.cx n z).Z ((d : ℤ) + p + 2))
    (hlev : ∀ (b : Finset (Two d)) (L : Finset κ), d < L.card → c (uni b L) = 0)
    (Y : Finset (Two d) → Finset κ → E)
    (hY : ∀ b, Y b = 0 ∨ ((lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1 ∧
      Y b ∈ (T.colCx n z (lft b) (rgt b)).Z d))
    (hfin : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I.card + J.card = p + 2 →
      ∀ e ∈ (T.colCx n z I J).Z d,
        (∀ L, e L = c (uni (uni I J) L) - wd (fun _ => (1 : Module.End ℂ E)) (fun b' => Y b' L) (uni I J)) →
        e ∈ (T.colCx n z I J).B d) :
    c ∈ (T.cx n z).B ((d : ℤ) + p + 2) := by
  have hl : ∀ (b : Finset (Two d)) (L : Finset κ), lft (uni b L) = b := fun b L =>
    (hU (Two d) κ E (fun _ => 0) (fun _ => 0) b L).2.1
  have hr : ∀ (b : Finset (Two d)) (L : Finset κ), rgt (uni b L) = L := fun b L =>
    (hU (Two d) κ E (fun _ => 0) (fun _ => 0) b L).2.2.1
  have hl2 : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.1
  have hr2 : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.2.1
  have hcard : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.2.2.1
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = (d : ℤ) + p + 2 := ⟨_, rfl⟩
  rw [← hN] at hc ⊢
  let y : Finset (Two d ⊕ₗ κ) → E := fun s => Y (lft s) (rgt s)
  have hyu : ∀ b L, y (uni b L) = Y b L := fun b L => by simp only [y, hl, hr]
  have hYs : ∀ b L, L.card ≠ d → Y b L = 0 := by
    intro b L hL
    rcases hY b with h | ⟨_, _, _, h⟩
    · rw [h]; rfl
    · exact acx_off _ _ d (Y b) h.1 L (by exact_mod_cast hL)
  have hYz : ∀ b, wd (fun l => T.wt z (inrE l)) (Y b) = 0 := by
    intro b
    rcases hY b with h | ⟨_, _, _, h⟩
    · rw [h, map_zero]
    · exact h.2
  have hyC : y ∈ (T.cx n z).C (N - 1) := by
    refine ((hB d S E T κ n z (N - 1)).2.1 y).2 fun I J => ?_
    have hcolE : col y (uni I J) = Y (uni I J) := by
      funext L
      exact hyu _ _
    rw [hcolE]
    rcases hY (uni I J) with h | ⟨h1, h2, h3, h4⟩
    · rw [h]
      exact Submodule.zero_mem _
    · rw [hl2] at h1
      rw [hr2] at h2
      rw [hl2, hr2] at h4
      rw [hcard] at h3
      rw [if_pos ⟨h1, h2⟩]
      have e1 : N - 1 - (I.card : ℤ) - J.card = d := by
        have : (I.card : ℤ) + J.card = p + 1 := by exact_mod_cast h3
        omega
      rw [e1]
      exact h4.1
  have hIs := (hW _ E _ (T.wt z)).2.1 (hOk d S E T κ n z hG hAd).1 (N - 1) y hyC
  have hDy : wd (T.wt z) y ∈ (T.cx n z).Z N := by
    refine ⟨?_, ?_⟩
    · have := hIs.1
      rwa [sub_add_cancel] at this
    · exact hIs.2
  have hval : ∀ b L, (c - wd (T.wt z) y) (uni b L) =
      c (uni b L) - wd (fun _ => (1 : Module.End ℂ E)) (fun b' => Y b' L) b := by
    intro b L
    have h1 := (hU (Two d) κ E (T.wt z) y b L).1
    have h2 : (fun L' => y (uni b L')) = Y b := by
      funext L'
      exact hyu _ _
    have h3 : (fun b' => y (uni b' L)) = fun b' => Y b' L := by
      funext b'
      exact hyu _ _
    rw [h2, h3, hYz b, Pi.zero_apply, smul_zero, add_zero] at h1
    rw [Pi.sub_apply, h1]
    rfl
  have hc' : c - wd (T.wt z) y ∈ (T.cx n z).Z N := Submodule.sub_mem _ hc hDy
  have hlev' : ∀ (b : Finset (Two d)) (L : Finset κ), d < L.card → (c - wd (T.wt z) y) (uni b L) = 0 := by
    intro b L hL
    have h0 : (fun b' => Y b' L) = 0 := by
      funext b'
      exact hYs b' L hL.ne'
    rw [hval, hlev b L hL, h0, map_zero]
    simp
  have hcols : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → ((I.card + J.card : ℕ) : ℤ) = N - d →
      col (c - wd (T.wt z) y) (uni I J) ∈ (T.colCx n z I J).B d := by
    intro I J hI hJ hIJ
    have hcard2 : I.card + J.card = p + 2 := by
      have : ((I.card + J.card : ℕ) : ℤ) = ((p + 2 : ℕ) : ℤ) := by
        rw [hIJ, hN]
        push_cast
        ring
      exact_mod_cast this
    have hZ := (hB d S E T κ n z N).2.2.2.2.1 _ hc' I J hI hJ (fun I' J' L hlt => by
      by_cases hL : d < L.card
      · exact hlev' _ L hL
      · refine (hB d S E T κ n z N).1 _ hc'.1 I' J' L (Or.inr (Or.inr ?_))
        have h1 : ((I'.card + J'.card + L.card : ℕ) : ℤ) < ((d + p + 2 : ℕ) : ℤ) := by
          have : I'.card + J'.card + L.card < d + p + 2 := by omega
          exact_mod_cast this
        rw [hN]
        push_cast at h1 ⊢
        omega)
    have e1 : N - (I.card : ℤ) - J.card = d := by
      push_cast at hIJ
      omega
    rw [e1] at hZ
    exact hfin I J hI hJ hcard2 _ hZ fun L => hval _ L
  have hfinal := hL1 d S E T κ n z N hG hAd hK _ hc' hlev' hcols
  have hsum : c = (c - wd (T.wt z) y) + wd (T.wt z) y := by abel
  rw [hsum]
  exact Submodule.add_mem _ hfinal (Submodule.mem_map_of_mem hyC)

end

theorem UpperTheory.Gal.productCup_of_system.pCmp_of :
    PLift → ColP → CechKoszulSystemBoundaryCriterion → SysBasic → SysOk → KoszulBoundaryOfComponentMemIdeal → KSub → RS → GoodZ → ThMuLat → MuSpan → ActsLin → WdUni → PCmp := by
  intro hLift hColP hL1 hB hOk hK2 hKS hRS hGood hThLat _ hAct hU F K _ _ _ _ _ _ d x hx a p c hc hlev γ hγ hval
  obtain ⟨τ, hτ⟩ := hx.exists_isTop
  have hG : (sysP K x a).Good := (hGood F K d x hx a).2.1
  have hAd := (hThLat d _ _ (sysP K x a) hG).1
  obtain ⟨γ', hγ', rfl⟩ := hγ
  have hex : ∀ b : Finset (Two d), ∃ yb : Finset (Mi d) → F ⊗[ℂ] DR ℂ K,
      (yb = 0 ∨ ((lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1 ∧
        yb ∈ ((sysP K x a).colCx n11 (sysP K x a).mu (lft b) (rgt b)).Z d)) ∧
      ∀ L : Finset (Mi d), L.card = d → mulP F K (yb L) = kap K x L • γ' b := by
    intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1
    · have hm := acx_on _ _ _ γ' hγ' b (by rw [h.2.2]; push_cast; ring)
      have hm' : γ' b ∈ omB ℂ K (rB ℂ K (xv x) (lft b ∪ rgt b)) a := by
        simpa only [mixF, if_pos (And.intro h.1 h.2.1)] using hm
      obtain ⟨yb, h1, h2⟩ := hLift F K d x hx a (lft b) (rgt b) h.1 h.2.1 _ hm'
      exact ⟨yb, Or.inr ⟨h.1, h.2.1, h.2.2, h1⟩, h2⟩
    · have h0 : γ' b = 0 := by
        by_cases hb : b.card = p + 1
        · have hm := acx_on _ _ _ γ' hγ' b (by rw [hb]; push_cast; ring)
          have hn : ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) := fun h' => h ⟨h'.1, h'.2, hb⟩
          simpa only [mixF, if_neg hn, Submodule.mem_bot] using hm
        · exact acx_off _ _ _ γ' hγ' b (by
            intro h'
            apply hb
            have : (b.card : ℤ) = ((p + 1 : ℕ) : ℤ) := by rw [h']; push_cast; ring
            exact_mod_cast this)
      refine ⟨0, Or.inl rfl, fun L _ => ?_⟩
      simp [h0]
  choose Y hY1 hY2 using hex
  have hKE : ∀ I J, I.Nonempty → J.Nonempty → KE ((sysP K x a).colCx n11 (sysP K x a).mu I J) d :=
    fun I J hI hJ => col_KE _ _ _ hRS hKS hOk hG hAd I J hI hJ (dj (pk J))
      (hColP F K d x hx a I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  refine core (sysP K x a) n11 (sysP K x a).mu hU wdBasic_of hB hOk hL1 hG hAd hKE p c hc hlev Y hY1 ?_
  intro I J hI hJ _ e he heq
  have hP := hColP F K d x hx a I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)
  refine col_B _ _ _ hRS hKS hK2 hOk hG hAd I J hI hJ (dj (pk J)) hP.1 e he ?_
  have hR := hRS _ _ (sysP K x a).act (Mi d) ((sysP K x a).M I J) ((sysP K x a).u n11 (pk I) (pk J))
    ((sysP K x a).r n11 (sysP K x a).mu (pk I) (pk J)) (sysP K x a).mu (fun _ => rfl) d e
  have hcardL : (img (dj (d := d) (pk J))).card = d := by simp [img]
  refine hP.2 _ (acx_on _ _ _ _ (hR.2.1.1 he).1 _ (by rw [hcardL])) ?_
  show mulP F K ((sysP K x a).act _ (e _)) = 0
  rw [(hAct F K d x hx τ hτ a).2.2.2.2.1]
  have h0 : mulP F K (e (img (dj (pk J)))) = 0 := by
    have hv : mulP F K (c (uni (uni I J) (img (dj (pk J))))) = kap K x (img (dj (pk J))) •
        wd (fun _ => (1 : Module.End ℂ (DR ℂ K))) γ' (uni I J) := hval _ _ hcardL
    set_option synthInstance.maxHeartbeats 100000 in
      rw [heq, map_sub, hv, sub_eq_zero, cubeDifferential_identity_apply, cubeDifferential_identity_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hY2 _ _ hcardL, smul_comm]
  rw [h0, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IdJCriterion
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem ext_comm_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (v : M) (q : ℕ)
    (w : ExteriorAlgebra R M) (hw : w ∈ ⋀[R]^q M) :
    ExteriorAlgebra.ι R v * w = ((-1 : ℤ) ^ q) • (w * ExteriorAlgebra.ι R v) := by
  induction hw using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [mul_add, add_mul, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    have h := ExteriorAlgebra.ι_add_mul_swap (R := R) v u
    have h' : ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u = -(ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) :=
      eq_neg_of_add_eq_zero_left h
    rw [← mul_assoc, h', neg_mul, mul_assoc, hx, mul_smul_comm]
    simp only [pow_succ, mul_neg, mul_one, neg_smul, mul_assoc]

private theorem ext_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (p q : ℕ)
    (y w : ExteriorAlgebra R M) (hy : y ∈ ⋀[R]^p M) (hw : w ∈ ⋀[R]^q M) :
    y * w = ((-1 : ℤ) ^ (p * q)) • (w * y) := by
  induction hy using Submodule.pow_induction_on_left' with
  | algebraMap r => simp [Algebra.commutes]
  | add x y i _ _ hx hy => rw [add_mul, mul_add, hx, hy, smul_add]
  | mem_mul m hm i x _ hx =>
    obtain ⟨u, rfl⟩ := hm
    rw [mul_assoc, hx, mul_smul_comm, ← mul_assoc, ext_comm_one u q w hw, smul_mul_assoc, smul_smul,
      mul_assoc, Nat.succ_mul, pow_add]

theorem UpperTheory.Gal.productCup_of_system.idJ_of :
    LatOm → LatA → DualForm → IdJ := by
  intro hOm hA hD F K _ _ _ _ _ _ d x hc τ hτ a ha j
  obtain ⟨⟨_, n, v, φ, hv, hφ, hdec⟩, hsp⟩ := hOm F K d x hc a {j} (by simp)
  have hdec' : ∀ z ∈ Submodule.span F (omB ℂ K (rB ℂ K (xv x) {j}) a : Set (DR ℂ K)), z = ∑ k, φ k z • v k := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact hdec z hz
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [map_add (f := _), add_smul, Finset.sum_add_distrib]
      rw [← hp, ← hq]
    | smul c p _ hp =>
      simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum]
      rw [← hp]
  have hG : omG x j ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x j).ne_zero
  choose w hwm hwt using fun k => (hD F K d x hc τ hτ a ha (omG x j • φ k)).2
  have hwB : ∀ k, w k ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a) := by
    intro k
    refine (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) hc τ hτ {j} (by simp) a (d - a) (by omega) (w k) (hwm k)).1 ?_
    intro y hy
    have hy' : y ∈ ⋀[K]^a Ω[K⁄ℂ] := GlobalTheory.PD.mem_deg_of_mem_omB _ _ _ hy
    rw [ext_comm a (d - a) y (w k) hy' (hwm k), map_zsmul, map_zsmul]
    refine zsmul_mem ?_ _
    rw [← hwt k y hy']
    refine ((hA F d x hc.pd {j} j (by simp)).2.1 _).2 ?_
    simpa [hG] using hφ k y hy
  refine ⟨∑ k, w k ⊗ₜ[ℂ] v k, ?_, ?_⟩
  · show _ ∈ MZ F K (xv x) a {j} {j}
    exact Submodule.sum_mem _ fun k _ => Submodule.apply_mem_map₂ _ (hwB k) (hv k)
  · intro y hy
    conv_rhs => rw [hdec' y (hsp y hy)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : muP F K τ (w k ⊗ₜ[ℂ] v k) y = (Algebra.trace F K (τ (w k * y))) ⊗ₜ[ℂ] v k := by
      simp [muP]
    rw [this, ← hwt k y hy]
    simp [mulP]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PDualForm
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma perfectPairing_surjective {F Q P : Type*} [Field F] [AddCommGroup Q] [Module F Q] [AddCommGroup P] [Module F P]
    [FiniteDimensional F Q] [FiniteDimensional F P] (hr : Module.finrank F Q = Module.finrank F P)
    (B : Q →ₗ[F] P →ₗ[F] F) (hB : ∀ w, (∀ y, B w y = 0) → w = 0) :
    Function.Surjective B ∧ Function.Surjective B.flip := by
  have hinj : Function.Injective B :=
    (injective_iff_map_eq_zero B).2 fun w hw => hB w fun y => by simp [hw]
  have hs : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (P →ₗ[F] F) = Module.finrank F P from Subspace.dual_finrank_eq, hr])).1 hinj
  refine ⟨hs, ?_⟩
  have hinj' : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    refine (Module.forall_dual_apply_eq_zero_iff F y).1 fun f => ?_
    obtain ⟨w, rfl⟩ := hs f
    exact LinearMap.congr_fun hy w
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [show Module.finrank F (Q →ₗ[F] F) = Module.finrank F Q from Subspace.dual_finrank_eq, hr])).1 hinj'

theorem UpperTheory.Gal.productCup_of_system.dualForm_of :
    DualForm := by
  intro F K _ _ _ _ _ _ d x hc τ ht a ha ψ
  obtain ⟨hinj, hrk, hfdP⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht (d - a) a (by omega)
  obtain ⟨-, -, hfdQ⟩ := GlobalTheory.T.trace_wedge_pairing_perfect_rational_forms ℂ F K d (xv x) hc τ ht a (d - a) (by omega)
  haveI : FiniteDimensional F K := hc.fin
  haveI : FiniteDimensional F (⋀[K]^(d - a) Ω[K⁄ℂ]) := Module.Finite.trans K _
  haveI : FiniteDimensional F (⋀[K]^a Ω[K⁄ℂ]) := Module.Finite.trans K _
  let T : DR ℂ K →ₗ[F] F := (Algebra.trace F K) ∘ₗ (τ.restrictScalars F)
  let B : (⋀[K]^a Ω[K⁄ℂ]) →ₗ[F] (⋀[K]^(d - a) Ω[K⁄ℂ]) →ₗ[F] F :=
    LinearMap.mk₂ F (fun w y => T ((y : DR ℂ K) * (w : DR ℂ K)))
      (fun w w' y => by simp [mul_add])
      (fun c w y => by simp [mul_smul_comm])
      (fun w y y' => by simp [add_mul])
      (fun c w y => by simp [smul_mul_assoc])
  have hr : Module.finrank F (⋀[K]^a Ω[K⁄ℂ]) = Module.finrank F (⋀[K]^(d - a) Ω[K⁄ℂ]) := by
    rw [← Module.finrank_mul_finrank F K (⋀[K]^a Ω[K⁄ℂ]),
      ← Module.finrank_mul_finrank F K (⋀[K]^(d - a) Ω[K⁄ℂ]), hrk]
  obtain ⟨hs, hs'⟩ := perfectPairing_surjective hr B (fun w hw => Subtype.ext (hinj w.1 w.2 fun y hy => hw ⟨y, hy⟩))
  constructor
  · obtain ⟨w, hw⟩ := hs (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
  · obtain ⟨w, hw⟩ := hs' (ψ ∘ₗ (Submodule.subtype _).restrictScalars F)
    exact ⟨w.1, w.2, fun y hy => (LinearMap.congr_fun hw ⟨y, hy⟩).symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PrBOf
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

theorem UpperTheory.Gal.productCup_of_system.prB_of :
    GoodZ → PrB := by
  intro hG F K _ _ _ _ _ _ d x h τ hτ ρ hρ a q had hqd e he y hy
  have mono : ∀ r : ℕ, ∀ s t : Finset (Fin (d + 1)), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) r ≤ omB ℂ K (rB ℂ K (xv x) t) r :=
    fun r => (hG F K d x h r).2.2
  have hvan : ∀ i, (Finset.univ.erase i).Nonempty →
      ∀ u ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) (d - a),
      ∀ v ∈ omB ℂ K (rB ℂ K (xv x) (Finset.univ.erase i)) a,
      (LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ) u v = 0 := by
    intro i hi u hu v hv
    have hvq : v ∈ ⋀[K]^a Ω[K⁄ℂ] := ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties ℂ K _ a 0).2.1 v hv).2.2.1
    have hmem := (GlobalTheory.T.twistedDual_regularForms_finiteCover ℂ F K d (xv x) h τ hτ (Finset.univ.erase i) hi (d - a) a
      (by omega) v hvq).2 hv u hu
    exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) h.pd ρ hρ i _ hi (Finset.notMem_erase i _) _ hmem
  obtain ⟨ε, hε⟩ := GlobalTheory.T.cechDifferential_adjoint_cupProductPairing ℂ d _ _ (fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a))
    (fun I => omB ℂ K (rB ℂ K (xv x) I) a) ((LinearMap.mul ℂ (DR ℂ K)).compr₂ (trF ℂ τ ρ))
    (mono _) (mono _) hvan ((d : ℤ) - (q : ℕ))
  obtain ⟨y', hy', rfl⟩ := hy
  have key := hε e he.1 y' (by
    have e1 : (d : ℤ) - ((d : ℤ) - (q : ℕ)) - 1 = (q : ℤ) - 1 := by ring
    rw [e1]
    exact hy')
  have h0 : (cech fun I => omB ℂ K (rB ℂ K (xv x) I) (d - a)).D e = 0 := he.2
  rw [h0, map_zero, LinearMap.zero_apply] at key
  exact (smul_eq_zero_iff_eq ε).1 key.symm
end

