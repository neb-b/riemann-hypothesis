module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugation
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PkgConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

noncomputable def gaC (N : NumDatum) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ)
    (z : RPl N.R) (s : ZMod 2) : ℕ → ℕ :=
  gap (Dw.mult (tauC N pl z s)) fun i => a (tauC N pl z s, i)

theorem exists_rowFam (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => PhiC N l →
      Function.Bijective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) ∧
      ∃ R : RF.RowFam (parOf N j l) l 2, (∀ z, (R.X z).Alt) ∧
        (∀ z s, (R.X z).rkF 0 s = Dw.mult (tauC N pl z s)) ∧
        @RF.ValBlocksC R.C R.fC R.V (parOf N j l).Pl _ R.I R.J R.fI R.fJ R.X R.F nW (gaC N Dw pl a) ν := by
  intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 _ _ hM _ T io e hover y hy C3 nW ν hν hC
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hla, hunit, hconv⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (hVl ▸ (fun h => h2 (h ▸ N.H.two_mem_small) : resCharOf la ≠ 2)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  obtain ⟨hA, hS⟩ := GlobalTheory.LabSelf.arithS_tauC E H lv c N pl hP la T io C V ι hι hVl hla (hVl ▸ hC)
    (N.R.k - 1) j (N.R.m - j)
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hrk : (⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ : LabS E (RPl N.R)).RankOK Dw := by
    intro z
    have h10 : ¬ (1 : ZMod 2) = 0 := by decide
    have t0 : tauC N pl z 0 = pl z := if_pos rfl
    have t1 : tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := if_neg h10
    have m0 : Dw.mult (pl z) = Dw.p := if_pos (hpsi z)
    have m1 : Dw.mult (ComplexEmbedding.conjugate (pl z)) = Dw.q :=
      if_neg (GlobalTheory.LabSelf.not_inPsi_conj H (hpsi z))
    refine ⟨?_, ?_⟩
    · show Dw.mult (tauC N pl z 0) = N.R.k - 1 + j
      rw [t0, m0]; omega
    · show Dw.mult (tauC N pl z 1) = N.R.m - j
      rw [t1, m1, hq']
  obtain ⟨I, J, fI, fJ, X, F, hX, hval⟩ := _root_.GlobalTheory.RowAt.supplyC_selfConj hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy
    (RPl N.R) ⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ hA hS hrk (by show N.R.m - j < N.R.k - 1; omega) a hdom nW ν
    (hconv y C3 lv.M a nW ν hν)
  refine ⟨⟨hA.inj, hS⟩, { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F, hn := ?_ },
    fun z => (hX z).2.2.1, fun z => (hX z).2.2.2, hval⟩
  intro z
  refine ⟨(hX z).1, (hX z).2.1.trans ?_⟩
  show j + (N.R.m - j) = N.R.m
  omega

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (ga : ZMod 2 → ℕ → ℕ) :
    ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) =
      ∑ s : ZMod 2, ((∑ k ∈ Finset.Icc 1 K, k * ga s k : ℕ) : ℝ) - (n : ℝ) * ga 0 n := by
  have e : (n : ℝ) * ga 0 n =
      ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, if s = 0 ∧ k = n then (k : ℝ) * ga s k else 0 := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem packages_conj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC T0 θ0 C1 hdeg hrows
    obtain ⟨hbij, R, halt, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hmain : ∀ z, gaC N Dw pl a z 0 (N.R.k - 1) = gapW N pl a z := by
      intro z
      have t0 : tauC N pl z 0 = pl z := if_pos rfl
      have hm : Dw.mult (pl z) = Dw.p := if_pos (hpsi _)
      unfold gaC
      rw [t0, hm]
      unfold gap gapW
      rw [if_pos (by omega), if_pos (by omega)]
      rfl
    have hDF : DF Dw a = ∑ z, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r, k * gaC N Dw pl a z s k := by
      unfold DF
      rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2.symm
    refine ⟨{ R := R, alt := halt, gaC := gaC N Dw pl a, W := gapW N pl a, nW := nW, T := T0, θ0 := θ0,
              rest := restOf N Dw pl a, ν := ν, supp := ?_, main := hmain, rest_eq := ?_, what₂ := hrows,
              deg := hdeg, val := hval }, rfl, rfl⟩
    · intro z s k hk
      rw [hrk]
      exact (hgs _).1 k hk
    · show restOf N Dw pl a = ∑ z : RPl N.R, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r,
        (if s = 0 ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * gaC N Dw pl a z s k)
      simp only [rest_add (N.R.k - 1) N.R.r (by omega) (by omega), hmain]
      unfold restOf
      rw [hDF, Finset.sum_sub_distrib, ← Finset.mul_sum]
      push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
      rfl
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC hw s hfirst hrows
    obtain ⟨-, R, -, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hcard : Fintype.card (RPl N.R) = N.R.f := by
      simp [RPl, Ranks.f, Ranks.n, ZMod.card, N.R.card_A]
    refine ⟨{ R := R, gaC := gaC N Dw pl a, K := N.R.r, s := s, nW := nW, T := 1, ν := ν, T_one := le_rfl,
              w_nonneg := hw, supp := ?_, first := ?_, what₂ := ?_, val := hval }, rfl⟩
    · intro z σ k hk
      rw [hrk]
      have h := (hgs _).1 k hk
      exact ⟨h.1, h.2, h.2.trans (hmul _)⟩
    · intro z σ
      rcases Nat.eq_zero_or_pos (Dw.mult (tauC N pl z σ)) with h0 | h0
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun k _ => ?_)) (Nat.zero_le _)
        by_contra hk
        have h := (hgs _).1 k hk
        omega
      · exact le_trans (le_of_eq (((hgs _).2 _ (hmul _)).1 0 h0)) (hfirst _ h0)
    · show 4 * N.R.r * s * Fintype.card (RPl N.R) ≤ nW
      rw [hcard]; exact hrows

end GlobalTheory.PkgConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProof
section
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SplitPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  have hd : 0 < H.d := H.d_prime.pos
  have e2 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
    have h1 : τ (H.rt : E) = H.rt0 := h
    have h2 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rw [h2, h1]
  have e3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) H.rt_sq
    simpa using this
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast hd
  nlinarith [sq_nonneg r]

theorem pkgSplit : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd' hM _ T io e hov y hy C3 nW ν hν
    hsp Tr θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hMM, hunit, hnu⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hov
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (by rw [hVl]; intro h; exact h2 (h ▸ N.H.two_mem_small)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E :=
    hpl.unr V.l V.l_prime (by rw [hVl]; exact h2) (by rw [hVl]; exact hq') (by rw [hVl]; exact hd')
  obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hpl la T io C V ι hι hVl hMM
    (by rw [hVl]; exact hsp) j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq'' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d :=
    { tau := fun o => tauSp N pl pos o.1, n := N.R.k - 1, j := j, j' := N.R.m - j, big := fun _ g _ => g = 0 }
  have hsep := (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => by simp [lab, tauSp]
      frob := fun o g s x => hfr o.1 g s x
      sep := fun x x' hx => hsep _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr d _ (hfr o.1 g) }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · change (1 - g = 0) ↔ ¬ g = 0
      revert g; decide
    · change g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.k - 1 + j
      rw [tauSp, if_pos hg]
      have : Dw.mult (pl (pos o.1 s.val)) = Dw.p := if_pos (hpsi _)
      omega
    · change ¬ g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.m - j
      rw [tauSp, if_neg hg]
      have : Dw.mult (ComplexEmbedding.conjugate (pl (pos o.1 s.val))) = Dw.q :=
        if_neg (not_inPsi_conjugate H (hpsi _))
      omega
  have hsup := _root_.GlobalTheory.RowAt.supply_pairs hU E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z d lab harith hbij.2 hrank
    (by change N.R.m - j < N.R.k - 1; omega) (fun o => Or.inr fun _ => rfl) a hdom nW ν (hnu y C3 lv.M a nW ν hν)
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hval⟩ := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g _ => g = 0) (fun z g s => Dw.mult (tauSp N pl pos z g s))
    (fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)) nW ν hne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom d pos Z (fun _ => 0) (tauSp N pl pos) hZ hbij
    (fun z s => by simp [tauSp])
  refine ⟨d, inferInstance, pos,
    { R := { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F,
             hn := fun z => ⟨(hn z).1, (hn z).2.trans (by change j + (N.R.m - j) = N.R.m; omega)⟩ }
      Z := Z
      hZ := hZ
      allBig := fun z hz s => ((hbig z hz 0 s).1).2 rfl
      ga := fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)
      W := gapW N pl a
      nW := nW
      T := Tr
      θ0 := θ0
      rest := restOf N Dw pl a
      ν := ν
      wt := ⟨fun z hz g s k hk => ?_, hwt.main, hwt.rest_eq⟩
      what₂ := hrows
      deg := ⟨hdeg.T_one, hdeg.w_pos, hdeg.TW_lo, hdeg.TW_hi, hdeg.th_rng, hdeg.th_m, hdeg.rest_nonneg, hdeg.rest_le⟩
      val := hval }, rfl, rfl⟩
  have h1 := hwt.supp z hz g s k hk
  exact ⟨h1.1, h1.2.trans (hbig z hz g s).2.ge⟩

end GlobalTheory.SplitPackage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaStableOfAlgHom
section
open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct

namespace GlobalTheory.FormTies

theorem theta_stable_of_algHom {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (Ψ : X.Forms →ₐ[B.KO] X.Forms) (Sc : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (hL : ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Ψ (X.inc wL F) = X.inc wL F')
    (hS : ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Ψ (X.inc w F) = X.inc w F') :
    ∀ x ∈ X.Theta Sc ka wL wF T, Ψ x ∈ X.Theta Sc ka wL wF T := by
  let Φ : X.Forms →ₐ[𝓞 B.KO] X.Forms := Ψ.restrictScalars _
  suffices key : (X.Theta Sc ka wL wF T).map Φ.toLinearMap ≤ X.Theta Sc ka wL wF T from
    fun x hx => key ⟨x, hx, rfl⟩
  change ∀ F ∈ X.thAll wL, ∃ F' ∈ X.thAll wL, Φ (X.inc wL F) = X.inc wL F' at hL
  change ∀ w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) → ∀ F ∈ X.shortTh w, ∃ F' ∈ X.shortTh w, Φ (X.inc w F) = X.inc w F' at hS
  have hsm : ∀ (s : 𝓞 B.KO) w (F : B.Cusp j w), X.inc w (s • F) = s • X.inc w F := fun s w F =>
    ((X.inc w).restrictScalars (𝓞 B.KO)).map_smul s F
  have hsc : ∀ (s : 𝓞 B.KO) w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') →
      ∀ F ∈ X.scaled s w N, ∃ F' ∈ X.scaled s w N, Φ (X.inc w F) = X.inc w F' := by
    rintro s w N hN _ ⟨F, hF, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    refine ⟨_, ⟨F', hF', rfl⟩, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, hsm, map_smul, e]
  have hemb : ∀ w (N : Submodule (𝓞 B.KO) (B.Cusp j w)),
      (∀ F ∈ N, ∃ F' ∈ N, Φ (X.inc w F) = X.inc w F') → (X.emb w N).map Φ.toLinearMap ≤ X.emb w N := by
    rintro w N hN _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    obtain ⟨F', hF', e⟩ := hN F hF
    exact ⟨F', hF', e.symm⟩
  have h1 : (X.emb wL (X.WWc Sc.sW wL)).map Φ.toLinearMap ≤ X.emb wL (X.WWc Sc.sW wL) :=
    hemb _ _ (hsc _ _ _ hL)
  have h2 : ∀ s w, (w = wF ∨ w = X.wF0 wL wF ∨ w = ka) →
      (X.emb w (X.Thc s w)).map Φ.toLinearMap ≤ X.emb w (X.Thc s w) := fun s w hw =>
    hemb _ _ (hsc _ _ _ (hsc _ _ _ (hS w hw)))
  unfold WeightAlgebra.PJ.Theta
  rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_mul, Submodule.map_mul, Submodule.map_pow, Submodule.map_pow]
  refine sup_le_sup (sup_le_sup (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inl rfl)))
    (mul_le_mul' (pow_le_pow_left' h1 _) (h2 _ _ (Or.inr (Or.inl rfl))))) (h2 _ _ (Or.inr (Or.inr rfl)))

theorem map_mem_spanIn {D : D7} {K : Type} [Field K] [NumberField K] {R : ℕ → Type} [∀ j, CommRing (R j)]
    [∀ j, Algebra K (R j)] [∀ j, Algebra (𝓞 K) (R j)] [∀ j, IsScalarTower (𝓞 K) K (R j)]
    (C : ∀ j, WeightFamilies.Wt D j → Submodule K (R j)) (j : ℕ) (w : WeightFamilies.Wt D j) (s : Set (R j)) (ψ : R j →ₗ[K] R j)
    (hs : ∀ f ∈ s, ∃ (u : 𝓞 K) (f' : R j), f' ∈ s ∧ ψ f = (u : K) • f') (F F' : cutR C j w) (e : F'.1 = ψ F.1) (hF : F ∈ spanIn C j w s) :
    F' ∈ spanIn C j w s := by
  change F'.1 ∈ Submodule.span (𝓞 K) s
  rw [e]
  have hle : (Submodule.span (𝓞 K) s).map (ψ.restrictScalars (𝓞 K)) ≤ Submodule.span (𝓞 K) s := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨u, f', hf', e'⟩ := hs f hf
    have e'' : ψ f = u • f' := e'.trans (algebraMap_smul K u f')
    change ψ f ∈ Submodule.span (𝓞 K) s
    rw [e'']
    exact Submodule.smul_mem _ u (Submodule.subset_span hf')
  exact hle ⟨F.1, hF, rfl⟩

theorem coe_one_smul_eq {K : Type} [Field K] {R : ℕ → Type} [∀ j, CommRing (R j)] [∀ j, Algebra K (R j)] (j : ℕ)
    (x : R j) : x = ((1 : 𝓞 K) : K) • x := by
  simp

noncomputable def actLevAlg {D : D7} (T : Top D) (j : ℕ)
    (γ : LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l) : T.R j →ₐ[T.Q.c.F] T.R j :=
  AlgHom.ofLinearMap (actLev (Xo := T.Q.Xo j) T.Q.c (levFull (T.Q.Dw j) T.Q.l) γ) rfl (fun _ _ => rfl)

theorem levAct_theta : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Full D) (h : LawsP T.toTop) (j : ℕ) (hj : InR D j), LawsFull T → (∀ γ₀ ∈ Formalism.L2.Theta.GQ (T.V j T.σ₀), T.xi (Matrix.GeneralLinearGroup.det (Formalism.L2.Theta.finHom (T.V j T.σ₀) γ₀)) = 1) → ∀ (Sc : WeightAlgebra.Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn : ℕ), WeightAlgebra.IsF' ka wL wF Tn wF.n → ka.n = wF.n + Tn * wL.n → WeightFamilies.dimY D j ≤ Tn → D.R.r ≤ wF.n → ∀ (P : Type) (ℓ : P → (LaMod (T.Q.Dw j) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw j) T.Q.l)) (act : P → (recB h.toLawsCore).Cusp j ka → (recB h.toLawsCore).Cusp j ka), IsLevAct T.toTop h j ka ℓ act → ∀ g F, (recPJ h j hj).inc ka F ∈ (recPJ h j hj).Theta Sc ka wL wF Tn → (recPJ h j hj).inc ka (act g F) ∈ (recPJ h j hj).Theta Sc ka wL wF Tn := by
  intro hC D T h j hj hfull hxi Sc ka wL wF Tn _ hn _ hr P ℓ act hact g F hF
  let ψ := actLevAlg T.toTop j (ℓ g)
  let Φ0 : AddMonoidAlgebra (T.R j) (Deg D j) →ₐ[T.Q.c.F] AddMonoidAlgebra (T.R j) (Deg D j) :=
    AddMonoidAlgebra.mapAlgHom (Deg D j) ψ
  let Φ : @AlgHom _ _ _ _ _ _ (recPJ h j hj).aF (recPJ h j hj).aF := Φ0
  have hΦ : ∀ w (F F' : (recB h.toLawsCore).Cusp j w), F'.1 = ψ F.1 →
      Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w F F' e
    change Φ0 (AddMonoidAlgebra.single (deg w) F.1) = AddMonoidAlgebra.single (deg w) F'.1
    rw [e]
    exact AddMonoidAlgebra.mapAlgHom_single _ _ _
  have hspan : ∀ w (s : Set (T.R j)), (∀ f ∈ s, ∃ (u : 𝓞 T.Q.c.F) (f' : T.R j), f' ∈ s ∧ ψ f = (u : T.Q.c.F) • f') →
      ∀ F ∈ spanIn T.C j w s,
      ∃ F' ∈ spanIn T.C j w s, Φ ((recPJ h j hj).inc w F) = (recPJ h j hj).inc w F' := by
    intro w s hs F hF
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.FormTies.exists_isLevAct D T.toTop h j hj w P ℓ
    exact ⟨a g F, map_mem_spanIn T.C j w s ψ.toLinearMap hs F _ (ha g F) hF, hΦ w F _ (ha g F)⟩
  have hone : ∀ x : T.R j, x = ((1 : 𝓞 T.Q.c.F) : T.Q.c.F) • x := fun x => coe_one_smul_eq (R := T.R) j x
  have key := theta_stable_of_algHom (recPJ h j hj) Φ Sc ka wL wF Tn
    (hspan wL (T.th j wL) fun f hf => by
      obtain ⟨_, hnab⟩ := h.nabPin j hj
      exact ⟨1, ψ f, GlobalTheory.T.levelAction_mem_thetaSeries hC D T.toTop h j hj wL (ℓ g) f hf
        (GlobalTheory.thetaRule_mem_sec GlobalTheory.abelianSchemeLaws_all.1 hC _ _ _ _ _ _ _ hnab _ _ f hf), hone _⟩)
    (fun w hw => hspan w (T.toTop.sh j w) fun f hf => GlobalTheory.T.levelAction_shortThetaSeries_rootOfUnity_mul hC D T hfull j hj hxi w (by
      rcases hw with rfl | rfl | rfl
      · exact hr
      · exact hr.trans (Nat.le_add_right _ _)
      · rw [hn]; exact hr.trans (Nat.le_add_right _ _)) (ℓ g) f hf)
  rw [← hΦ ka F (act g F) (hact g F)]
  exact key _ hF

end GlobalTheory.FormTies
end

