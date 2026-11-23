module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0030
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0027
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0022
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0029
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0021
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0024
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0028
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpMazur

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AnnOfFlat
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ann_of_flat {A R : Type} [CommRing A] [CommRing R] [IsLocalRing R] (f : A →+* R) (hf : f.Flat)
    {a : A} (ha : f a = 0) : ∃ s, s ∉ (maximalIdeal R).comap f ∧ s * a = 0 := by
  algebraize [f]
  have h0 : ∑ i : Fin 1, (fun _ : Fin 1 => a) i • (fun _ : Fin 1 => (1 : R)) i = 0 := by
    rw [Fin.sum_univ_one, Algebra.smul_def, mul_one]
    exact ha
  obtain ⟨k, c, y, hy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := A) (M := R) (f := fun _ : Fin 1 => a) (x := fun _ : Fin 1 => (1 : R)) h0
  by_contra hne
  push_neg at hne
  have h1 : (1 : R) = ∑ j, c 0 j • y j := hy 0
  have hone : (1 : R) ∈ maximalIdeal R := by
    rw [h1]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    by_contra h'
    refine hne (c 0 j) h' ?_
    have h2 : a * c 0 j = 0 := by
      have := hc j
      rwa [Fin.sum_univ_one] at this
    rwa [mul_comm] at h2
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hone)

private theorem ann_ideal {A : Type} [CommRing A] (x : Ideal A) [hx : x.IsPrime] (I : Ideal A) (hI : I.FG)
    (h : ∀ a ∈ I, ∃ s, s ∉ x ∧ s * a = 0) : ∃ s, s ∉ x ∧ ∀ a ∈ I, s * a = 0 := by
  classical
  obtain ⟨t, rfl⟩ := hI
  choose! s hs hsa using fun g (hg : g ∈ t) => h g (Ideal.subset_span hg)
  refine ⟨∏ g ∈ t, s g, ?_, fun a ha => ?_⟩
  · intro hmem
    obtain ⟨g, hg, hgx⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    exact hs g hg hgx
  · induction ha using Submodule.span_induction with
    | mem g hg => rw [← Finset.prod_erase_mul _ _ hg, mul_assoc, hsa g hg, mul_zero]
    | zero => simp
    | add u v _ _ hu hv => rw [mul_add, hu, hv, add_zero]
    | smul r u _ hu => rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

theorem UpperTheory.V.Fr.gpos :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ∀ E : L.EPres, E.g ≠ 0 := by
  intro l _ O _ _ _ _ F C₀ hF S x L hx E hg
  obtain ⟨hfl, hmax, hB⟩ := UpperTheory.V.Fr.loc_flat hF (Or.inr rfl) S x L
  have hA : IsNoetherianRing S.A := (UpperTheory.V.Fr.gr_A hF (Or.inr rfl) S).2.2.2.2.2.1
  have h0 : L.ρ.ee ≤ ⊥ := by
    rw [E.ee, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have := i.2
    omega
  have h1 : S.u.ee ≤ L.im ⊥ := ((UpperTheory.V.Fr.loc_rho hF (Or.inr rfl) S x L).2.2.1 ⊥).2.2.1 h0
  haveI := hmax.isPrime
  obtain ⟨s, hs, hs0⟩ := ann_ideal x S.u.ee (IsNoetherian.noetherian _) fun a ha => by
    have := ann_of_flat (L.ι : S.A →+* L.R) hfl (a := a) (h1 ha)
    rwa [L.lies] at this
  have hxB : (⟨x, hmax.isPrime⟩ : PrimeSpectrum S.A) ∈ S.BB := ⟨hB, hx⟩
  have hcl := (UpperTheory.V.Fr.preconnected_rank_three hF S).2.2 hxB
  obtain ⟨p, hp1, -, hp2⟩ := mem_closure_iff.1 hcl (PrimeSpectrum.basicOpen s)
    (PrimeSpectrum.basicOpen s).isOpen hs
  refine hp2 fun a ha => ?_
  have h2 : s * a ∈ p.asIdeal := by
    rw [hs0 a ha]
    exact zero_mem _
  exact (p.isPrime.mem_or_mem h2).resolve_left hp1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibDim
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem dim_le_of_primes {R : Type} [CommRing R] (I : Ideal R) (d : WithBot ℕ∞)
    (h : ∀ P : Ideal R, P.IsPrime → I ≤ P → ringKrullDim (R ⧸ P) ≤ d) : ringKrullDim (R ⧸ I) ≤ d := by
  rw [ringKrullDim_quotient]
  unfold Order.krullDim
  refine iSup_le fun s => ?_
  let q : PrimeSpectrum R := (s.head).1
  have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp s.head.2
  have hP := h q.asIdeal q.isPrime hIq
  rw [ringKrullDim_quotient] at hP
  have hmem : ∀ i, (s i).1 ∈ PrimeSpectrum.zeroLocus (R := R) q.asIdeal := by
    intro i
    have hle : s.head ≤ s i := s.monotone (Fin.zero_le i)
    exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hle
  let s' : LTSeries (PrimeSpectrum.zeroLocus (R := R) q.asIdeal) :=
    { length := s.length
      toFun := fun i => ⟨(s i).1, hmem i⟩
      step := fun i => s.step i }
  exact le_trans (Order.LTSeries.length_le_krullDim s') hP

private theorem trdeg_le_of_dim {B A : Type} [CommRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A]
    (η : Ideal A) [η.IsPrime] (hm : (η.comap (algebraMap B A)).IsMaximal) (t : ℕ)
    (h : ringKrullDim (A ⧸ η) ≤ t) : Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) ≤ t := by
  haveI := hm
  letI : Field (B ⧸ η.comap (algebraMap B A)) := Ideal.Quotient.field _
  haveI : IsDomain (A ⧸ η) := Ideal.Quotient.isDomain η
  haveI : Algebra.FiniteType B (A ⧸ η) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ B η) (Ideal.Quotient.mkₐ_surjective B η)
  haveI : Algebra.FiniteType (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) :=
    Algebra.FiniteType.of_restrictScalars_finiteType B _ _
  obtain ⟨d, hd1, hd2⟩ :=
    GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq (B ⧸ η.comap (algebraMap B A)) (A ⧸ η)
  rw [hd2]
  rw [hd1] at h
  have hdt : d ≤ t := by exact_mod_cast h
  exact_mod_cast hdt

private theorem exists_field_injective_ringHom_of_isDomain (D : Type) [CommRing D] [IsDomain D] :
    ∃ (K : Type) (_ : Field K) (j : D →+* K), Function.Injective j := by
  set_option synthInstance.maxHeartbeats 400000 in
  exact ⟨FractionRing D, inferInstance, algebraMap D _, IsFractionRing.injective D (FractionRing D)⟩

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Fr.fib_dim :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ¬ S.u.triP ≤ x → ringKrullDim (L.R ⧸ S.mB.map L.b) ≤ (2 * C₀ : ℕ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L hx
  obtain ⟨hCO, hmB⟩ := co_B hF hn S
  haveI := hCO
  obtain ⟨-, -, -, -, hft, -, -⟩ := gr_A hF hn S
  haveI := hft
  have hl42 := finrank_frameSpace_eq hF hn S
  apply dim_le_of_primes
  intro P hP hbP
  have hπ : S.mB ≤ L.π P := by
    show S.mB ≤ Ideal.comap (S.inc : S.B →+* S.A) (Ideal.comap (L.ι : S.A →+* L.R) P)
    rw [Ideal.comap_comap]
    exact Ideal.map_le_iff_le_comap.mp hbP
  haveI hηp : (L.im P).IsPrime := Ideal.comap_isPrime _ P
  have hπprime : (L.π P).IsPrime := by
    show (Ideal.comap (S.inc : S.B →+* S.A) (L.im P)).IsPrime
    exact Ideal.comap_isPrime _ _
  have hmBmax : S.mB.IsMaximal := by
    rw [← hmB]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hπeq : S.mB = L.π P := hmBmax.eq_of_le hπprime.ne_top hπ
  have hπmax : (L.π P).IsMaximal := hπeq ▸ hmBmax
  have hx0 : S.x0 ≤ L.im P := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr hπ
  have hηx : L.im P ≤ x := by
    have h1 : Ideal.comap (L.ι : S.A →+* L.R) P ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) :=
      Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP.ne_top)
    exact h1.trans L.lies.le
  haveI : IsDomain (S.A ⧸ L.im P) := Ideal.Quotient.isDomain _
  obtain ⟨K, hK, j, hj⟩ := exists_field_injective_ringHom_of_isDomain (S.A ⧸ L.im P)
  have hker : RingHom.ker (j.comp (Ideal.Quotient.mk (L.im P))) = L.im P := by
    rw [RingHom.ker_comp_of_injective _ hj, Ideal.mk_ker]
  have htypes := (types hF hn S K (j.comp (Ideal.Quotient.mk (L.im P)))).2
  rw [hker] at htypes
  have hM : S.u.triM ≤ L.im P := by
    rcases htypes hπ with h | h
    · exact absurd (le_trans h hηx) hx
    · exact h
  have hdimA : ringKrullDim (S.A ⧸ L.im P) ≤ ((2 * C₀ : ℕ) : WithBot ℕ∞) := by
    have hle : S.x0 ⊔ S.u.triM ≤ L.im P := sup_le hx0 hM
    exact le_trans (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle)) hl42
  have htd : S.td (L.im P) ≤ ((2 * C₀ : ℕ) : Cardinal) := by
    unfold Space.td
    exact trdeg_le_of_dim (L.im P) hπmax (2 * C₀) hdimA
  have hd := (loc_dim hF hn S x L).1 P hP (2 * C₀) htd
  have hB0 : ringKrullDim (S.B ⧸ L.π P) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hπmax)
  rw [hB0, zero_add] at hd
  exact hd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.HasObs
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), L.Pres := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  haveI : CharP (ResidueField O) l := IsCoef.char
  haveI : IsNoetherianRing L.O' := inferInstance
  haveI : IsAdicComplete (maximalIdeal L.O') L.O' := IsCoef.complete
  haveI : Finite (ResidueField L.O') := IsCoef.fin
  haveI : CharP (ResidueField L.O') l := IsCoef.char
  have hU : NRep.Univ L.O' L.ρ := by
    refine ⟨(loc_rho hF hn S x L).1, ?_⟩
    intro C _ _ _ ρ' hc hb
    exact def_iso hF hn S x L C ρ' hc hb
  obtain ⟨B, hBo, hBc⟩ := pr_box hF L.R (maximalIdeal L.R) L.ρ (loc_rho hF hn S x L).1 (fun v => flag hF hn S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨φ, hφ⟩ := (pr_res hF hn S x L).1
  have hG := pr_good hF hn (ResidueField L.O') φ _ hφ
  haveI : Module.Finite (ResidueField L.O') (Tan L.O' L.R) := (pr_tan L.O' L.R).1
  have hBo' := hBo.map (res L.O' L.R : L.R →+* ResidueField L.O')
  have hres := pr_res hF hn S x L
  have hcount := pr_count (K := ResidueField L.O') F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b
    ((Box.tanCo L.O' B).comp (Tan L.O' L.R).subtype)
    (fun v Y hY => pr_brig (ResidueField L.O') _ (Box.bar L.O' B) hBo' hG.1 v Y hY)
    (fun z hz => by
      obtain ⟨D, hD, X, hX⟩ := pr_tsurj hF L.O' L.R L.ρ B hU hBo hBc hG.1 z hz
      exact ⟨⟨D, hD⟩, X, hX⟩)
  obtain ⟨D₀, hD₀, hD₀s⟩ := pr_tor hF L.O' L.R L.ρ B hU hBo hBc hG.1 hG.2.2
  have h1 := hcount.2 _ ⟨D₀, hD₀⟩ hG.2.1 hD₀s
  have hec := hF.ec (ResidueField L.O') (Matrix (Fin n) (Fin n) (ResidueField L.O')) (Box.bar L.O' B).ad (Box.bar L.O' B).b
    (pr_open hF L.O' L.R B hBc).2.1
    (fun v s X hX => pr_bstab _ (Box.bar L.O' B) v s X hX)
    (fun f hf => pr_dual hF hn (ResidueField L.O') φ _ (Box.bar L.O' B) hBo' hφ hres.2 f hf)
  have h2K : (2 : ResidueField L.O') ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff (ResidueField L.O') l 2).1 (by exact_mod_cast h)
    have hl := (Fact.out : l.Prime)
    have h4 := Nat.le_of_dvd (by norm_num) hd
    have h5 := hl.two_le
    have h6 := hF.l_odd
    omega
  have hκ : ∀ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = (n * n - n) / 2 := by
    intro w
    have hsq : (Box.bar L.O' B).r (F.cw w) * (Box.bar L.O' B).r (F.cw w) = 1 := by
      rw [← map_mul, hF.cw_sq w, map_one]
    have hr : ((Box.bar L.O' B).r (F.cw w)).right = -1 := by
      rw [(Box.bar L.O' B).nu, hF.del_cw w]
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker + n = n * n :=
      pr_cfix (ResidueField L.O') n _ h2K hsq hr
    have hle : n ≤ n * n := Nat.le_mul_self n
    omega
  have hβ : ∀ v : F.V, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = (n * n - n) / 2 + n := by
    intro v
    have key : 2 * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = n * (n + 1) :=
      pr_bdim (ResidueField L.O') n ((Box.bar L.O' B).g v)
    have hle : n ≤ n * n := Nat.le_mul_self n
    have e : n * (n + 1) = n * n + n := by ring
    omega
  have hsum1 : ∑ v : F.V, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).b v) = F.d * ((n * n - n) / 2) + F.d * n := by
    rw [Finset.sum_congr rfl (fun v _ => by rw [hβ v]), ← Finset.sum_mul]
    show F.d * ((n * n - n) / 2 + n) = _
    ring
  have hsum2 : ∑ w : F.Inf, Module.finrank (ResidueField L.O') ((Box.bar L.O' B).ad (F.cw w) - 1).ker = F.d * ((n * n - n) / 2) := by
    simp only [hκ, Finset.sum_const, Finset.card_univ, smul_eq_mul, hF.card_inf]
  have hT : Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) + n * F.d + 1 ≤ Module.finrank (ResidueField L.O') (Tan L.O' L.R) := by
    have e := hec.2
    rw [hsum1, hsum2] at e
    have : n * F.d = F.d * n := Nat.mul_comm _ _
    omega
  have hobs : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := by
    intro C' _ _ _ p hp hm
    obtain ⟨D⟩ := pr_setlift hF L.O' C' L.R p B hp hm hBc
    have hZ : ∀ u, D.co u ∈ continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b := by
      intro u
      obtain ⟨_, _, hlc1, hlc2⟩ := pr_omk hF L.O' C' L.R p B D hm
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hlc1.comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro v
        exact (hlc2 v).comp (fun M => M.map (evK (RingHom.ker p) u))
      · intro s t r
        exact borelProjection_isTwoCocycle hF L.O' C' L.R p B D u hm s t r
      · intro v s t
        exact pr_cocv hF L.O' C' L.R p B D u hm v s t
    refine ⟨(Submodule.mkQ _).comp (LinearMap.codRestrict _ D.co hZ), ?_⟩
    intro u hu C'' _ _ _ q p'' hc hq hk
    refine pr_obs hF L.O' L.R L.ρ B hU hBo hBc hG.1 C' p D u hm ?_ C'' q p'' hc hq hk
    have h' : (⟨D.co u, hZ u⟩ : continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) ∈
        Submodule.comap (continuousCocycles2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b).subtype (continuousCoboundaries2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) :=
      (Submodule.Quotient.mk_eq_zero _).1 hu
    exact h'
  haveI : Module.Finite (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b) := hec.1
  have hobs' : HasObs L.O' L.R (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b ×
      (Fin (Module.finrank (ResidueField L.O') (Tan L.O' L.R) - (n * F.d + 1) -
        Module.finrank (ResidueField L.O') (coneH2 F.loc (Box.bar L.O' B).ad (Box.bar L.O' B).b)) → ResidueField L.O')) := by
    intro C' _ _ _ p hp hm
    obtain ⟨ob, hob⟩ := hobs C' p hp hm
    refine ⟨(LinearMap.inl _ _ _).comp ob, fun u hu => hob u ?_⟩
    simpa using hu
  obtain ⟨p, f, hs, hk⟩ := pr_mazur L.O' L.R _ hobs'
  refine ⟨_, _, p, f, ?_, hs, hk⟩
  rw [Module.finrank_prod, Module.finrank_fin_fun]
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Seedpt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.seedpt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ ∀ L : S.Loc x.asIdeal, ∃ P : Ideal L.R, P.IsPrime ∧ L.ρ.TI P ∧ L.π P = p ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ p) + 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ
  obtain ⟨η, hηp, hhom, hπ, hTIη, htd⟩ := frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ
  have hTIη' := hTIη
  unfold NRep.TI NRep.OffTri at hTIη'
  obtain ⟨x, hxmax, hxBB, hηx⟩ := l41 hF hn S η hηp hhom hTIη'.1.1
  refine ⟨x, hxmax, hxBB, fun L => ?_⟩
  have htd' : S.td η = ((1 : ℕ) : _) := by
    rw [htd]
    rfl
  obtain ⟨P, hP, himP, hdim⟩ := (loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'
  have hloc := (loc_rho hF hn S x.asIdeal L).2.2.1 P
  rw [himP] at hloc
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · unfold NRep.TI NRep.OffTri
    exact ⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩,
      fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩
  · show S.π (L.im P) = p
    rw [himP, hπ]
  · rw [hdim, hπ]
    norm_num
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SumLe
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem sum_ge {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (F : Frame l k) (m : ℕ) (e : F.V → ℕ)
    (h : ∀ v, m ≤ e v) : m * F.d ≤ ∑ v, F.dv v * e v := by
  unfold Frame.d
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [mul_comm]
  exact Nat.mul_le_mul_left _ (h v)

private theorem sum_le {I : Type} [Fintype I] (m : ℕ) (e : I → ℕ) (h : ∀ v, e v ≤ m) :
    ∑ v, e v ≤ m * Fintype.card I := by
  have := Finset.sum_le_card_nsmul Finset.univ e m (fun v _ => h v)
  simpa [mul_comm] using this

theorem UpperTheory.V.Fr.epres :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → Nonempty L.EPres := by
  intro l _ O _ _ _ _ F C₀ hok S x L hx
  obtain ⟨σ, hσ⟩ := ep_inv hok S x L hx
  have hbarL := pr_res hok (Or.inr rfl) S x L
  obtain ⟨φ, hφ⟩ := hbarL.1
  have hgood := pr_good hok (Or.inr rfl) (ResidueField L.O') φ _ hφ
  have h2K : (2 : ResidueField L.O') ≠ 0 := hgood.1.two
  have h2 : IsUnit (2 : L.O') := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    rw [map_ofNat]
    exact h2K
  have hloc := loc_rho hok (Or.inr rfl) S x L
  have hU : NRep.Univ L.O' L.ρ := ⟨hloc.1, fun C _ _ _ ρ' hc hb => def_iso hok (Or.inr rfl) S x L C ρ' hc hb⟩
  obtain ⟨B₀, hB₀, hB₀c⟩ := pr_box hok L.R (maximalIdeal L.R) L.ρ hloc.1
    (fun v => flag hok (Or.inr rfl) S L.R (L.ι : S.A →+* L.R) v)
  obtain ⟨B, π, hBo, hBr, hG⟩ := ep_gbox L.O' h2 hok.del_c L.R σ hσ.sq L.ρ B₀ hB₀ hgood.1 hσ.ent
    (fun v i s => hσ.base (S.ψB v i s))
  have hBc : Box.Cont (maximalIdeal L.R) B := by
    unfold Box.Cont
    rw [hBr]
    exact hB₀c
  have hEv := ep_ev L.O' h2 L.R σ B π hG
  have htan := ep_tan hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv hgood.2.1 hgood.2.2
  obtain ⟨a, g, p, hsurj, hvar, hpart, hhom, hmin⟩ := ep_vars L.O' h2 L.R σ hσ.sq
  obtain ⟨κ, _, f, wf, hf, hker, hind⟩ := ep_rels L.O' h2 (Fin a ⊕ Fin g) (Space.Loc.par a g) (RingHom.ker p) hhom
  let P : GPres L.O' σ := ⟨a, g, p, κ, f, wf, hsurj, hvar, hpart, hhom, hmin, hf, hker, hind⟩
  have hee : L.ρ.ee = Ideal.span (Set.range fun i => P.p (MvPowerSeries.X (Sum.inr i))) := by
    rw [ep_ee hok S x L hx σ hσ, ep_odd L.O' L.R σ P]
  have hBbOf : (Box.bar L.O' B).Of (NRep.bar L.O' L.ρ) := hBo.map _
  have hdual := pr_dual hok (Or.inr rfl) (ResidueField L.O') φ (NRep.bar L.O' L.ρ) (Box.bar L.O' B) hBbOf hφ hbarL.2
  have hprp := ep_prp h2K (Box.bar L.O' B) π hEv
  have hopen := (pr_open hok L.O' L.R B hBc).2.1
  have hopenj : ∀ j, IsOpen ((hEv.ad j).ker : Set F.Γ) := by
    intro j
    apply Subgroup.isOpen_mono _ hopen
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    apply LinearMap.ext
    intro X
    apply Subtype.ext
    simp [Box.Ev.ad_apply, hs]
  have hstab : ∀ j (v : F.V) (s : F.Gv v), ∀ X ∈ (Box.bar L.O' B).bp j v, (hEv.ad j (F.loc v s)) X ∈ (Box.bar L.O' B).bp j v := by
    intro j v s X hX
    simp only [Box.bp, Submodule.mem_comap, Submodule.subtype_apply] at hX ⊢
    rw [Box.Ev.ad_apply]
    exact pr_bstab _ _ v s _ hX
  have EC := fun j => hok.ec (ResidueField L.O') (adp (ResidueField L.O') j) (hEv.ad j) ((Box.bar L.O' B).bp j) (hopenj j) (hstab j) (hprp.2 j _ hdual)
  have hder := ep_der L.O' h2 L.R σ P
  have hdimb := ep_dimb h2K (Box.bar L.O' B) π hEv
  have hcw := fun w => ep_cw h2K (Box.bar L.O' B) π hEv (F.cw w) (hok.cw_sq w) (hok.del_cw w)
  refine ep_pad S x L σ hσ P ?_ ?_ hee
  · haveI := (EC 0).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 0 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 0)
    have hs1 : 4 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 0 v) :=
      sum_ge F 4 _ (fun v => (hdimb v).1)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 0 (F.cw w)) - 1).ker ≤ 1 * Fintype.card F.Inf :=
      sum_le 1 _ (fun w => (hcw w).1)
    rw [hok.card_inf] at hs2
    have e := (EC 0).2
    have t := htan.2
    have d0 := hder.2.1
    omega
  · haveI := (EC 1).1
    have hm := ep_mazur L.O' h2 L.R σ hσ.sq P 1 _ (ep_hasobs hok L.O' h2 L.R σ hσ.sq L.ρ B π hU hBo hBc hgood.1 hG hEv 1)
    have hs1 : 2 * F.d ≤ ∑ v, F.dv v * Module.finrank (ResidueField L.O') ((Box.bar L.O' B).bp 1 v) :=
      sum_ge F 2 _ (fun v => (hdimb v).2)
    have hs2 : ∑ w, Module.finrank (ResidueField L.O') ((hEv.ad 1 (F.cw w)) - 1).ker ≤ 2 * Fintype.card F.Inf :=
      sum_le 2 _ (fun w => (hcw w).2)
    rw [hok.card_inf] at hs2
    have e := (EC 1).2
    have t := htan.1 1
    have d1 := hder.2.2
    omega
end

