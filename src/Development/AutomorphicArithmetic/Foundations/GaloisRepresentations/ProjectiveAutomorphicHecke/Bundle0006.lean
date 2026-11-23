module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Formalism.LocalToGlobal.Columns.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PNbhdU
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap.PNbhdU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private noncomputable def th {w : Plc E} (hw : IsSplitAt w) : GLw n w →* GLw n (cj w) :=
  (cLoc (cj w)).comp ((finU (E := E) (n := n)).subtype.comp (locF hw))

private theorem continuous_th {w : Plc E} (hw : IsSplitAt w) : Continuous (th (n := n) hw) :=
  (GlobalTheory.BCT.GlobLev.continuous_cLoc (cj w)).comp
    ((continuous_subtype_val (p := (· ∈ locU n w))).comp (locE hw).symm.continuous)

private theorem cLoc_cj_eq {w : Plc E} (hw : IsSplitAt w) (u : finU (E := E) (n := n)) :
    cLoc (cj w) u.1 = th hw (cLoc w u.1) :=
  GlobalTheory.LocInj.cLoc_conj_eq w u.1 (locF hw (cLoc w u.1)).1 (cLoc_locF hw _).symm

private theorem cj_cj (w : Plc E) : cj (cj w) = w := GlobalTheory.SplitPts.conjSrc_conjSrc_cm w

private theorem exists_lt (α : Type) : ∃ lt : α → α → Prop, (∀ a b, a ≠ b → lt a b ∨ lt b a) ∧ ∀ a b, lt a b → ¬ lt b a := by
  refine ⟨WellOrderingRel, ?_, fun _ _ h => asymm h⟩
  intro a b h
  rcases trichotomous_of (WellOrderingRel : α → α → Prop) a b with hab | heq | hba
  · exact Or.inl hab
  · exact (h heq).elim
  · exact Or.inr hba

private def Top (lt : Plc E → Plc E → Prop) (Up : Plc E → Prop) (w₀ w : Plc E) : Prop :=
  Up w ∧ (Up (cj w) → w = w₀ ∨ (cj w ≠ w₀ ∧ lt w (cj w)))

private theorem top_or {lt : Plc E → Plc E → Prop} (h1 : ∀ a b, a ≠ b → lt a b ∨ lt b a) {Up : Plc E → Prop} (w₀ : Plc E)
    {w : Plc E} (hne : cj w ≠ w) (hup : Up w ∨ Up (cj w)) : Top lt Up w₀ w ∨ Top lt Up w₀ (cj w) := by
  by_cases ha : Up w
  · by_cases hb : Up (cj w)
    · by_cases e : w = w₀
      · exact Or.inl ⟨ha, fun _ => Or.inl e⟩
      · by_cases e' : cj w = w₀
        · exact Or.inr ⟨hb, fun _ => Or.inl e'⟩
        · rcases h1 w (cj w) hne.symm with h | h
          · exact Or.inl ⟨ha, fun _ => Or.inr ⟨e', h⟩⟩
          · exact Or.inr ⟨hb, fun _ => Or.inr ⟨by rwa [cj_cj], by rwa [cj_cj]⟩⟩
    · exact Or.inl ⟨ha, fun h => absurd h hb⟩
  · have hb := hup.resolve_left ha
    exact Or.inr ⟨hb, fun h => absurd (by rwa [cj_cj] at h) ha⟩

private theorem not_both {lt : Plc E → Plc E → Prop} (h2 : ∀ a b, lt a b → ¬ lt b a) {Up : Plc E → Prop} {w₀ w : Plc E}
    (hne : cj w ≠ w) (ha : Top lt Up w₀ w) (hb : Top lt Up w₀ (cj w)) : False := by
  have hb2 := hb.2 (by rw [cj_cj]; exact ha.1)
  rw [cj_cj] at hb2
  rcases ha.2 hb.1 with e | ⟨e, h⟩
  · rcases hb2 with e' | ⟨e', _⟩
    · exact hne (e'.trans e.symm)
    · exact e' e
  · rcases hb2 with e' | ⟨_, h'⟩
    · exact e e'
    · exact h2 _ _ h h'

end UpperTheory.Gal.CertificateRingHomMap.PNbhdU

open UpperTheory.Gal.CertificateRingHomMap.PNbhdU in
theorem UpperTheory.Gal.CertificateRingHomMap.pNbhdU_of :
    UpperTheory.Gal.CertificateRingHomMap.Nbhd2 → UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.NbhdU := by
  intro h2 hI hL _ E _ _ _ n O hO Up hUp w₀ hw₀ hu₀
  obtain ⟨S₀, K₀, hK₀, hS₀⟩ := h2 E n O hO
  obtain ⟨lt, hlt1, hlt2⟩ := exists_lt (Plc E)
  have hne : ∀ w : Plc E, IsSplitAt w → cj w ≠ w := fun w hw => (hL E n w hw).2.2.1
  have hsp : ∀ w : Plc E, IsSplitAt w → IsSplitAt (cj w) := fun w hw => (hL E n w hw).2.2.2.1
  let T : Finset (Plc E) := insert w₀ (S₀ ∪ S₀.image (fun w => cj w))
  let S : Finset (Plc E) := T.filter (fun w => IsSplitAt w → Top lt Up w₀ w)
  let Kw : ∀ w : Plc E, Subgroup (GLw n w) := fun w =>
    if hw : IsSplitAt w then K₀ w ⊓ (K₀ (cj w)).comap (th hw) else K₀ w
  have hKle : ∀ w, Kw w ≤ K₀ w := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw]; exact inf_le_left
    · simp only [Kw, dif_neg hw]; exact le_rfl
  have hKopen : ∀ w, IsOpen (Kw w : Set (GLw n w)) := by
    intro w
    by_cases hw : IsSplitAt w
    · simp only [Kw, dif_pos hw, Subgroup.coe_inf, Subgroup.coe_comap]
      exact (hK₀ w).1.inter ((hK₀ (cj w)).1.preimage (continuous_th hw))
    · simp only [Kw, dif_neg hw]; exact (hK₀ w).1
  have hKKGL : ∀ w, Kw w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => (hKle w).trans (hK₀ w).2
  have hmemS : ∀ w, w ∈ T → (IsSplitAt w → Top lt Up w₀ w) → w ∈ S := fun w h h' => Finset.mem_filter.2 ⟨h, h'⟩
  refine ⟨S, Kw, ⟨?_, fun w _ => hKopen w, fun w _ => ?_, fun w _ _ => hKKGL w, fun w hw hs => ?_⟩, ?_⟩
  · exact hmemS _ (Finset.mem_insert_self _ _) fun _ => ⟨hu₀, fun _ => Or.inl rfl⟩
  · exact (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2.of_isClosed_subset
      (Subgroup.isClosed_of_isOpen (Kw w) (hKopen w)) (hKKGL w)
  · have hw' := (Finset.mem_filter.1 hw).2 hs
    exact ⟨hw'.1, fun hc => not_both hlt2 (hne w hs) hw' ((Finset.mem_filter.1 hc).2 (hsp w hs))⟩
  · intro u hu
    obtain ⟨hz, hS, hout⟩ := mem_lev.1 hu
    have hint : ∀ w, cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
      intro w
      by_cases h1 : w ∈ S
      · exact hKKGL w (hS w h1)
      · by_cases h2 : cj w ∈ S
        · have h3 := hI E n (ofU u) (cj w) hz (hKKGL _ (hS _ h2))
          have key : ∀ v : Plc E, v = w → comp v (ofU u) ∈ GlobalTheory.LFun.KGL v (n := n) → cLoc w u.1 ∈ GlobalTheory.LFun.KGL w (n := n) := by
            rintro v rfl h; exact h
          exact key _ (cj_cj w) h3
        · exact hout w h1 h2
    refine hS₀ u hint fun w hw => ?_
    have hT : w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_left _ hw)
    by_cases hs : IsSplitAt w
    · by_cases ht : Top lt Up w₀ w
      · exact hKle w (hS w (hmemS w hT fun _ => ht))
      · have ht' := (top_or hlt1 w₀ (hne w hs) (hUp w hs)).resolve_left ht
        have hT' : cj w ∈ T := Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw))
        have h3 := hS (cj w) (hmemS _ hT' fun _ => ht')
        simp only [Kw, dif_pos (hsp w hs)] at h3
        have h4 : th (hsp w hs) (cLoc (cj w) u.1) ∈ K₀ (cj (cj w)) := (Subgroup.mem_inf.1 h3).2
        rw [← cLoc_cj_eq (hsp w hs) u] at h4
        have key : ∀ v : Plc E, v = w → cLoc v u.1 ∈ K₀ v → cLoc w u.1 ∈ K₀ w := by
          rintro v rfl h; exact h
        exact key _ (cj_cj w) h4
    · exact hKle w (hS w (hmemS w hT fun h => absurd h hs))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PRootsAlg
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem cpow_key (q n j : ℕ) (hq : 0 < q) :
    (q : ℂ) ^ (j.choose 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) =
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ^ j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hρ : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (((n : ℂ) - 1) / 2) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q)]
    push_cast
    rfl
  rw [hρ, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast (q : ℂ) (j.choose 2), ← Complex.cpow_add _ _ hq0,
    Nat.cast_choose_two]
  congr 1
  ring

theorem UpperTheory.Gal.CertificateRingHomMap.pRootsAlg_of :
    UpperTheory.Gal.CertificateRingHomMap.RootsAlg := by
  intro q n hq B hB a c ϑ h
  refine ⟨?_, ?_⟩
  · have h0 := h 0 (Nat.zero_le n)
    simpa [GlobalTheory.LFun.satEig, Multiset.esymm] using h0
  · set ρ : ℂ := (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) with hρ
    set s : Multiset ℂ := B.map (fun b : ℂˣ => (b : ℂ)) with hs
    have hcard : Multiset.card s = n := by simp [hs, hB]
    have e1 : (UpperTheory.V.Af.algSat n q B).map (· * c) = s.map (fun x => (ρ * c) • x) := by
      have e0 : UpperTheory.V.Af.algSat n q B = s.map (fun α => ρ * α) := by
        show Multiset.map _ (B.bind fun b => ({(b : ℂ)} : Multiset ℂ)) = _
        rw [Multiset.bind_singleton]
      rw [e0, Multiset.map_map]
      refine Multiset.map_congr rfl fun x _ => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      ring
    have e2 : Multiset.card (s.map (fun x => (ρ * c) • x)) = n := by simp [hcard]
    rw [e1, UpperTheory.Gal.crystallineComparison.rootPol, Multiset.prod_X_sub_X_eq_sum_esymm, e2, Finset.mul_sum, UpperTheory.Gal.crystallineComparison.heckePol]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hk : _ = ρ ^ j := cpow_key q n j hq
    rw [h j hjn, ← Multiset.pow_smul_esymm, smul_eq_mul]
    have e3 : (-1 : ℂ) ^ j * (q : ℂ) ^ (j.choose 2) * (a * GlobalTheory.LFun.satEig q n B j * c ^ j) =
        a * ((-1) ^ j * ((ρ * c) ^ j * s.esymm j)) := by
      have e4 : GlobalTheory.LFun.satEig q n B j = (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - (j : ℂ))) / 2) * s.esymm j := rfl
      rw [e4, mul_pow]
      linear_combination ((-1) ^ j * a * s.esymm j * c ^ j) * hk
    rw [e3]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSphType
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pSphType_of :
    UpperTheory.Gal.CertificateRingHomMap.IntConj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.SphType := by
  intro hIC hLC E _ _ _ n π w hw
  refine ⟨?_, ?_⟩
  · rintro ⟨B, σ, ⟨-, f, hf0, hfV, hf⟩, hB⟩
    have hker : LinearMap.ker f = ⊥ := by
      refine (((GlobalTheory.CuspRep.isIrreducible_iff σ.ρ).1 σ.irred).2 (LinearMap.ker f) (fun g v hv => ?_)).resolve_right
        fun h => hf0 (LinearMap.ker_eq_top.1 h)
      rw [LinearMap.mem_ker] at hv ⊢
      have h1 := hf ⟨(locF hw g).1, locF_mem hw g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, cLoc_locF] at h1
      rw [h1, hv, map_zero]
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hB.1
    have hfix := GlobalTheory.LGrp.mem_fixed.1 hv
    have hφ0 : f v ≠ 0 := fun h => hv0 (LinearMap.ker_eq_bot.1 hker (h.trans (map_zero f).symm))
    have key : ∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x (f v) = f v := by
      intro x hx hk
      have h1 := hf ⟨x, hx⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
      rw [← h1, hfix _ hk]
    obtain ⟨-, -, -, -, hcc, hloc⟩ := hLC E n w hw
    refine ⟨⟨f v, hfV v, hφ0, fun x hx h => ?_⟩, ⟨f v, hfV v, hφ0, fun x hx h => ?_⟩⟩
    · simpa using key x hx h
    · rw [hloc] at hx
      have h2 := hIC E n (ofU ⟨x, (Subgroup.mem_inf.1 hx).1⟩) (cj w) (by rw [sim_ofU]; exact one_mem _)
        (by rw [comp_ofU]; exact h)
      rw [hcc, comp_ofU] at h2
      simpa using key x hx h2
  · rintro J χ ⟨φ, hφ, h0, hact⟩
    have hlev := (π.isAut.aut φ hφ).level
    have hc : Continuous fun k : J => (locF hw k.1 : finU (E := E) (n := n)) := by
      have h1 : Continuous fun k : GLw n w => (locF hw k : finU (E := E) (n := n)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp (locE hw).symm.continuous) _
      exact h1.comp continuous_subtype_val
    have hset : {k : J | χ k = 1} = (fun k : J => (locF hw k.1 : finU (E := E) (n := n))) ⁻¹' {k : finU (E := E) (n := n) | RU E n k φ = φ} := by
      ext k
      have hk : cLoc w (locF hw k.1).1 ∈ J := by rw [cLoc_locF]; exact k.2
      have h1 := hact (locF hw k.1).1 (locF_mem hw k.1) hk
      have h2 : (⟨cLoc w (locF hw k.1).1, hk⟩ : J) = k := Subtype.ext (cLoc_locF hw k.1)
      rw [h2] at h1
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      rw [h1]
      constructor
      · intro h; rw [h]; simp
      · intro h
        have h3 : ((χ k : ℂˣ) : ℂ) = 1 := smul_left_injective ℂ h0 (by simpa using h)
        exact Units.ext h3
    rw [hset]
    exact hlev.preimage hc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PStepAt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

noncomputable section

namespace UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem comm_of_cLoc {w : Plc E} (hw : IsSplitAt w) (z : UA E n) (hz : cLoc w z = 1)
    (y : UA E n) (hy : y ∈ locU n w) : y * z = z * y := by
  have hyf := (Subgroup.mem_inf.1 hy).1
  have hyo := (Subgroup.mem_inf.1 hy).2
  have hc : z * y * z⁻¹ * y⁻¹ ∈ locU n w := by
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
    · have h1 : cInf y = 1 := MonoidHom.mem_ker.1 hyf
      exact MonoidHom.mem_ker.2 (by simp [h1])
    · have h1 : cLoc u y = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hyo u) hu)
      exact MonoidHom.mem_ker.2 (by simp [h1])
  have h1 := GlobalTheory.SplitPts.eq_one_of_cLoc hw ⟨_, hc⟩ (by simp [hz])
  have h2 : z * y * z⁻¹ * y⁻¹ = 1 := congrArg Subtype.val h1
  exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h2)).symm

private def CJ {w : Plc E} (J : Subgroup (GLw n w)) : Subgroup (UA E n) := locU n w ⊓ J.comap (cLoc w)

private theorem isCompact_CJ {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) : IsCompact (CJ J : Set (UA E n)) := by
  have hc : Continuous fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n) :=
    continuous_subtype_val.comp (locE hw).symm.continuous
  have he : (CJ J : Set (UA E n)) = (fun x : GLw n w => (((locE hw).symm x : locU n w) : UA E n)) '' (J : Set (GLw n w)) := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨cLoc w g, h2, ?_⟩
      have : (locE hw).symm (cLoc w g) = ⟨g, h1⟩ := by
        apply (locE hw).injective
        rw [ContinuousMulEquiv.apply_symm_apply, locE_apply]
      simp [this]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨((locE hw).symm x).2, ?_⟩
      show cLoc w (locF hw x).1 ∈ J
      rw [cLoc_locF]
      exact hx
  rw [he]
  exact hJ.image hc

private theorem finite_index {w : Plc E} (hw : IsSplitAt w) (J : Subgroup (GLw n w))
    (hJ : IsCompact (J : Set (GLw n w))) (φ : UA E n → ℂ) (hφ : IsAutFormU φ) :
    ∃ N : Subgroup (CJ J : Subgroup (UA E n)), N.FiniteIndex ∧ ∀ k ∈ N, RU E n (k : UA E n) φ = φ := by
  haveI : CompactSpace (CJ J : Subgroup (UA E n)) := isCompact_iff_compactSpace.1 (isCompact_CJ hw J hJ)
  let N : Subgroup (CJ J : Subgroup (UA E n)) :=
    { carrier := {k | RU E n (k : UA E n) φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show RU E n ((a * b : CJ J) : UA E n) φ = φ
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        show RU E n ((a⁻¹ : CJ J) : UA E n) φ = φ
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul]
        simp }
  have hle : (CJ J : Subgroup (UA E n)) ≤ finU (E := E) (n := n) := fun k hk => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).1
  have hop : IsOpen (N : Set (CJ J : Subgroup (UA E n))) :=
    hφ.level.preimage (f := fun k : (CJ J : Subgroup (UA E n)) => (⟨k.1, hle k.2⟩ : finU (E := E) (n := n)))
      (Continuous.subtype_mk continuous_subtype_val _)
  haveI := Subgroup.quotient_finite_of_isOpen N hop
  exact ⟨N, Subgroup.finiteIndex_of_finite_quotient, fun k hk => hk⟩

private theorem step_core (π : AutSub E n) (W : Wt E n) (f : algForms W) {w : Plc E} (hw : IsSplitAt w)
    (hf : f ∈ π.finPart W) (r : UA E n →₀ ℂ) (hr : ∀ g ∈ r.support, g ∈ locU n w) :
    ∃ f' ∈ π.finPart W, (∀ v, f'.1 v = r.sum fun g a => a • RU E n g (f.1 v)) ∧
      ∀ u : finU (E := E) (n := n), cLoc w u.1 = 1 → algRep W u f = f → algRep W u f' = f' := by
  have hle : locU n w ≤ finU (E := E) (n := n) := inf_le_left
  let F : r.support → algForms W := fun g => r g.1 • algRep W ⟨g.1, hle (hr _ g.2)⟩ f
  have hval : ∀ v, (∑ g : r.support, F g).1 v = r.sum fun g a => a • RU E n g (f.1 v) := by
    intro v
    rw [Finsupp.sum, ← Finset.sum_coe_sort r.support, Submodule.coe_sum, LinearMap.sum_apply]
    rfl
  refine ⟨∑ g : r.support, F g, AutSub.mem_finPart.2 fun v => ?_, hval, fun u hu hfix => ?_⟩
  · rw [hval]
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (π.isAut.stable _ _ (AutSub.mem_finPart.1 hf v))
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hcm : u * (⟨g.1, hle (hr _ g.2)⟩ : finU (E := E) (n := n)) = ⟨g.1, hle (hr _ g.2)⟩ * u :=
        Subtype.ext (comm_of_cLoc hw u.1 hu g.1 (hr _ g.2)).symm
      simp only [F]
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hcm, map_mul, Module.End.mul_apply, hfix]

private theorem mem_lev_off (hC : LocComm) {S : Finset (Plc E)} {Kw : ∀ w : Plc E, Subgroup (GLw n w)} {w : Plc E}
    (hw : IsSplitAt w) (hwS : w ∈ S) (hcj : cj w ∉ S) {J : Subgroup (GLw n w)} (u : finU (E := E) (n := n))
    (hu : ofU u ∈ lev S (Function.update Kw w J)) (x : GLw n w) (u' : finU (E := E) (n := n)) (hx : u = locF hw x * u')
    (h1 : cLoc w u'.1 = 1) : ofU u' ∈ lev S Kw := by
  obtain ⟨-, hap, -, -, hcc, -⟩ := hC E n w hw
  obtain ⟨-, hu2, hu3⟩ := mem_lev.1 hu
  have hsame : ∀ t : Plc E, GlobalTheory.Cong.Apart t w → comp t (ofU u') = comp t (ofU u) := by
    intro t ht
    have h2 : comp t (loc hw x) = 1 := comp_loc_of_apart hw ht x
    rw [hx, map_mul, map_mul]
    have h3 : comp t (ofU (locF hw x)) = 1 := h2
    rw [h3, one_mul]
  refine mem_lev.2 ⟨by rw [sim_ofU]; exact one_mem _, fun t ht => ?_, fun t ht hct => ?_⟩
  · by_cases htw : t = w
    · subst htw
      rw [comp_ofU, h1]
      exact one_mem _
    · have hne : t ≠ cj w := fun h => hcj (h ▸ ht)
      rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
      have := hu2 t ht
      rwa [Function.update_of_ne htw] at this
  · have htw : t ≠ w := fun h => ht (h ▸ hwS)
    have hne : t ≠ cj w := fun h => hct (by rw [h, hcc]; exact hwS)
    rw [hsame t ((hap t).2 ⟨htw, hne⟩)]
    exact hu3 t ht hct

end UpperTheory.Gal.CertificateRingHomMap.LevelShrinking

open UpperTheory.Gal.CertificateRingHomMap.LevelShrinking in
theorem UpperTheory.Gal.CertificateRingHomMap.pStepAt_of :
    UpperTheory.Gal.CertificateRingHomMap.LocAdj → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.OfUBij → UpperTheory.Gal.CertificateRingHomMap.StepAt := by
  intro hA hC _ E _ _ _ n π W f hf hf0 S Kw w hw hwS hcj hfix J χ hJc hT
  obtain ⟨φ, hφπ, hφ0, hφ⟩ := hT
  let χ' : (CJ J : Subgroup (UA E n)) →* ℂˣ :=
    χ.comp (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J fun k => (Subgroup.mem_inf.1 k.2).2)
  have hf1 : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
  obtain ⟨r, hrH, ⟨v₀, hv₀⟩, hrχ⟩ := hA (UA E n) (UA E n → ℂ) W.Sp (RU E n) π.V π.isAut.stable π.isAut.irred
    (locU n w) (CJ J) inf_le_left
    (fun g => ⟨(locF hw (cLoc w g)).1, locF_mem hw _, (locF hw (cLoc w g)).1⁻¹ * g,
      fun y hy => (comm_of_cLoc hw _ (by simp) y hy).symm, by simp⟩)
    (fun ψ hψ => finite_index hw J hJc ψ (π.isAut.aut ψ hψ)) χ'
    ⟨φ, hφπ, hφ0, fun k => hφ k.1 (Subgroup.mem_inf.1 k.2).1 (Subgroup.mem_inf.1 k.2).2⟩
    f.1 hf1 (AutSub.mem_finPart.1 hf)
  obtain ⟨f', hf', hval, hoff⟩ := step_core π W f hw hf r hrH
  refine ⟨f', hf', fun h => hv₀ ?_, fun u hu h => ?_⟩
  · rw [← hval, h]
    rfl
  · set x := cLoc w u.1 with hxdef
    set a := locF hw x with hadef
    have hax : cLoc w a.1 = x := cLoc_locF hw x
    have h1 : cLoc w ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = 1 := by
      have : ((a⁻¹ * u : finU (E := E) (n := n)) : UA E n) = a.1⁻¹ * u.1 := rfl
      rw [this, map_mul, map_inv, hax, ← hxdef, inv_mul_cancel]
    have hu' : u = a * (a⁻¹ * u) := by group
    have hfix' : algRep W (a⁻¹ * u) f = f :=
      hfix _ (mem_lev_off hC hw hwS hcj u hu x _ hu' h1)
    have hstep := hoff _ h1 hfix'
    have hak : a.1 ∈ (CJ J : Subgroup (UA E n)) :=
      Subgroup.mem_inf.2 ⟨locF_mem hw x, by show cLoc w a.1 ∈ J; rw [hax]; exact h⟩
    have hχ : ((χ' ⟨a.1, hak⟩ : ℂˣ) : ℂ) = ((χ ⟨x, h⟩ : ℂˣ) : ℂ) := by
      have : (((cLoc w).comp (CJ J : Subgroup (UA E n)).subtype).codRestrict J
          fun k => (Subgroup.mem_inf.1 k.2).2) ⟨a.1, hak⟩ = ⟨x, h⟩ := Subtype.ext hax
      simp only [χ', MonoidHom.comp_apply, this]
    have e : algRep W u f' = algRep W a f' := by
      conv_lhs => rw [hu', map_mul, Module.End.mul_apply, hstep]
    rw [e]
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have h2 := hrχ ⟨a.1, hak⟩ v
    rw [← hval, hχ] at h2
    exact h2

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiScalar
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

theorem UpperTheory.Gal.CertificateRingHomMap.pXiScalar_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar := by
  intro E _ _ _ n W j y s t hy v
  have hy' : y = Formalism.L2.Col.brpSc E t := Units.ext (by rw [hy, Formalism.L2.Col.brpSc_coe])
  have hinv : y⁻¹ = Formalism.L2.Col.brpSc E t⁻¹ := by
    rw [hy']
    exact (map_inv (Units.map (algebraMap E (Matrix (Fin n) (Fin n) E) : E →* Matrix (Fin n) (Fin n) E)) t).symm
  have hemb : embAll E n y⁻¹ = fun u => Formalism.L2.Col.brpSc ℂ (Units.map (u.embedding : E →* ℂ) t⁻¹) := by
    funext u
    ext i k
    rw [hinv]
    change ((((Formalism.L2.Col.brpSc E t⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E).map u.embedding) i k = _
    rw [Formalism.L2.Col.brpSc_coe, Formalism.L2.Col.brpSc_coe]
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hr := Formalism.L2.Col.tensorWeights_scalar_action (K := ℂ) W (fun u => Units.map (u.embedding : E →* ℂ) t⁻¹)
  rw [← hemb] at hr
  simp only [xi, MonoidHom.coe_mk, OneHom.coe_mk, Representation.dual_apply]
  rw [MonoidHom.comp_apply, hr]
  ext x
  simp [Module.Dual.transpose_apply, smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PXiZeta
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

private theorem zpow_sum_eq_prod_zpow {ι : Type*} {a : ℂ} (ha : a ≠ 0) (s : Finset ι) (e : ι → ℤ) :
    a ^ (∑ u ∈ s, e u) = ∏ u ∈ s, a ^ e u := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add₀ ha, ih]

theorem UpperTheory.Gal.CertificateRingHomMap.pXiZeta_of :
    UpperTheory.Gal.CertificateRingHomMap.XiScalar → UpperTheory.Gal.CertificateRingHomMap.XiZeta := by
  intro hXi E _ _ _ n W j x ζ hζ k
  obtain ⟨γ, t, h1, h2, h3, h4⟩ := hζ.onRat k
  refine ⟨γ, h1, fun v => ?_⟩
  have hs : xi0 W j γ v = _ := hXi E n W j γ.1.1 γ.1.2 t h2 v
  rw [hs]
  congr 1
  rw [h4]
  have e : ∀ u : InfinitePlace E, u.embedding (t : E) ^ (-∑ i, (W u).w i) =
      ∏ φ : E →+* ℂ, (if φ x = -u.embedding x then φ (k : E) else 1) ^ (-∑ i, (W u).w i) := by
    intro u
    rw [h3 u.embedding, Finset.prod_filter, Finset.prod_zpow]
  rw [Finset.prod_congr rfl fun u _ => e u, Finset.prod_comm, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun φ _ => ?_
  have ha : φ (k : E) ≠ 0 := (map_ne_zero φ).2 k.ne_zero
  unfold mOf
  rw [zpow_sub₀ ha, div_eq_mul_inv, zpow_sum_eq_prod_zpow ha, ← Finset.prod_inv_distrib]
  congr 1
  refine Finset.prod_congr rfl fun u _ => ?_
  by_cases h : φ x = -u.embedding x
  · have h' : u.embedding x = -φ x := by rw [h, neg_neg]
    rw [if_pos h, if_pos h', _root_.zpow_neg]
  · have h' : ¬ u.embedding x = -φ x := fun h'' => h (by rw [h'', neg_neg])
    rw [if_neg h, if_neg h']
    simp
end

